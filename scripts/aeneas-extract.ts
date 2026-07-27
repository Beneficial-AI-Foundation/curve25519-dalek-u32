/**
 * Run the full extraction pipeline: Charon -> Aeneas -> Tweaks.
 *
 * Charon reads start_from / exclude / opaque natively from
 * [package.metadata.charon] in curve25519-dalek/Cargo.toml (Charon PR #1104).
 * This script only passes preset and cargo_args as CLI flags.
 *
 * Aeneas writes the generated Lean files to `<dest>/<subdir>/` and an
 * auto-generated root import file `<dest>/<subdir>.lean`. The `subdir` value
 * doubles as the Lean import-path prefix (e.g. `import translated.Funs`).
 * `-emit-json` additionally writes `translation.json` alongside the Lean files.
 */

import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { loadConfig } from "./lib/config.js";
import { findBinary } from "./lib/paths.js";
import { runStreaming } from "./lib/shell.js";
import { applyTweaks, warnUnmatchedTweaks } from "./lib/tweaks.js";
import { syncLeanToolchain } from "./lib/lean-toolchain.js";

/**
 * True if `binPath` is an ELF whose program interpreter lives in the Nix store
 * (i.e. a Nix-built binary). `make setup-charon` builds Charon via `nix build`,
 * producing binaries linked against the Nix glibc loader.
 */
function usesNixLoader(binPath: string): boolean {
  try {
    const fd = fs.openSync(binPath, "r");
    const buf = Buffer.alloc(4096);
    fs.readSync(fd, buf, 0, buf.length, 0);
    fs.closeSync(fd);
    return /\/nix\/store\/[^\0]*ld-linux/.test(buf.toString("latin1"));
  } catch {
    return false;
  }
}

/**
 * Locate a Nix-provided `libz.so.1` lib dir. A Nix-built charon-driver uses the
 * Nix glibc loader, whose search path is the Nix store, so it can't see the
 * system libz.so.1 that `librustc_driver` needs — we must put a matching Nix zlib
 * on LD_LIBRARY_PATH. Returns null if none is found.
 */
function findNixZlibLibDir(): string | null {
  const store = "/nix/store";
  let entries: string[];
  try {
    entries = fs.readdirSync(store);
  } catch {
    return null;
  }
  for (const name of entries) {
    if (!name.includes("-zlib-")) continue;
    const libDir = path.join(store, name, "lib");
    if (fs.existsSync(path.join(libDir, "libz.so.1"))) return libDir;
  }
  return null;
}

async function main(): Promise<void> {
  console.log(chalk.bold("\nAeneas Extract\n"));

  const { config, root } = loadConfig();

  // Resolve binaries
  const charonBin = findBinary("charon", root);
  const aeneasBin = findBinary("aeneas", root);

  if (!charonBin) {
    throw new Error("Charon binary not found. Run 'npm run aeneas-install' first.");
  }
  if (!aeneasBin) {
    throw new Error("Aeneas binary not found. Run 'npm run aeneas-install' first.");
  }

  // Charon reads [package.metadata.charon] from ./Cargo.toml in its cwd,
  // but always outputs the LLBC to the workspace root regardless of cwd.
  const crateDir = path.join(root, config.crate.dir);
  const llbcFile = `${config.crate.name}.llbc`;
  const llbcPath = path.join(root, llbcFile); // charon outputs to workspace root
  const destDir = path.join(root, config.aeneas_args.dest);
  const outputDir = config.aeneas_args.subdir
    ? path.join(destDir, config.aeneas_args.subdir)
    : destDir;
  const logsDir = path.join(root, ".logs");

  // ── Step 1: Charon ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 1: Generating LLBC with Charon..."));

  const charonArgs: string[] = ["cargo"];

  if (config.charon.preset) charonArgs.push(`--preset=${config.charon.preset}`);

  // Running from the crate directory, so --package is not needed.
  // Cargo args (feature flags etc.) go after --
  if (config.charon.cargo_args.length > 0) {
    charonArgs.push("--", ...config.charon.cargo_args);
  }

  // Remove stale LLBC
  if (fs.existsSync(llbcPath)) {
    fs.unlinkSync(llbcPath);
  }

  fs.mkdirSync(logsDir, { recursive: true });

  // Force cfg overrides (e.g. the serial u64 backend) for the charon build only,
  // so the crate's normal multi-backend builds are unaffected. CARGO_ENCODED_RUSTFLAGS
  // treats each entry as one flag token (separated by 0x1f), avoiding whitespace splitting.
  const charonEnvParts: Record<string, string> = {};
  if (config.charon.rustflags.length > 0) {
    charonEnvParts.CARGO_ENCODED_RUSTFLAGS = config.charon.rustflags.join("\x1f");
  }
  // A Nix-built charon-driver (make setup-charon runs `nix build`) uses the Nix
  // glibc loader, which searches the Nix store and can't find the system
  // libz.so.1 that librustc_driver needs. Put a matching Nix zlib on
  // LD_LIBRARY_PATH; Charon forwards this to charon-driver (appending the rustup
  // toolchain lib dir itself). No-op on non-Nix systems.
  if (usesNixLoader(charonBin)) {
    const nixZlibDir = findNixZlibLibDir();
    if (nixZlibDir) {
      charonEnvParts.LD_LIBRARY_PATH = [nixZlibDir, process.env.LD_LIBRARY_PATH]
        .filter(Boolean)
        .join(":");
    } else {
      console.log(chalk.yellow(
        "  Warning: charon is a Nix build but no Nix zlib was found; " +
        "charon-driver may fail to load libz.so.1.",
      ));
    }
  }
  const charonEnv = Object.keys(charonEnvParts).length > 0 ? charonEnvParts : undefined;

  await runStreaming(charonBin, charonArgs, {
    cwd: crateDir,  // read [package.metadata.charon] from crate's Cargo.toml
    env: charonEnv,
    logFile: path.join(logsDir, "charon.log"),
  });

  if (!fs.existsSync(llbcPath)) {
    throw new Error(`Failed to generate ${llbcFile}`);
  }
  console.log(chalk.green(`  LLBC generated: ${llbcFile}\n`));

  // ── Step 2: Aeneas ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 2: Generating Lean files with Aeneas..."));

  const aeneasArgs: string[] = [
    "-backend", "lean",  // we only ever target the Lean backend
    ...config.aeneas_args.options.map((o) => `-${o}`),
    "-dest", destDir,
  ];
  if (config.aeneas_args.subdir) {
    aeneasArgs.push("-subdir", config.aeneas_args.subdir);
  }
  aeneasArgs.push(llbcPath);  // absolute path since aeneas runs from root

  fs.mkdirSync(outputDir, { recursive: true });

  // Aeneas may exit non-zero while still producing output (known errors like
  // "join of nested borrows not supported" or internal errors on certain
  // constructs are non-fatal for our codebase).  We check for the output
  // files explicitly rather than relying solely on the exit code.
  try {
    await runStreaming(aeneasBin, aeneasArgs, {
      cwd: root,
      logFile: path.join(logsDir, "aeneas.log"),
    });
  } catch {
    // Check if output files were generated despite the error
    const missingFiles = config.tweaks.files.filter(
      (f) => !fs.existsSync(path.join(outputDir, f)),
    );
    if (missingFiles.length > 0) {
      throw new Error(
        `Aeneas failed and did not generate: ${missingFiles.join(", ")}. See .logs/aeneas.log`,
      );
    }
    console.log(chalk.yellow("  Aeneas exited with errors but output files were generated (see .logs/aeneas.log)\n"));
  }

  console.log(chalk.green(`  Lean files generated in ${path.relative(root, outputDir)}/\n`));

  // ── Step 3: Tweaks ──────────────────────────────────────────────────
  if (config.tweaks.substitutions.length > 0 && config.tweaks.files.length > 0) {
    console.log(chalk.bold("Step 3: Applying tweaks..."));

    const matchedPerFile: Set<number>[] = [];
    for (const file of config.tweaks.files) {
      const filePath = path.join(outputDir, file);
      if (!fs.existsSync(filePath)) {
        console.log(chalk.yellow(`  Warning: File not found, skipping: ${file}`));
        continue;
      }
      const matched = applyTweaks(filePath, config.tweaks.substitutions);
      matchedPerFile.push(matched);
      console.log(chalk.green(`  Tweaks applied to ${file} (${matched.size} substitutions matched)`));
    }
    warnUnmatchedTweaks(config.tweaks.substitutions, matchedPerFile);
    console.log();
  }

  // ── Step 4: Lean toolchain sync ─────────────────────────────────────
  syncLeanToolchain(root);

  console.log(chalk.green("Done."));
}

main().catch((err) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
