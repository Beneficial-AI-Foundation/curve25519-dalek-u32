/**
 * Clone and build aeneas + charon from source.
 *
 * Steps:
 * 1. Check dependencies (git, opam, make, rustup)
 * 2. Setup OCaml 5.2.0 switch + deps
 * 3. Clone/update aeneas repo at pinned commit
 * 4. Build charon (make setup-charon) — this clones Charon at its pinned commit
 *    and builds it; Charon's rust-toolchain.toml makes rustup auto-install the
 *    pinned nightly + components (rustc-dev, etc.).
 * 5. Build aeneas (make)
 *
 * Skips rebuild if the installed aeneas version matches the pinned commit.
 */

import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import ora from "ora";
import { loadConfig } from "./lib/config.js";
import { run, runStreaming } from "./lib/shell.js";
import { findBinary } from "./lib/paths.js";
import { syncLeanToolchain } from "./lib/lean-toolchain.js";

// ── Paths ─────────────────────────────────────────────────────────────

function getAeneasDir(root: string): string {
  return path.join(root, ".aeneas");
}

function getRepoDir(root: string): string {
  return path.join(getAeneasDir(root), "aeneas");
}

// ── Version check ─────────────────────────────────────────────────────

/**
 * Check if the currently installed aeneas matches the pinned commit.
 * Uses `aeneas -version` if available, falls back to git rev-parse.
 */
async function getInstalledVersion(root: string): Promise<string | null> {
  const aeneasBin = findBinary("aeneas", root);
  if (!aeneasBin) return null;

  // Try aeneas -version first (available in recent builds)
  try {
    const output = await run(aeneasBin, ["-version"], { silent: true });
    // Expected to contain a commit hash
    const match = output.match(/[0-9a-f]{8,40}/);
    if (match) return match[0];
  } catch {
    // -version not supported in this build, fall through
  }

  // Fallback: check git commit in the repo dir
  const repoDir = getRepoDir(root);
  if (!fs.existsSync(repoDir)) return null;
  try {
    const output = await run("git", ["rev-parse", "HEAD"], { cwd: repoDir, silent: true });
    return output.trim();
  } catch {
    return null;
  }
}

// ── Dependencies ──────────────────────────────────────────────────────

async function checkDependencies(): Promise<void> {
  const spinner = ora("Checking dependencies...").start();
  const deps = ["git", "opam", "gmake", "rustup"];
  const missing: string[] = [];

  for (const dep of deps) {
    try {
      await run("which", [dep], { silent: true });
    } catch {
      missing.push(dep);
    }
  }

  if (missing.length > 0) {
    spinner.fail();
    throw new Error(`Missing dependencies: ${missing.join(", ")}`);
  }
  spinner.succeed("Dependencies OK");
}

// ── OCaml setup ───────────────────────────────────────────────────────

async function getOpamEnv(switchName: string): Promise<Record<string, string>> {
  const output = await run("opam", ["env", `--switch=${switchName}`, "--set-switch"], {
    silent: true,
  });
  const env: Record<string, string> = {};
  for (const line of output.split("\n")) {
    const match = line.match(/^(\w+)='([^']*)'; export \1;/);
    if (match) {
      env[match[1]] = match[2];
    }
  }
  return env;
}

const OCAML_DEPS = [
  "ppx_deriving", "ppx_deriving_yojson", "visitors", "easy_logging", "zarith", "yojson",
  "core_unix", "odoc", "ocamlgraph", "menhir", "ocamlformat",
  "unionFind", "domainslib", "progress",
];

async function setupOcaml(root: string): Promise<Record<string, string>> {
  const switchName = "5.2.0";
  const logsDir = path.join(root, ".logs");
  fs.mkdirSync(logsDir, { recursive: true });

  const switches = await run("opam", ["switch", "list", "--short"], { silent: true });
  const exists = switches.split("\n").some((s) => s.trim() === switchName);

  if (!exists) {
    console.log("  Creating OCaml 5.2.0 switch...");
    await runStreaming("opam", ["switch", "create", switchName], {
      logFile: path.join(logsDir, "opam-switch-create.log"),
    });
  }

  const env = await getOpamEnv(switchName);

  console.log("  Updating opam...");
  await runStreaming("opam", ["update"], {
    env,
    logFile: path.join(logsDir, "opam-update.log"),
  });

  console.log("  Installing OCaml dependencies...");
  await runStreaming("opam", ["install", "-y", ...OCAML_DEPS], {
    env,
    logFile: path.join(logsDir, "opam-install.log"),
  });

  return env;
}

// ── Git operations ────────────────────────────────────────────────────

async function setupRepo(repo: string, repoDir: string, commit: string): Promise<void> {
  // Only treat the dir as updatable if it's an actual git checkout. An existing
  // path that is NOT a git repo (e.g. an uninitialized submodule gitlink, which
  // leaves an empty dir) would otherwise make `git fetch`/`git reset` resolve to
  // the PARENT repo and fail on the aeneas commit — so clone fresh in that case.
  const isGitRepo = fs.existsSync(path.join(repoDir, ".git"));
  if (isGitRepo) {
    const spinner = ora("Updating repository...").start();
    await run("git", ["fetch", "origin"], { cwd: repoDir, silent: true });
    // Reset any local modifications before switching commits
    await run("git", ["reset", "--hard", commit], { cwd: repoDir, silent: true });
    spinner.succeed(`Aeneas at ${commit}`);
  } else {
    const spinner = ora(`Cloning ${repo}...`).start();
    // Remove any stale non-repo dir so `git clone` has a clean target.
    if (fs.existsSync(repoDir)) fs.rmSync(repoDir, { recursive: true, force: true });
    await run("git", ["clone", repo, repoDir], { silent: true });
    await run("git", ["checkout", commit], { cwd: repoDir, silent: true });
    spinner.succeed(`Cloned and checked out ${commit}`);
  }
}

// ── Build ─────────────────────────────────────────────────────────────

async function buildCharon(repoDir: string, env: Record<string, string>): Promise<void> {
  const spinner = ora("Building Charon...").start();
  await runStreaming("gmake", ["setup-charon"], { cwd: repoDir, env });
  spinner.succeed("Charon built");
}

async function buildAeneas(repoDir: string, env: Record<string, string>): Promise<void> {
  const spinner = ora("Building Aeneas...").start();
  await runStreaming("gmake", [], { cwd: repoDir, env });
  spinner.succeed("Aeneas built");
}

// ── Main ──────────────────────────────────────────────────────────────

async function main(): Promise<void> {
  console.log(chalk.bold("\nAeneas Install\n"));

  const { config, root } = loadConfig();
  const commit = config.aeneas.commit;
  const repoDir = getRepoDir(root);

  // Check if already installed at correct version
  const installed = await getInstalledVersion(root);
  if (installed && installed.startsWith(commit)) {
    const charonBin = findBinary("charon", root);
    const aeneasBin = findBinary("aeneas", root);
    if (charonBin && aeneasBin) {
      console.log(chalk.green(`Already up to date (${commit}). Skipping.`));
      return;
    }
  }

  await checkDependencies();

  console.log(chalk.bold("\nSetting up OCaml..."));
  const opamEnv = await setupOcaml(root);
  console.log(chalk.green("  OCaml environment ready\n"));

  await setupRepo(config.aeneas.repo, repoDir, commit);

  // The Rust toolchain is handled by `make setup-charon`: it clones Charon at
  // its pinned commit and builds it, and Charon's own rust-toolchain.toml makes
  // rustup auto-install the pinned nightly + components (rustc-dev, etc.).
  console.log();
  await buildCharon(repoDir, opamEnv);
  await buildAeneas(repoDir, opamEnv);

  // Verify binaries exist
  const charonBin = findBinary("charon", root);
  const aeneasBin = findBinary("aeneas", root);

  if (!charonBin || !aeneasBin) {
    throw new Error("Build completed but binaries not found at expected paths");
  }

  console.log(chalk.green("\nBuild complete!"));
  console.log(`  Charon: ${charonBin}`);
  console.log(`  Aeneas: ${aeneasBin}`);

  syncLeanToolchain(root);
}

main().catch((err) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
