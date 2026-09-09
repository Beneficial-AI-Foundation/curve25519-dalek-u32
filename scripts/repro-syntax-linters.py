#!/usr/bin/env python3
"""Disposable A/B/control experiment. No Git commands or remote writes."""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "Dalek32/LinterRepro.lean"
OUTPUT = Path(os.environ.get("RUNNER_TEMP", tempfile.gettempdir())) / "dalek32-linter-repro"
HEADER = "Copyright line should start with 'Copyright (c) YYYY'"
INDENT = "Postcondition body is at column 4, expected 6."
RESULTS = []


def run(label, command):
    """Save unfiltered compiler output and the actual exit code."""
    print(f"\n=== {label}: {' '.join(command)} ===", flush=True)
    with (OUTPUT / f"{label}.log").open("w") as log:
        with subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True) as process:
            for line in process.stdout:
                print(line, end="", flush=True)
                log.write(line)
            code = process.wait()
    text = (OUTPUT / f"{label}.log").read_text()
    non_sorry = [line for line in text.splitlines()
                 if "warning:" in line and not re.search(r"declaration uses .sorry", line)]
    record = {
        "label": label, "command": command, "exit_code": code,
        "fixture_sha256": hashlib.sha256(FIXTURE.read_bytes()).hexdigest(),
        "header_diagnostic": HEADER in text, "indent_diagnostic": INDENT in text,
        "non_sorry_warning_lines": non_sorry,
    }
    RESULTS.append(record)
    (OUTPUT / "results.json").write_text(json.dumps(RESULTS, indent=2) + "\n")
    if code != 0 or re.search(r"\berror:", text):
        raise RuntimeError(f"{label}: compilation/lint failed; inspect its raw log")
    return record


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError(f"Expected exactly one occurrence of {old!r}")
    return text.replace(old, new, 1)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    OUTPUT.mkdir(parents=True, exist_ok=True)
    original = FIXTURE.read_text()
    imported = replace_once(original, "import translated.Funs\n",
                            "import translated.Funs\nimport Dalek32.Lint.Basic\n")
    corrected = replace_once(imported, "Copyright 2026 ", "Copyright (c) 2026 ")
    corrected = replace_once(corrected, "    result = x ⦄ := by\n",
                              "      result = x ⦄ := by\n")
    for label, text in [("A-original", original), ("B-import-only", imported),
                        ("C-corrected", corrected)]:
        (OUTPUT / f"{label}.lean").write_text(text)
    require("import Dalek32.LinterRepro\n" in (ROOT / "Dalek32.lean").read_text(),
            "Fixture must be imported by the library root, including for headerAlt's guard")
    try:
        a = run("A-build", ["lake", "build", "--no-ansi"])
        require(not a["non_sorry_warning_lines"], "A: unexpected baseline style warning")
        require(not a["header_diagnostic"] and not a["indent_diagnostic"],
                "A: the hypothesized missing checks were NOT reproduced")
        lint = run("A-environment-lint", ["lake", "exe", "runLinter", "Dalek32"])
        require(not lint["header_diagnostic"] and not lint["indent_diagnostic"],
                "A: environment lint detected the defects; revise the diagnosis")

        FIXTURE.write_text(imported)
        b = run("B-import-only", ["lake", "build", "Dalek32.LinterRepro", "--no-ansi"])
        require(b["header_diagnostic"] and b["indent_diagnostic"],
                "B: adding the import did not activate BOTH expected diagnostics")
        require(bool(b["non_sorry_warning_lines"]),
                "B: expected warnings would not trigger the existing CI warning gate")

        FIXTURE.write_text(corrected)
        c = run("C-corrected", ["lake", "build", "Dalek32.LinterRepro", "--no-ansi"])
        require(not c["non_sorry_warning_lines"], "C: corrected control still warns")
        require(not c["header_diagnostic"] and not c["indent_diagnostic"],
                "C: corrected control still reports the deliberate defects")
        summary = (
            "## Syntax-linter reproduction confirmed\n\n"
            "A: valid proof with two style defects builds and passes environment lint.\n\n"
            "B: adding only `import Dalek32.Lint.Basic` reports BOTH defects. "
            "These non-sorry warnings would fail the existing Lean CI warning gate.\n\n"
            "C: correcting only the header and postcondition indentation removes the warnings.\n\n"
            "No linter options were disabled and no mathematical proof was changed.\n"
        )
        (OUTPUT / "SUMMARY.md").write_text(summary)
        if os.environ.get("GITHUB_STEP_SUMMARY"):
            with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as file:
                file.write(summary)
        print(summary)
    finally:
        FIXTURE.write_text(original)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"REPRODUCTION NOT CONFIRMED: {error}", file=sys.stderr)
        sys.exit(1)
