#!/usr/bin/env python3
"""Disposable indentation-only A/B/control experiment. No Git commands or remote writes."""

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
    require(original.startswith("/-\nCopyright (c) 2026 "),
            "All cases must start with a valid copyright header")
    imported = replace_once(original, "import translated.Funs\n",
                            "import translated.Funs\nimport Dalek32.Lint.Basic\n")
    corrected = replace_once(imported, "    result = x ⦄ := by\n",
                              "      result = x ⦄ := by\n")
    for label, text in [("A-original", original), ("B-import-only", imported),
                        ("C-corrected", corrected)]:
        (OUTPUT / f"{label}.lean").write_text(text)
    require("import Dalek32.LinterRepro\n" in (ROOT / "Dalek32.lean").read_text(),
            "Fixture must be imported by the library root")
    try:
        a = run("A-build", ["lake", "build", "--no-ansi"])
        require(not a["non_sorry_warning_lines"], "A: unexpected baseline style warning")
        require(not a["header_diagnostic"] and not a["indent_diagnostic"],
                "A: the hypothesized indentation-check gap was NOT reproduced")
        lint = run("A-environment-lint", ["lake", "exe", "runLinter", "Dalek32"])
        require(not lint["non_sorry_warning_lines"], "A: unexpected environment-lint warning")
        require(not lint["header_diagnostic"] and not lint["indent_diagnostic"],
                "A: environment lint reported a diagnostic; revise the diagnosis")

        FIXTURE.write_text(imported)
        b = run("B-import-only", ["lake", "build", "Dalek32.LinterRepro", "--no-ansi"])
        require(b["indent_diagnostic"] and not b["header_diagnostic"],
                "B: import-only control did not isolate the expected indentation diagnostic")
        require(bool(b["non_sorry_warning_lines"]),
                "B: expected warning would not trigger the existing CI warning gate")

        FIXTURE.write_text(corrected)
        c = run("C-corrected", ["lake", "build", "Dalek32.LinterRepro", "--no-ansi"])
        require(not c["non_sorry_warning_lines"], "C: corrected control still warns")
        require(not c["header_diagnostic"] and not c["indent_diagnostic"],
                "C: corrected control still reports a header or indentation diagnostic")
        summary = (
            "## Specification-indentation reproduction confirmed\n\n"
            "A: valid header and proof with a four-space postcondition build and pass "
            "environment lint without the indentation diagnostic.\n\n"
            "B: adding only `import Dalek32.Lint.Basic` reports the indentation defect. "
            "This non-sorry warning would fail the existing Lean CI warning gate.\n\n"
            "C: correcting only the postcondition indentation removes the warning.\n\n"
            "The header is valid throughout. No linter options were disabled and no "
            "mathematical proof was changed. The first run had already shown that Mathlib's "
            "standard header checker catches the malformed header.\n"
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
