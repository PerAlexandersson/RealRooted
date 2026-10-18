#!/usr/bin/env python3
"""Check Mathlib's file-header conventions on the upstream targets (`RealRooted/Mathlib/**`).

This mirrors the rules of Mathlib's `linter.style.header` that apply outside Mathlib itself:

* the file starts with the copyright comment
  ```
  /-
  Copyright (c) YYYY Name, Name. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Name, Name
  -/
  ```
  where the authors line uses `, ` (not `and`), has no double spaces and no final period;
* the first command after the `module`/`import` header is the module docstring `/-! ... -/`;
* no import is repeated.

The lakefile cannot enable `linter.style.header` for one directory only, and `set_option` is
forbidden, so this script enforces the convention for the upstream targets.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "RealRooted" / "Mathlib"
LICENSE = "Released under Apache 2.0 license as described in the file LICENSE."
COPYRIGHT = re.compile(r"Copyright \(c\) \d{4} (\S.*)\. All rights reserved\.")
HEADER_LINE = re.compile(r"(module|(public |meta |private )*import( all)? \S+)\s*(--.*)?")


def check_authors(line: str) -> list[str]:
    if not line.startswith("Authors: "):
        return ["the fourth line should be 'Authors: ...'"]
    errors = []
    names = line[len("Authors: "):]
    if not names.strip():
        errors.append("add at least one author")
    if "  " in line:
        errors.append("double spaces in the authors line")
    if " and " in line:
        errors.append("use ', ' instead of 'and' between authors")
    if line.rstrip().endswith("."):
        errors.append("the authors line should not end with a period")
    return errors


def check_file(path: Path) -> list[str]:
    lines = path.read_text(encoding="utf-8").split("\n")
    errors: list[str] = []
    head = lines[:5]
    if len(head) < 5 or head[0] != "/-" or head[4] != "-/":
        return ["missing copyright header (a `/-` ... `-/` block of four lines at the top)"]
    if not COPYRIGHT.fullmatch(head[1]):
        errors.append("the second line should be 'Copyright (c) YYYY Names. All rights reserved.'")
    if head[2] != LICENSE:
        errors.append(f"the third line should be '{LICENSE}'")
    errors += check_authors(head[3])
    imports: list[str] = []
    i = 5
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped == "" or stripped.startswith("--"):
            i += 1
            continue
        if HEADER_LINE.fullmatch(stripped):
            if stripped != "module":
                imports.append(stripped.split("--")[0].strip())
            i += 1
            continue
        break
    if i >= len(lines) or not lines[i].startswith("/-!"):
        errors.append("the first command after the imports should be the module docstring `/-! -/`")
    duplicates = sorted({imp for imp in imports if imports.count(imp) > 1})
    errors += [f"duplicate import `{imp}`" for imp in duplicates]
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("files", nargs="*", type=Path, help="files to check (default: all targets)")
    args = parser.parse_args()
    files = args.files or sorted(TARGET.rglob("*.lean"))
    failures = 0
    for path in files:
        for error in check_file(path):
            print(f"{path.relative_to(ROOT) if path.is_absolute() else path}: {error}")
            failures += 1
    if failures:
        print(f"error: {failures} header problem(s) in the upstream targets")
        return 1
    print(f"ok: {len(files)} upstream target file(s) follow the Mathlib header conventions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
