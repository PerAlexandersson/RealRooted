#!/usr/bin/env python3
"""Convert RealRooted source files to the Lean module system.

Usage: ``python3 scripts/modularize.py [--check] MODULE_OR_PATH...``

Each file gets the layout already used by the module files of the repository:

    /- copyright header -/
    module

    public import ...

    /-! module docstring -/

    @[expose] public section      -- or ``public section``, see below

Every import becomes ``public import``.  Following Mathlib, a file that declares definitions is
exposed (``@[expose] public section``) so that importers can still unfold them (``rfl``,
``decide``, ``simp``); a file with only theorems, notation or syntax gets ``public section``,
since theorem bodies are never exported anyway (that is where the rebuild savings come from).
``scripts/check_module_system.py`` enforces the second rule.
Files that already start with ``module`` are left unchanged.  A ``module`` file
may only import other modules, so convert files bottom-up along the import graph.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_system import DEFINITION  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^(?:(public|private)\s+)?(meta\s+)?import\s+\S+")


def _block_end(lines: list[str], start: int) -> int:
    """Index of the line closing the block comment opened on ``lines[start]``."""
    depth = 0
    for i in range(start, len(lines)):
        depth += lines[i].count("/-") - lines[i].count("-/")
        if depth <= 0:
            return i
    raise ValueError("unterminated block comment")


def convert(text: str) -> str:
    lines = text.split("\n")
    if any(line.strip() == "module" for line in lines[:40]):
        return text
    i = 0
    copyright_end = -1
    if lines and lines[0].startswith("/-") and not lines[0].startswith("/-!"):
        copyright_end = _block_end(lines, 0)
        i = copyright_end + 1
    # Header: blank lines, line comments and imports.
    header_end = i
    j = i
    while j < len(lines):
        s = lines[j].strip()
        if s == "" or s.startswith("--"):
            j += 1
            continue
        if IMPORT_RE.match(s):
            lines[j] = re.sub(r"^(?:public\s+)?import\s", "public import ", lines[j])
            header_end = j + 1
            j += 1
            continue
        break
    # Optional module docstring right after the imports.
    k = header_end
    while k < len(lines) and lines[k].strip() == "":
        k += 1
    insert_at = header_end
    if k < len(lines) and lines[k].lstrip().startswith("/-!"):
        insert_at = _block_end(lines, k) + 1
    body = lines[insert_at:]
    while body and body[0].strip() == "":
        body.pop(0)
    head = lines[:insert_at]
    while head and head[-1].strip() == "":
        head.pop()
    defines = DEFINITION.search("\n".join(body)) is not None
    head += ["", "@[expose] public section" if defines else "public section", ""]
    pre = head[: copyright_end + 1]
    rest = head[copyright_end + 1 :]
    while rest and rest[0].strip() == "":
        rest.pop(0)
    return "\n".join(pre + ["module", ""] + rest + body)


def resolve(arg: str) -> Path:
    if arg.endswith(".lean"):
        return Path(arg)
    return ROOT / (arg.replace(".", "/") + ".lean")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--check", action="store_true", help="only list files to convert")
    parser.add_argument("targets", nargs="+")
    args = parser.parse_args()
    changed = 0
    for target in args.targets:
        path = resolve(target)
        old = path.read_text()
        new = convert(old)
        if new != old:
            changed += 1
            if args.check:
                print(path)
            else:
                path.write_text(new)
    print(f"{'would convert' if args.check else 'converted'} {changed} file(s)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
