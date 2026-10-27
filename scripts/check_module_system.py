#!/usr/bin/env python3
"""Check that RealRooted source files use the Lean module system.

Every `.lean` file under `RealRooted/` (and `RealRooted.lean`) must start with `module` right
after its copyright comment, unless it is listed in `scripts/non_module_files.txt`.  The list
holds the files that cannot be modules yet (example-only files, umbrellas over them, and files
whose tactic expansions need private declarations); see issue #2016.  It may only shrink:
a listed file that has become a module, or no longer exists, is also an error.

Exposure follows Mathlib: a file that declares no definitions (only theorems, notation,
syntax, ...) uses `public section`, not `@[expose] public section`; theorem bodies are never
exported, so exposing such a file only adds noise.  A file that defines things may use
`@[expose] public section`, or `public section` with `@[expose]` on the definitions whose bodies
importers must unfold.

Convert a new file with `python3 scripts/modularize.py FILE`.
`--update` drops converted or deleted files from the list; `--fix` rewrites the section header
of theorem-only files.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWLIST = ROOT / "scripts" / "non_module_files.txt"


def is_module(text: str) -> bool:
    """Whether the first command after the leading comments is `module`."""
    depth = 0
    for line in text.split("\n"):
        s = line.strip()
        if depth > 0 or s.startswith("/-") and not s.startswith("/-!"):
            depth += line.count("/-") - line.count("-/")
            continue
        if s == "" or s.startswith("--"):
            continue
        return s == "module"
    return False


EXPOSED = re.compile(r"^@\[expose\] public (noncomputable )?section\b", re.M)
DEFINITION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|public|noncomputable|meta|partial|unsafe|nonrec)\s+)*"
    r"(?:def|abbrev|instance|structure|class|inductive|opaque|irreducible_def)\b", re.M)


def exposes_without_definitions(text: str) -> bool:
    """Whether the file exposes its section although it declares no definitions."""
    return bool(EXPOSED.search(text)) and not DEFINITION.search(text)


def sources() -> list[str]:
    files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / "RealRooted").rglob("*.lean"))
    return ["RealRooted.lean", *files]


def read_allowlist() -> list[str]:
    lines = ALLOWLIST.read_text().split("\n")
    return [s for s in (x.strip() for x in lines) if s and not s.startswith("#")]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--update", action="store_true",
                        help="remove converted or deleted files from the allowlist")
    parser.add_argument("--fix", action="store_true",
                        help="use `public section` in files that declare no definitions")
    args = parser.parse_args()
    allowed = read_allowlist()
    present = set(sources())
    modules = {f for f in present if is_module((ROOT / f).read_text())}
    stale = [f for f in allowed if f not in present or f in modules]
    if args.update:
        keep = set(allowed) - set(stale)
        text = ALLOWLIST.read_text().split("\n")
        ALLOWLIST.write_text("\n".join(x for x in text if x.strip() not in stale or not x.strip()))
        print(f"removed {len(stale)} entries; {len(keep)} remain")
        return 0
    errors = [f"{f}: not a module; run `python3 scripts/modularize.py {f}`"
              for f in sorted(present - modules - set(allowed))]
    noisy = [f for f in sorted(modules) if exposes_without_definitions((ROOT / f).read_text())]
    if args.fix:
        for f in noisy:
            path = ROOT / f
            path.write_text(EXPOSED.sub(lambda m: f"public {m.group(1) or ''}section",
                                        path.read_text(), count=1))
        print(f"rewrote the section header of {len(noisy)} theorem-only files")
        noisy = []
    errors += [f"{f}: declares no definitions, so use `public section` instead of "
               "`@[expose] public section` (run with --fix)" for f in noisy]
    errors += [f"{f}: listed in {ALLOWLIST.relative_to(ROOT)} but "
               + ("missing" if f not in present else "already a module")
               + "; run with --update" for f in stale]
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print(f"{len(modules)} module files, {len(allowed)} allowlisted non-module files")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
