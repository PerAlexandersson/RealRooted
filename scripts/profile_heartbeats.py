#!/usr/bin/env python3
"""Rank the declarations of a Lean file by heartbeats.

The file is copied to a temporary directory with `#count_heartbeats in` and a
`#print` tag before every declaration, elaborated once, and the counts are
printed in decreasing order.  The source file is not modified.

Usage, from the project root:

    scripts/profile_heartbeats.py RealRooted/Tactic/Examples/RowInterlacing.lean
    LEAN_CMD="lake-workspace env lean" scripts/profile_heartbeats.py FILE --top 20

`LEAN_CMD` (default `lake env lean`) is the command that elaborates one file
with the project's dependencies on the path; the imports must be built.
"""

from __future__ import annotations

import argparse
import os
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\] )?(?:private |protected )?(?:noncomputable )?"
    r"(theorem|lemma|example|def|instance|abbrev)\b\s*(\S*)"
)
TAG_RE = re.compile(r'^HB (\d+) (\S+)')
USED_RE = re.compile(r"Used (\d+) heartbeats")


def instrument(lines: list[str]) -> list[str]:
    """Insert a tag and `#count_heartbeats in` before each declaration, above its
    docstring and attributes."""
    out: list[str] = []
    for i, line in enumerate(lines):
        if i == 0 and line.startswith("import"):
            out += [line, "import Mathlib.Util.CountHeartbeats"]
            continue
        m = DECL_RE.match(line)
        if m:
            k = len(out)
            while True:
                if k > 0 and out[k - 1].lstrip().startswith("@["):
                    k -= 1
                    continue
                if k > 0 and out[k - 1].rstrip().endswith("-/"):
                    j = k - 1
                    while j > 0 and "/-" not in out[j]:
                        j -= 1
                    if "/--" in out[j]:
                        k = j
                        continue
                break
            tag = f'#print "HB {i + 1} {m.group(2) or m.group(1)}"'
            out[k:k] = [tag, "#count_heartbeats in"]
        out.append(line)
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("file", type=Path)
    parser.add_argument("--top", type=int, default=30, help="rows to print")
    args = parser.parse_args()

    lines = args.file.read_text(encoding="utf-8").split("\n")
    cmd = shlex.split(os.environ.get("LEAN_CMD", "lake env lean"))
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / args.file.name
        copy.write_text("\n".join(instrument(lines)), encoding="utf-8")
        proc = subprocess.run(cmd + [str(copy)], capture_output=True, text=True)
    output = proc.stdout + proc.stderr

    rows: list[tuple[int, int, str]] = []
    tag = (0, "?")
    for line in output.splitlines():
        if m := TAG_RE.match(line):
            tag = (int(m.group(1)), m.group(2))
        elif m := USED_RE.search(line):
            rows.append((int(m.group(1)), *tag))
    errors = [line for line in output.splitlines() if ": error" in line]
    for line in errors[:5]:
        print(line, file=sys.stderr)

    rows.sort(reverse=True)
    print(f"{sum(r[0] for r in rows):>10}  TOTAL ({len(rows)} declarations)")
    for count, line_no, name in rows[: args.top]:
        print(f"{count:>10}  {args.file}:{line_no}  {name}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
