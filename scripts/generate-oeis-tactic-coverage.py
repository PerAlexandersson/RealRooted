#!/usr/bin/env python3
"""Generate the OEIS tactic coverage ledger from Lean example files."""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "RealRooted" / "Tactic" / "Examples"
CONCRETE = ROOT / "RealRooted" / "OEIS"
OUTPUT = ROOT / "RealRooted" / "Tactic" / "OEIS_COVERAGE.md"

OEIS_RE = re.compile(r"A\d{6}")
ROUTE_RE = re.compile(r"\b(rr_[A-Za-z0-9_]+)")
ARG_RE = re.compile(r"\b([a-z][A-Za-z0-9_]*)\s*:=")
SIGN_ONLY = {
    "rr_sign",
    "rr_sign_at_roots",
    "rr_sign_at_roots_upper",
    "rr_sign_at_roots_window",
    "rr_sign_at_roots_with_factor",
}


@dataclass
class Coverage:
    sources: set[str] = field(default_factory=set)
    shapes: list[str] = field(default_factory=list)
    routes: set[str] = field(default_factory=set)
    arguments: set[str] = field(default_factory=set)


def comment_text(lines: list[str], index: int) -> str:
    """Return the consecutive line-comment paragraph containing index."""
    start = index
    while start > 0 and lines[start - 1].lstrip().startswith("--"):
        start -= 1
    stop = index + 1
    while stop < len(lines) and lines[stop].lstrip().startswith("--"):
        stop += 1
    parts = []
    for line in lines[start:stop]:
        text = line.strip().removeprefix("/--").removeprefix("--").strip()
        text = text.removesuffix("-/").strip()
        text = OEIS_RE.sub("", text)
        text = text.replace("`/`", "/").replace("``", "")
        text = re.sub(r"^[/,;:\s]+", "", text)
        if text:
            parts.append(text)
    return " ".join(parts)


def example_block(lines: list[str], index: int) -> str:
    """Return the next example block following a comment at index."""
    start = index + 1
    while start < len(lines) and not lines[start].lstrip().startswith("example"):
        if OEIS_RE.search(lines[start]):
            return ""
        start += 1
    if start == len(lines):
        return ""
    stop = start + 1
    while stop < len(lines):
        stripped = lines[stop].lstrip()
        if stripped.startswith("example") or stripped.startswith("end "):
            break
        if OEIS_RE.search(lines[stop]) and stripped.startswith("--"):
            break
        stop += 1
    return "\n".join(lines[start:stop])


def clean_shape(text: str) -> str:
    text = text.replace("|", "\\|")
    text = re.sub(r"\s+", " ", text).strip()
    return text[:240] + ("..." if len(text) > 240 else "")


def collect() -> tuple[dict[str, Coverage], set[str]]:
    rows: dict[str, Coverage] = {}
    for path in sorted(EXAMPLES.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        source = path.relative_to(ROOT).as_posix()
        for index, line in enumerate(lines):
            ids = OEIS_RE.findall(line)
            if not ids:
                continue
            block = example_block(lines, index)
            shape = clean_shape(comment_text(lines, index))
            routes = set(ROUTE_RE.findall(block))
            arguments = set(ARG_RE.findall(block))
            for oeis_id in ids:
                row = rows.setdefault(oeis_id, Coverage())
                row.sources.add(source)
                if shape and shape not in row.shapes:
                    row.shapes.append(shape)
                row.routes.update(routes)
                row.arguments.update(arguments)

    concrete_ids: set[str] = set()
    if CONCRETE.exists():
        for path in CONCRETE.rglob("*.lean"):
            concrete_ids.update(OEIS_RE.findall(path.read_text(encoding="utf-8")))
    for oeis_id in concrete_ids:
        row = rows.setdefault(oeis_id, Coverage())
        row.sources.add(f"RealRooted/OEIS/{oeis_id}.lean")
        if not row.shapes:
            row.shapes.append("concrete sequence-facing theorem")
    return rows, concrete_ids


def status(row: Coverage, oeis_id: str, concrete_ids: set[str]) -> str:
    if oeis_id in concrete_ids:
        return "formalized"
    if row.routes and row.routes <= SIGN_ONLY:
        return "fragment"
    if row.routes:
        return "shell"
    return "documented"


def certificates(row: Coverage) -> str:
    if not row.arguments:
        if row.routes and row.routes <= SIGN_ONLY:
            return "root sign/interval hypotheses"
        if row.routes:
            return "implicit/local certificates resolved by the route"
        return "not recorded"
    ignored = {"certificate", "route"}
    args = sorted(row.arguments - ignored)
    return ", ".join(f"`{arg}`" for arg in args) or "route-specific certificate"


def blocker(kind: str) -> str:
    if kind == "formalized":
        return "none"
    if kind == "fragment":
        return "full recurrence shell, base cases, degree, and leading-coefficient data"
    if kind == "shell":
        return "concrete row definition and proofs of the listed certificates"
    return "executable tactic route and its certificates"


def render() -> str:
    rows, concrete_ids = collect()
    counts = {kind: 0 for kind in ("formalized", "shell", "fragment", "documented")}
    for oeis_id, row in rows.items():
        counts[status(row, oeis_id, concrete_ids)] += 1

    out = [
        "# OEIS Tactic Coverage",
        "",
        "This file is generated by `scripts/generate-oeis-tactic-coverage.py` from",
        "the executable examples in `RealRooted/Tactic/Examples`. Do not edit the",
        "table manually. Regenerate it after adding or changing an OEIS-labelled",
        "example:",
        "",
        "```bash",
        "python3 scripts/generate-oeis-tactic-coverage.py",
        "python3 scripts/generate-oeis-tactic-coverage.py --check",
        "```",
        "",
        "The status values deliberately separate tactic capability from completed",
        "sequence formalization:",
        "",
        "- `formalized`: a concrete sequence-facing theorem exists under `RealRooted/OEIS`;",
        "- `shell`: an executable abstract recurrence shell reaches `Prec` or `Splits`;",
        "- `fragment`: only a sign or root-window subcertificate is exercised;",
        "- `documented`: the ID is mentioned, but no executable route was associated.",
        "",
        f"Current totals: **{len(rows)} IDs**; **{counts['formalized']} formalized**, "
        f"**{counts['shell']} shells**, **{counts['fragment']} fragments**, and "
        f"**{counts['documented']} documented-only**.",
        "",
        "| OEIS ID | Status | Recurrence shape / test intent | Tactic route | Required certificates | Missing blocker |",
        "|---|---|---|---|---|---|",
    ]
    for oeis_id in sorted(rows):
        row = rows[oeis_id]
        kind = status(row, oeis_id, concrete_ids)
        shape = "<br>".join(row.shapes[:2]) or "See source example."
        if len(row.shapes) > 2:
            shape += f"<br>+{len(row.shapes) - 2} additional test intents"
        routes = ", ".join(f"`{route}`" for route in sorted(row.routes)) or "none"
        out.append(
            f"| {oeis_id} | `{kind}` | {shape} | {routes} | "
            f"{certificates(row)} | {blocker(kind)} |"
        )
    out.extend([
        "",
        "## Unsupported Router Buckets",
        "",
        "These are explicit tactic failure modes rather than OEIS-specific rows.",
        "They are tested with `#guard_msgs` in `RealRooted/Tactic/Examples/OEIS.lean`.",
        "",
        "| Bucket | Missing certificate |",
        "|---|---|",
        "| `jacobiOrHypergeom` | classical coefficient formula and root-location bridge |",
        "| `transformNeeded` | transformed recurrence and root-window certificate |",
        "| `vectorNeeded` | vector/interlacing or PF certificate; the scalar wrapper is invalid |",
        "",
    ])
    return "\n".join(out)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if the ledger is stale")
    args = parser.parse_args()
    generated = render()
    if args.check:
        current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.exists() else ""
        if current != generated:
            print(f"{OUTPUT.relative_to(ROOT)} is stale", file=sys.stderr)
            return 1
        return 0
    OUTPUT.write_text(generated, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
