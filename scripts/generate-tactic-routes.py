#!/usr/bin/env python3
"""Generate the row-tactic route reference and its small Lean lookup table."""

from __future__ import annotations

import argparse
import json
import re
import sys
import textwrap
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "scripts" / "tactic_routes.json"
MARKDOWN = ROOT / "RealRooted" / "Tactic" / "ROUTES.md"
LEAN = ROOT / "RealRooted" / "Tactic" / "Row" / "Routes.lean"
TACTIC_ROOT = ROOT / "RealRooted" / "Tactic"
REQUIRED = {
    "name",
    "frontEnds",
    "conclusion",
    "theorems",
    "module",
    "summary",
    "requires",
    "examples",
    "pseudo",
}
LITERAL_ROUTE = re.compile(r"\brow(?:Route|Veto|Skip)\s+`([A-Za-z0-9_'.]+)")


def fail(message: str) -> None:
    raise ValueError(message)


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def load_registry() -> list[dict[str, object]]:
    data = json.loads(REGISTRY.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or not isinstance(data.get("routes"), list):
        fail("the registry must be an object with a routes array")
    routes = data["routes"]
    names: set[str] = set()
    positions: dict[str, set[int]] = defaultdict(set)
    for index, route in enumerate(routes):
        where = f"routes[{index}]"
        if not isinstance(route, dict):
            fail(f"{where} must be an object")
        missing = REQUIRED - route.keys()
        if missing:
            fail(f"{where} is missing: {', '.join(sorted(missing))}")
        name = route["name"]
        if not isinstance(name, str) or not name:
            fail(f"{where}.name must be a nonempty string")
        if name in names:
            fail(f"duplicate route name: {name}")
        names.add(name)
        if not isinstance(route["pseudo"], bool):
            fail(f"{where}.pseudo must be a boolean")
        for key in ("conclusion", "module", "summary", "requires"):
            if not isinstance(route[key], str) or not route[key]:
                fail(f"{where}.{key} must be a nonempty string")
        for key in ("theorems", "examples"):
            values = route[key]
            if not isinstance(values, list) or not all(isinstance(x, str) for x in values):
                fail(f"{where}.{key} must be an array of strings")
        front_ends = route["frontEnds"]
        if not isinstance(front_ends, list) or not front_ends:
            fail(f"{where}.frontEnds must be a nonempty array")
        for front_end in front_ends:
            if not isinstance(front_end, dict):
                fail(f"{where}.frontEnds entries must be objects")
            if set(front_end) - {"tactic", "position", "selectable"}:
                fail(f"{where}.frontEnds has an unknown field")
            tactic = front_end.get("tactic")
            position = front_end.get("position")
            selectable = front_end.get("selectable", True)
            if not isinstance(tactic, str) or not tactic:
                fail(f"{where}.frontEnds tactic must be a nonempty string")
            if not isinstance(position, int) or position <= 0:
                fail(f"{where}.frontEnds position must be a positive integer")
            if not isinstance(selectable, bool):
                fail(f"{where}.frontEnds selectable must be a boolean")
            if position in positions[tactic]:
                fail(f"duplicate position {position} in {tactic}")
            positions[tactic].add(position)
        for example in route["examples"]:
            if not module_path(example).is_file():
                fail(f"example module does not exist: {example}")
    check_code_names(names)
    return routes


def check_code_names(names: set[str]) -> None:
    sources = list(TACTIC_ROOT.rglob("*.lean"))
    texts = [path.read_text(encoding="utf-8") for path in sources]
    literals = set().union(*(set(LITERAL_ROUTE.findall(text)) for text in texts))
    missing = sorted(literals - names)
    if missing:
        fail("literal route names missing from the registry: " + ", ".join(missing))
    unused = []
    for name in sorted(names):
        token = re.compile(rf"`{re.escape(name)}(?![A-Za-z0-9_'])")
        if not any(token.search(text) for text in texts):
            unused.append(name)
    if unused:
        fail("registry routes absent from tactic code: " + ", ".join(unused))


def front_end_routes(routes: list[dict[str, object]]) -> dict[str, list[dict[str, object]]]:
    result: dict[str, list[dict[str, object]]] = defaultdict(list)
    for route in routes:
        for front_end in route["frontEnds"]:
            result[front_end["tactic"]].append(
                {"position": front_end["position"], "route": route, **front_end}
            )
    for entries in result.values():
        entries.sort(key=lambda entry: entry["position"])
    return dict(result)


def wrap_text(value: str, width: int = 92) -> list[str]:
    return textwrap.wrap(value, width=width, break_long_words=False, break_on_hyphens=False)


def markdown_cell(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def markdown_table(entries: list[dict[str, object]]) -> list[str]:
    lines = [
        "| # | route | proves | main theorem(s) |",
        "|---:|---|---|---|",
    ]
    for entry in entries:
        route = entry["route"]
        label = f"`{route['name']}`" + (" (pseudo)" if route["pseudo"] else "")
        theorems = ", ".join(
            f"`{name.removeprefix('RealRooted.')}`" for name in route["theorems"]
        ) or "—"
        lines.append(
            f"| {entry['position']} | {label} | {markdown_cell(route['conclusion'])} "
            f"| {theorems} |"
        )
    return lines


def markdown_bullet(label: str, value: str) -> list[str]:
    prefix = f"- **{label}:** "
    parts = textwrap.wrap(
        value,
        width=96,
        initial_indent=prefix,
        subsequent_indent="  ",
        break_long_words=False,
        break_on_hyphens=False,
    )
    return parts or [prefix]


def render_markdown(routes: list[dict[str, object]]) -> str:
    by_front_end = front_end_routes(routes)
    lines = [
        "*Generated by scripts/generate-tactic-routes.py; do not edit.*",
        "# Row-tactic routes",
        "",
        "The `via` hint selects one named route, for example",
        "`rr_row_splits (via := closedForm)`. The tables below follow dispatch order;",
        "pseudo-routes describe probes or nested dispatch rather than a mathematical backend.",
        "",
        "Enable the attempt table with `set_option rr.row.explain true`. Heartbeat counts are",
        "shown by default; set `rr.row.explain.heartbeats false` when stable output matters.",
        "An indented route ran inside its parent, so the parent's heartbeat total includes it.",
        "Set `rr.row.disable` to a comma-separated list of route names to skip, for example",
        "`set_option rr.row.disable \"pathPower,derivativeXMul\"`.",
        "",
        "Read each row as a goal shape and its main theorem(s). The route sections record",
        "side conditions, implementing modules, and regression examples.",
        "",
    ]
    for front_end, entries in by_front_end.items():
        lines.extend([f"## `{front_end}`", ""])
        lines.extend(markdown_table(entries))
        lines.append("")
    lines.extend(["# Route details", ""])
    for route in routes:
        pseudo = " (pseudo)" if route["pseudo"] else ""
        examples = ", ".join(f"`{name}`" for name in route["examples"])
        lines.extend([f"## `{route['name']}`{pseudo}", ""])
        lines.extend(markdown_bullet("Summary", route["summary"]))
        lines.extend(markdown_bullet("Side conditions", route["requires"]))
        lines.extend(markdown_bullet("Module", f"`{route['module']}`"))
        lines.extend(markdown_bullet("Regression examples", examples or "None recorded."))
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def lean_string_field(prefix: str, value: str, indent: str = "    ") -> list[str]:
    chunks = wrap_text(value, 66)
    if len(chunks) == 1:
        return [f"{indent}{prefix} := {lean_string(chunks[0])}"]
    lines = [f"{indent}{prefix} := {lean_string(chunks[0] + ' ')} ++"]
    for index, chunk in enumerate(chunks[1:]):
        suffix = " ++" if index + 1 < len(chunks[1:]) else ""
        spacer = " " if suffix else ""
        lines.append(f"{indent}  {lean_string(chunk + spacer)}{suffix}")
    return lines


def lean_name_list(names: list[str], indent: str) -> list[str]:
    if not names:
        return [f"{indent}[]"]
    lines = [f"{indent}["]
    for index, name in enumerate(names):
        comma = "," if index + 1 < len(names) else ""
        lines.append(f"{indent}  `{name}{comma}")
    lines.append(f"{indent}]")
    return lines


def render_lean(routes: list[dict[str, object]]) -> str:
    by_front_end = front_end_routes(routes)
    lines = [
        "-- generated by scripts/generate-tactic-routes.py; do not edit",
        "module",
        "",
        "public import Lean",
        "",
        "/-! # Generated row-route metadata -/",
        "",
        "@[expose] public section",
        "",
        "open Lean",
        "",
        "namespace RealRooted.Tactic",
        "",
        "/-- The runtime metadata needed by row-tactic dispatch and environment checks. -/",
        "structure RowRouteInfo where",
        "  /-- The stable route name used by `via`. -/",
        "  name : Name",
        "  /-- The row front ends that can attempt the route. -/",
        "  frontEnds : List String",
        "  /-- The mathematical conclusion proved by the route. -/",
        "  conclusion : String",
        "  /-- The main declarations applied by the route. -/",
        "  theorems : List Name",
        "",
        "/-- Every row route, generated from `scripts/tactic_routes.json`. -/",
        "def rowRouteTable : List RowRouteInfo := [",
    ]
    for route_index, route in enumerate(routes):
        comma = "," if route_index + 1 < len(routes) else ""
        lines.append(f"  {{ name := `{route['name']}")
        front_ends = [item["tactic"] for item in route["frontEnds"]]
        lines.append("    frontEnds := [")
        for index, front_end in enumerate(front_ends):
            item_comma = "," if index + 1 < len(front_ends) else ""
            lines.append(f"      {lean_string(front_end)}{item_comma}")
        lines.append("    ]")
        lines.extend(lean_string_field("conclusion", route["conclusion"]))
        lines.append("    theorems :=")
        lines.extend(lean_name_list(route["theorems"], "      "))
        lines.append(f"  }}{comma}")
    lines.extend([
        "]",
        "",
        "/-- The selectable route names of a front end, in dispatch order. -/",
        "def rowRoutesOf (frontEnd : String) : List Name :=",
        "  match frontEnd with",
    ])
    for front_end, entries in by_front_end.items():
        selected = [
            entry["route"]["name"]
            for entry in entries
            if entry.get("selectable", True)
        ]
        lines.append(f"  | {lean_string(front_end)} => [")
        for index, name in enumerate(selected):
            comma = "," if index + 1 < len(selected) else ""
            lines.append(f"      `{name}{comma}")
        lines.append("    ]")
    lines.extend(["  | _ => []", "", "end RealRooted.Tactic", ""])
    rendered = "\n".join(lines)
    too_long = [(i, line) for i, line in enumerate(rendered.splitlines(), 1) if len(line) > 100]
    if too_long:
        fail(f"generated Routes.lean line {too_long[0][0]} exceeds 100 characters")
    return rendered


def check_output(path: Path, generated: str) -> bool:
    current = path.read_text(encoding="utf-8") if path.exists() else ""
    if current == generated:
        return True
    print(f"{path.relative_to(ROOT)} is stale", file=sys.stderr)
    return False


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if generated files are stale")
    args = parser.parse_args()
    try:
        routes = load_registry()
        markdown = render_markdown(routes)
        lean = render_lean(routes)
    except (OSError, json.JSONDecodeError, ValueError) as error:
        print(f"route registry error: {error}", file=sys.stderr)
        return 1
    if args.check:
        return 0 if check_output(MARKDOWN, markdown) and check_output(LEAN, lean) else 1
    MARKDOWN.write_text(markdown, encoding="utf-8")
    LEAN.write_text(lean, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
