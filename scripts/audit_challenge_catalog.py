#!/usr/bin/env python3
"""Prepare and collect the Lean audit for the curated challenge catalogue.

The source phase validates the opt-in catalogue blocks and resolves selected
declarations to their physical Lean files.  The Lean phase is deliberately
separate: ``--generate`` writes a temporary module whose ``run_cmd`` inspects
the imported environment with ``Lean.collectAxioms``.  After the integrator
runs that module through ``lake-workspace``, ``--collect`` turns its marker
output into the frozen JSON report consumed by the Pages renderer.

Typical integrator commands are::

    python3 scripts/audit_challenge_catalog.py --generate /tmp/catalog-audit.lean
    lake-workspace lean /tmp/catalog-audit.lean > /tmp/catalog-audit.raw
    python3 scripts/audit_challenge_catalog.py --collect /tmp/catalog-audit.raw \
      --report /tmp/catalog-audit.json

The first command does not invoke Lean, Lake, or a build.  The generated file
is temporary and must not be committed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import tomllib
from dataclasses import dataclass
from typing import Any


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
SECTIONS = frozenset({"concepts", "families", "theorems"})
CATALOG_MARKER = "<!-- realrooted-catalog\n"
CATALOG_END = "-->"
CONTENT_START = "<!-- realrooted-catalog-content -->"
CONTENT_END = "<!-- /realrooted-catalog-content -->"
SLUG_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$")
DECL_RE = re.compile(
    r"^\s*(?P<private>private\s+)?"
    r"(?:(?:protected|noncomputable)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance)"
    r"\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
SHA_RE = re.compile(r"^[0-9a-f]{40}$")


@dataclass(frozen=True)
class Record:
    name: str
    expected_kind: str
    module: str
    source_path: pathlib.Path
    source_line: int


@dataclass(frozen=True)
class Page:
    path: pathlib.Path
    section: str
    slug: str
    definitions: tuple[dict[str, str], ...]
    theorems: tuple[dict[str, str], ...]
    content: str


def repo_root_from_args() -> pathlib.Path:
    return pathlib.Path(__file__).resolve().parents[1]


def strip_comments_and_strings(text: str) -> str:
    """Blank Lean comments and strings while preserving line positions."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if block_depth:
            if char == "/" and next_char == "-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif char == "-" and next_char == "/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == "-" and next_char == "-":
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
            continue
        if char == "/" and next_char == "-":
            block_depth = 1
            output.extend("  ")
            index += 2
            continue
        if char == '"':
            in_string = True
            output.append(" ")
            index += 1
            continue
        output.append(char)
        index += 1
    return "".join(output)


def extract_block(text: str, start: str, end: str) -> str | None:
    first = text.find(start)
    if first < 0:
        return None
    second = text.find(start, first + len(start))
    if second >= 0:
        raise ValueError(f"duplicate marker {start!r}")
    finish = text.find(end, first + len(start))
    if finish < 0:
        raise ValueError(f"unterminated marker {start!r}")
    return text[first + len(start) : finish].strip("\n")


def extract_content(text: str) -> str | None:
    first = text.find(CONTENT_START)
    if first < 0:
        return None
    second = text.find(CONTENT_START, first + len(CONTENT_START))
    if second >= 0:
        raise ValueError("duplicate catalogue-content marker")
    finish = text.find(CONTENT_END, first + len(CONTENT_START))
    if finish < 0:
        raise ValueError("unterminated catalogue-content marker")
    return text[first + len(CONTENT_START) : finish].strip() + "\n"


def validate_content(content: str, path: pathlib.Path) -> None:
    headings = [line for line in content.splitlines() if line.startswith("# ")]
    if len(headings) != 1:
        raise ValueError(f"{path}: content must contain exactly one H1")
    reference_positions = [
        index
        for index, line in enumerate(content.splitlines())
        if line.strip() == "## References"
    ]
    if len(reference_positions) != 1:
        raise ValueError(f"{path}: content must contain exactly one ## References")
    lines = content.splitlines()
    references = lines[reference_positions[0] + 1 :]
    if not any(line.strip() and not line.startswith("## ") for line in references):
        raise ValueError(f"{path}: ## References must have nonempty content")


def module_name_for_path(repo_root: pathlib.Path, path: pathlib.Path) -> str:
    return ".".join(path.relative_to(repo_root).with_suffix("").parts)


def local_module_paths(repo_root: pathlib.Path) -> dict[str, pathlib.Path]:
    return {
        module_name_for_path(repo_root, path): path
        for path in [
            repo_root / "RealRooted.lean",
            *sorted((repo_root / "RealRooted").rglob("*.lean")),
        ]
    }


def imports_for(path: pathlib.Path) -> set[str]:
    return {
        match.group(1)
        for line in path.read_text(encoding="utf-8").splitlines()
        if (match := IMPORT_RE.match(line))
    }


def import_closure(module: str, imports: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    pending = [module]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        pending.extend(imports.get(current, set()) - seen)
    return seen


def declaration_locations(path: pathlib.Path) -> dict[str, tuple[str, int, bool]]:
    clean = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    namespace: list[str] = []
    locations: dict[str, tuple[str, int, bool]] = {}
    for line_number, line in enumerate(clean.splitlines(), start=1):
        namespace_match = NAMESPACE_RE.match(line)
        if namespace_match:
            namespace.extend(namespace_match.group(1).split("."))
            continue
        if re.match(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\s*$", line):
            if namespace:
                namespace.pop()
            continue
        declaration = DECL_RE.match(line)
        if declaration:
            local_name = declaration.group("name")
            full_name = ".".join([*namespace, local_name])
            kind = declaration.group("kind")
            locations[full_name] = (kind, line_number, bool(declaration.group("private")))
    return locations


def parse_page(path: pathlib.Path, repo_root: pathlib.Path) -> Page | None:
    text = path.read_text(encoding="utf-8")
    raw = extract_block(text, CATALOG_MARKER, CATALOG_END)
    content = extract_content(text)
    if raw is None:
        if content is not None:
            raise ValueError(f"{path}: content block without catalogue metadata")
        return None
    if content is None:
        raise ValueError(f"{path}: catalogue metadata without bounded content")
    try:
        data = tomllib.loads(raw)
    except tomllib.TOMLDecodeError as error:
        raise ValueError(f"{path}: invalid catalogue TOML: {error}") from error
    if set(data) - {"version", "section", "slug", "definitions", "theorems"}:
        unknown = sorted(set(data) - {"version", "section", "slug", "definitions", "theorems"})
        raise ValueError(f"{path}: unknown catalogue keys: {', '.join(unknown)}")
    if data.get("version") != 1:
        raise ValueError(f"{path}: catalogue version must be 1")
    section = data.get("section")
    slug = data.get("slug")
    if section not in SECTIONS:
        raise ValueError(f"{path}: invalid catalogue section {section!r}")
    if not isinstance(slug, str) or not SLUG_RE.fullmatch(slug):
        raise ValueError(f"{path}: invalid catalogue slug {slug!r}")
    definitions = tuple(validate_records(data.get("definitions", []), "definitions", path))
    theorems = tuple(validate_records(data.get("theorems", []), "theorems", path))
    if not definitions and not theorems:
        raise ValueError(f"{path}: catalogue must select a definition or theorem")
    validate_content(content, path)
    return Page(path, section, slug, definitions, theorems, content)


def validate_records(value: Any, label: str, path: pathlib.Path) -> list[dict[str, str]]:
    if not isinstance(value, list):
        raise ValueError(f"{path}: {label} must be an array of tables")
    records: list[dict[str, str]] = []
    for record in value:
        if not isinstance(record, dict) or set(record) - {"name", "module"}:
            raise ValueError(f"{path}: invalid {label} record keys")
        name = record.get("name")
        module = record.get("module")
        if not isinstance(name, str) or not NAME_RE.fullmatch(name):
            raise ValueError(f"{path}: {label} names must be fully qualified Lean names")
        if module is not None and (not isinstance(module, str) or not NAME_RE.fullmatch(module)):
            raise ValueError(f"{path}: invalid physical module for {name}")
        records.append({"name": name, **({"module": module} if module else {})})
    names = [record["name"] for record in records]
    if len(names) != len(set(names)):
        raise ValueError(f"{path}: duplicate {label} declaration")
    return records


def load_pages(repo_root: pathlib.Path) -> list[Page]:
    pages = [
        page
        for path in sorted((repo_root / "RealRooted" / "Challenges").rglob("*.lean"))
        if (page := parse_page(path, repo_root)) is not None
    ]
    slugs = [page.slug for page in pages]
    if len(slugs) != len(set(slugs)):
        raise ValueError("duplicate catalogue slug")
    if not pages:
        raise ValueError("no opted-in challenge catalogue pages found")
    return pages


def resolve_records(repo_root: pathlib.Path, pages: list[Page]) -> list[Record]:
    modules = local_module_paths(repo_root)
    imports = {module: imports_for(path) for module, path in modules.items()}
    records: list[Record] = []
    seen: set[str] = set()
    for page in pages:
        challenge_module = module_name_for_path(repo_root, page.path)
        closure = import_closure(challenge_module, imports)
        for expected_kind, entries in (
            ("definition", page.definitions),
            ("theorem", page.theorems),
        ):
            for entry in entries:
                name = entry["name"]
                if name in seen:
                    raise ValueError(f"duplicate selected declaration {name}")
                seen.add(name)
                module = entry.get("module", challenge_module)
                if module not in modules:
                    raise ValueError(f"{page.path}: unknown physical module {module}")
                if module not in closure:
                    raise ValueError(f"{page.path}: physical module {module} is not imported")
                locations = declaration_locations(modules[module])
                if name not in locations:
                    raise ValueError(f"{module}: selected declaration not found: {name}")
                source_kind, source_line, private = locations[name]
                actual_kind = "theorem" if source_kind in {"theorem", "lemma"} else "definition"
                if actual_kind != expected_kind:
                    raise ValueError(
                        f"{name}: expected {expected_kind}, source declares {source_kind}"
                    )
                if private:
                    raise ValueError(f"{name}: private declarations cannot be catalogued")
                if expected_kind == "definition" and re.search(
                    r"(?:Statement|Target|Route|Inputs|Backend)$", name
                ):
                    raise ValueError(f"{name}: statement/scaffold-like definitions are excluded")
                records.append(Record(name, expected_kind, module, modules[module], source_line))
    return records


def canonical_data(pages: list[Page]) -> dict[str, Any]:
    return {
        "pages": [
            {
                "section": page.section,
                "slug": page.slug,
                "definitions": list(page.definitions),
                "theorems": list(page.theorems),
                "content": page.content,
            }
            for page in pages
        ]
    }


def catalogue_digest(pages: list[Page]) -> str:
    encoded = json.dumps(
        canonical_data(pages), ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def revision(repo_root: pathlib.Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    )
    value = result.stdout.strip()
    if not SHA_RE.fullmatch(value):
        raise ValueError(f"unexpected git revision {value!r}")
    return value


def lean_name_literal(name: str) -> str:
    if not NAME_RE.fullmatch(name):
        raise ValueError(f"cannot emit unsafe Lean name {name}")
    return "`" + name


def generate_module(
    repo_root: pathlib.Path, module_path: pathlib.Path, records: list[Record]
) -> None:
    imports = sorted({module_name_for_path(repo_root, record.source_path) for record in records})
    names = ", ".join(lean_name_literal(record.name) for record in records)
    lines = [
        "import Lean",
        "import Lean.Elab.Command",
        *[f"import {module}" for module in imports],
        "",
        "open Lean Elab Command",
        "",
        "run_cmd do",
        "  let env ← getEnv",
        f"  let names : Array Name := #[{names}]",
        "  for name in names do",
        "    match env.find? name with",
        "    | none =>",
        "        liftIO <| IO.println (\"CATALOG_AUDIT_ERROR|missing|\" ++ name.toString)",
        "    | some info =>",
        "        let kind := match info with",
        "          | .thmInfo _ => \"theorem\"",
        "          | .defnInfo _ | .opaqueInfo _ => \"definition\"",
        "          | .axiomInfo _ => \"axiom\"",
        "          | .quotInfo _ | .inductInfo _ | .ctorInfo _ => \"other\"",
        "        let axioms ← liftCoreM <| Lean.collectAxioms name",
        "        let axiomText := String.intercalate \",\" (axioms.toList.map Name.toString)",
        "        liftIO <| IO.println (\"CATALOG_AUDIT|\" ++ name.toString ++ "
        "\"|\" ++ kind ++ \"|\" ++ axiomText)",
    ]
    module_path.parent.mkdir(parents=True, exist_ok=True)
    module_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_raw(raw_path: pathlib.Path) -> dict[str, tuple[str, frozenset[str]]]:
    observed: dict[str, tuple[str, frozenset[str]]] = {}
    for line in raw_path.read_text(encoding="utf-8").splitlines():
        if line.startswith("CATALOG_AUDIT_ERROR|"):
            raise ValueError(line)
        if not line.startswith("CATALOG_AUDIT|"):
            continue
        _, name, kind, axioms = line.split("|", 3)
        if name in observed:
            raise ValueError(f"duplicate Lean audit result for {name}")
        observed[name] = (kind, frozenset(filter(None, axioms.split(","))))
    return observed


def collect_report(repo_root: pathlib.Path, raw_path: pathlib.Path, report_path: pathlib.Path,
                   pages: list[Page], records: list[Record]) -> None:
    observed = parse_raw(raw_path)
    expected_names = [record.name for record in records]
    if set(observed) != set(expected_names):
        missing = sorted(set(expected_names) - set(observed))
        extra = sorted(set(observed) - set(expected_names))
        raise ValueError(f"audit result mismatch; missing={missing}, extra={extra}")
    declarations: list[dict[str, Any]] = []
    for record in records:
        actual_kind, axioms = observed[record.name]
        if actual_kind != record.expected_kind:
            raise ValueError(
                f"{record.name}: Lean environment kind {actual_kind!r}, "
                f"expected {record.expected_kind!r}"
            )
        unexpected = sorted(axioms - ALLOWED_AXIOMS)
        if unexpected:
            raise ValueError(f"{record.name}: disallowed axioms: {', '.join(unexpected)}")
        declarations.append(
            {
                "name": record.name,
                "expected_kind": record.expected_kind,
                "actual_kind": actual_kind,
                "source_path": record.source_path.relative_to(repo_root).as_posix(),
                "source_line": record.source_line,
                "axioms": sorted(axioms),
            }
        )
    toolchain_path = repo_root / "lean-toolchain"
    if not toolchain_path.is_file():
        raise ValueError(f"missing {toolchain_path}")
    report = {
        "schema_version": 1,
        "revision": revision(repo_root),
        "catalog_digest": catalogue_digest(pages),
        "lean_toolchain": toolchain_path.read_text(encoding="utf-8").strip(),
        "declarations": declarations,
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(
        json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=pathlib.Path, default=repo_root_from_args())
    parser.add_argument("--check", action="store_true", help="validate source metadata only")
    parser.add_argument("--generate", type=pathlib.Path, metavar="MODULE")
    parser.add_argument("--collect", type=pathlib.Path, metavar="RAW")
    parser.add_argument("--report", type=pathlib.Path, metavar="JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        repo_root = args.repo_root.resolve()
        pages = load_pages(repo_root)
        records = resolve_records(repo_root, pages)
        if args.check:
            print(f"ok: {len(pages)} catalogue page(s), {len(records)} selected declaration(s)")
        if args.generate:
            generate_module(repo_root, args.generate.resolve(), records)
            print(f"ok: generated Lean audit module {args.generate}")
        if args.collect:
            if args.report is None:
                raise ValueError("--collect requires --report")
            collect_report(repo_root, args.collect.resolve(), args.report.resolve(), pages, records)
            print(f"ok: wrote catalogue audit report {args.report}")
        if not (args.check or args.generate or args.collect):
            print(f"ok: source metadata valid ({len(pages)} pages, {len(records)} declarations)")
        return 0
    except (OSError, subprocess.CalledProcessError, ValueError, tomllib.TOMLDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
