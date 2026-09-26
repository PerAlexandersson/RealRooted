#!/usr/bin/env python3
"""Prepare and collect the Lean audit for the curated challenge catalogue.

Catalogue parsing, source validation, canonicalization, and digest computation
are owned by :mod:`challenge_catalog`.  This driver only prepares the temporary
Lean environment query and converts its marker output into the frozen audit
report.

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
import json
import pathlib
import re
import sys
from dataclasses import dataclass
from typing import Any

import challenge_catalog


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$")


@dataclass(frozen=True)
class Record:
    name: str
    expected_kind: str
    module: str
    source_path: pathlib.Path
    source_line: int


# These aliases are deliberately direct: the generator owns the canonical
# catalogue loader and digest schema used by both source and publishable paths.
load_pages = challenge_catalog.load_catalogue
catalogue_digest = challenge_catalog.catalog_digest


def repo_root_from_args() -> pathlib.Path:
    return pathlib.Path(__file__).resolve().parents[1]


def resolve_records(
    repo_root: pathlib.Path, pages: tuple[challenge_catalog.CatalogPage, ...]
) -> list[Record]:
    resolved = challenge_catalog.validate_sources(repo_root, pages)
    records: list[Record] = []
    for page in pages:
        for item in page.items:
            source = resolved[item.name]
            source_path = repo_root / source.source_path
            module = item.module or page.source_path.removesuffix(".lean").replace("/", ".")
            records.append(
                Record(
                    name=item.name,
                    expected_kind=item.expected_kind,
                    module=module,
                    source_path=source_path,
                    source_line=source.source_line,
                )
            )
    return records


def lean_name_literal(name: str) -> str:
    if not NAME_RE.fullmatch(name):
        raise ValueError(f"cannot emit unsafe Lean name {name}")
    return "`" + name


def generate_module(
    repo_root: pathlib.Path, module_path: pathlib.Path, records: list[Record]
) -> None:
    imports = sorted(
        {
            challenge_catalog.module_name_for_path(repo_root, record.source_path)
            for record in records
        }
    )
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
        "          | .defnInfo _ | .opaqueInfo _ | .inductInfo _ => \"definition\"",
        "          | .axiomInfo _ => \"axiom\"",
        "          | .quotInfo _ | .ctorInfo _ => \"other\"",
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


def collect_report(
    repo_root: pathlib.Path,
    raw_path: pathlib.Path,
    report_path: pathlib.Path,
    pages: tuple[challenge_catalog.CatalogPage, ...],
    records: list[Record],
) -> None:
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
        "revision": challenge_catalog.revision_at(repo_root),
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
    except (OSError, ValueError, challenge_catalog.CatalogError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
