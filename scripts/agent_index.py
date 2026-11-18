#!/usr/bin/env python3
"""Build the source-only, catalog-centred RealRooted navigation index."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import re
import sqlite3
import sys
import tempfile
import time
import unicodedata
from typing import Any

sys.dont_write_bytecode = True

import challenge_catalog as catalog
import lemma_index

ROOT = Path(__file__).resolve().parent.parent
SCHEMA_VERSION = 1
LEAN_NAME = re.compile(r"\b(?:RealRooted|LinearRecurrence)\.[\w'.]+")
STOP_WORDS = set("a an and are as be by every f for g has in is of or the to with".split())


def tokens(text: str) -> list[str]:
    """Fold accents, split Lean identifiers, and normalize a few mathematical synonyms."""
    text = re.sub(r"([a-z])([A-Z])", r"\1 \2", text)
    text = unicodedata.normalize("NFKD", text)
    text = "".join(c for c in text if not unicodedata.combining(c)).lower()
    text = re.sub(r"real[ -]?root(?:ed|s)?|\bsplits\b", " realrooted ", text)
    text = re.sub(r"strict[ _]?interl\b|\binterl\b|\binterlaces\b", " interlacing ", text)
    text = re.sub(r"\bpf\b|polya[ -]frequency", " polyafrequency ", text)
    words = re.findall(r"[^\W_]+", text)
    return [w[:-1] if len(w) > 4 and w.endswith("s") else w
            for w in words if w not in STOP_WORDS]


def source_files(root: Path, polytool: bool = False) -> list[Path]:
    """List only indexed inputs, including untracked Lean/Rust sources."""
    if polytool:
        return sorted((root / "src").rglob("*.rs"))
    paths = list((root / "RealRooted").rglob("*.lean"))
    paths += list((root / "website").rglob("*"))
    paths += [root / "lean-toolchain"]
    paths += [root / "scripts" / name for name in (
        "challenge_catalog.py", "lemma_index.py", "agent_index.py", "rr_nav.py",
        "tactic_routes.json",
    )]
    paths += list((root / "scripts/_stdlib_tomllib").glob("*.py"))
    return sorted(p for p in paths if p.is_file() and not p.is_symlink())


def source_stamp(root: Path, polytool: bool = False) -> dict[str, str]:
    """Use HEAD and a content fingerprint; mtimes alone cannot detect dirty changes."""
    digest = hashlib.sha256()
    for path in source_files(root, polytool):
        if path.is_symlink():
            raise ValueError(f"indexed input is a symlink: {path}")
        digest.update(path.relative_to(root).as_posix().encode())
        digest.update(b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    return {"revision": catalog.revision_at(root), "fingerprint": digest.hexdigest()}


def source_state(root: Path, polytool: Path | None) -> dict[str, Any]:
    """Identify the checkouts as well as their indexed content."""
    return {
        "repo": {"path": str(root), **source_stamp(root)},
        "polytool": {"path": str(polytool), **source_stamp(polytool, True)}
        if polytool else None,
    }


def scrape_polytool(
    root: Path | None, names: set[str], modules: set[str] | None = None,
) -> list[dict[str, Any]]:
    """Read registry rows and source citations without indexing Rust symbols or OEIS data."""
    if root is None:
        return []
    parent = root / "src/recurrence/lift/parent_theorems"
    registry = parent / "registry.rs"
    table = registry.read_text(encoding="utf-8") if registry.exists() else ""
    rows = re.findall(r'^\s*\w+,\s*(\w+),\s*"([\w_]+)",\s*\n\s*"([^"]+)"',
                      table, re.M)
    wire_by_file = {}
    directory_routes = {}
    for module, wire, summary in rows:
        path = parent / f"{module}.rs"
        if not path.exists():
            path = parent / module / "mod.rs"
            directory_routes[wire] = "polytool/" + path.parent.relative_to(root).as_posix() + "/"
        wire_by_file[path] = (wire, summary)
    namespaces = {".".join(n.split(".")[:i]) for n in names
                  for i in range(1, len(n.split(".")))}
    result = []
    for path in source_files(root, True):
        text = path.read_text(encoding="utf-8")
        relative = "polytool/" + path.relative_to(root).as_posix()
        citations = []
        for match in LEAN_NAME.finditer(text):
            name = match.group().rstrip(".")
            if text[match.end():].startswith("{name}"):
                continue  # Expanded below, rather than treating a format prefix as a theorem.
            citations.append({
                "name": name, "source_line": text.count("\n", 0, match.start()) + 1,
                "rust_path": relative,
                "reference_kind": "module" if name in (modules or set()) else (
                    "namespace" if name in namespaces else "declaration"),
                "unresolved_at_head": name not in names and name not in namespaces
                and name not in (modules or set()),
            })
        dynamic = re.compile(
            r'\[(?P<items>\s*(?:"\w+",?\s*)+)\]\s*'
            r'\.map\(\|name\|\s*format!\("(?P<prefix>RealRooted\.[\w.]+)\{name\}"\)\)',
        )
        for match in dynamic.finditer(text):
            for item in re.finditer(r'"(\w+)"', match.group("items")):
                name = match.group("prefix") + item.group(1)
                citations.append({
                    "name": name, "source_line": text.count(
                        "\n", 0, match.start("items") + item.start()) + 1,
                    "rust_path": relative,
                    "reference_kind": "declaration", "unresolved_at_head": name not in names,
                })
        route_names = re.findall(
            r"(?:row\s+)?route\s+[`\"']?(\w+)", text, re.I,
        ) if "RealRooted" in text else []
        reference = re.search(r'\bREFERENCE\s*:\s*&str\s*=\s*"((?:[^"\\]|\\.)*)"',
                              text, re.S)
        if not citations and path not in wire_by_file:
            continue
        wire, summary = wire_by_file.get(path, (relative, "Lean citations"))
        result.append({
            "name": wire, "summary": summary, "rust_path": relative,
            "source_line": text.count("\n", 0, reference.start()) + 1 if reference else 1,
            "reference": re.sub(r"\\\s*", " ", reference.group(1)) if reference else "",
            "lean_names": sorted({c["name"] for c in citations
                                  if c["reference_kind"] == "declaration"}),
            "citations": citations, "tactic_routes": sorted(set(route_names)),
        })
    # Rust permits route modules to be directories. Include their nested theorem citations
    # in the registry route while retaining the individual citation files for navigation.
    for route in result:
        prefix = directory_routes.get(route["name"])
        if prefix:
            nested = [r for r in result if r is not route and r["rust_path"].startswith(prefix)]
            route["citations"] += [c for r in nested for c in r["citations"]]
            route["lean_names"] = sorted(set(route["lean_names"]) | {
                name for r in nested for name in r["lean_names"]
            })
            route["tactic_routes"] = sorted(set(route["tactic_routes"]) | {
                name for r in nested for name in r["tactic_routes"]
            })
    return result


def build_index(root: Path, polytool: Path | None = None) -> dict[str, Any]:
    """Reuse catalog resolution/rendering and the source theorem index; never invoke Lean."""
    started = time.perf_counter()
    root = root.resolve()
    polytool = polytool.resolve() if polytool else None
    state = source_state(root, polytool)
    # The catalog's caches otherwise retain old source strings in a long-lived server.
    for value in vars(catalog).values():
        if hasattr(value, "cache_clear"):
            value.cache_clear()
    pages = catalog.load_catalog(root)
    resolved = catalog.validate_sources(root, pages)
    revision = state["repo"]["revision"]
    manifest = json.loads(catalog.render_site(root, pages, resolved, revision)[
        "catalog-manifest.json"
    ])
    declarations = {}
    for decl in lemma_index.collect(root):
        declarations[decl["name"]] = {
            "name": decl["name"], "kind": "theorem", "module": decl["module"],
            "statement": decl["stmt"], "docstring": decl["doc"],
            "conclusion_key": decl["key"], "uses": decl["uses"],
            "source_path": decl["path"].relative_to(root).as_posix(),
            "source_line": decl["source_line"],
        }
    # The existing theorem index intentionally omits definitions. Reuse the catalog's
    # declaration scanner for those and for names missed by its lightweight theorem regex.
    for path in source_files(root):
        if path.suffix != ".lean":
            continue
        lines = catalog.strip_comments_and_strings(path.read_text(encoding="utf-8")).splitlines()
        raw_lines = path.read_text(encoding="utf-8").splitlines()
        for name, decl in catalog.source_declarations(root, path, include_source=False).items():
            if name not in declarations:
                statement = lemma_index.statement_of(lines, decl.source_line - 1)
                declarations[name] = {
                    "name": name, "kind": decl.actual_kind,
                    "module": decl.source_path.removesuffix(".lean").replace("/", "."),
                    "statement": statement, "source_path": decl.source_path,
                    "source_line": decl.source_line,
                    "conclusion_key": lemma_index.key_of(
                        lemma_index.conclusion_of(statement)),
                    "docstring": lemma_index.doc_before(raw_lines, decl.source_line - 1),
                    "uses": 0,
                }
        namespaces: list[str] = []
        for i, line in enumerate(lines):
            namespace = catalog.NAMESPACE_RE.match(line)
            ending = catalog.END_NAMESPACE_RE.match(line)
            if namespace:
                namespaces.extend(namespace.group(1).split("."))
            elif ending:
                tail = ending.group(1).split(".")
                if namespaces[-len(tail):] == tail:
                    del namespaces[-len(tail):]
            alias = re.match(r"^\s*(?:protected\s+)?alias\s+([\w'.]+)\s*:=", line)
            if alias:
                raw = alias.group(1)
                name = raw.removeprefix("_root_.") if raw.startswith("_root_.") else ".".join(
                    namespaces + [raw])
                declarations.setdefault(name, {
                    "name": name, "kind": "alias", "module": lemma_index.module_of(path, root),
                    "statement": "\n".join(raw_lines[i:i + 2]),
                    "source_path": path.relative_to(root).as_posix(), "source_line": i + 1,
                    "conclusion_key": "other", "uses": 0, "docstring": "",
                })
    by_slug = {p.slug: p for p in pages}
    for page in manifest["pages"]:
        source_page = by_slug[page["url"].strip("/").split("/")[-1]]
        page["slug"] = source_page.slug
        page["url"] = catalog.SITE_ORIGIN + page["url"]
        page["source_line"] = 1
        for item in page["declarations"]:
            decl = resolved[item["name"]]
            declarations[item["name"]].update({
                "statement": decl.source_code, "page": source_page.slug,
                "label": page["labels"].get(item["name"], ""),
                "headline": item["name"] in page["headlines"],
                "objects": item["objects"], "property": item["property"],
                "tags": item["tags"],
            })
    tactics = json.loads((root / "scripts/tactic_routes.json").read_text())["routes"]
    names = set(declarations)
    for route in tactics:
        route["citations"] = [
            {"name": name, "unresolved_at_head": name not in names}
            for name in route["theorems"]
        ]
        route["source_path"] = "scripts/tactic_routes.json"
        route["source_line"] = next(
            i for i, line in enumerate((root / route["source_path"]).read_text().splitlines(), 1)
            if f'"name": "{route["name"]}"' in line
        )
    poly_routes = scrape_polytool(polytool, names, {d["module"] for d in declarations.values()})
    _, bibliography = catalog.load_symcat_snapshots(root)
    tactic_names = {r["name"] for r in tactics}
    for route in poly_routes:
        linked = {r["name"] for r in tactics
                  if set(r["theorems"]) & set(route["lean_names"])}
        route["tactic_routes"] = sorted(linked | (set(route["tactic_routes"]) & tactic_names))
    if source_state(root, polytool) != state:
        raise RuntimeError("indexed inputs changed during build; retry the query")
    return {
        "schema_version": SCHEMA_VERSION, "revision": revision, "sources": state,
        "catalog_digest": manifest["catalog_digest"],
        "references": {key: bibliography[key] for key in sorted({
            key for page in manifest["pages"] for key in page["references"]
        })},
        "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
        "pages": manifest["pages"], "families": manifest["families_index"]["entries"],
        "declarations": list(declarations.values()), "tactic_routes": tactics,
        "polytool_routes": poly_routes,
        "build_seconds": round(time.perf_counter() - started, 3),
    }


def write_index(index: dict[str, Any], output: Path) -> None:
    """Replace a generated index atomically without creating symlinks."""
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=output.parent,
                                         prefix=output.name + ".", delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(index, stream, ensure_ascii=False, separators=(",", ":"))
            stream.write("\n")
        temporary.replace(output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


class Search:
    """Weighted token BM25 using FTS5, with an equivalent pure-Python fallback."""

    def __init__(self, records: list[dict[str, Any]], force_python: bool = False):
        self.records = records
        self.texts = []
        for r in records:
            title = " ".join(str(r.get(k, "")) for k in ("label", "title", "family"))
            name = r.get("name", "")
            body = " ".join(str(r.get(k, "")) for k in (
                "statement", "summary", "docstring", "objects", "requires", "conclusion",
            ))
            self.texts.append((" ".join(tokens(title)), " ".join(tokens(name)),
                               " ".join(tokens(body))))
        self.db = sqlite3.connect(":memory:")
        self.backend = "python-bm25"
        if not force_python:
            try:
                self.db.execute("CREATE VIRTUAL TABLE search USING fts5(label, name, body)")
                self.db.executemany("INSERT INTO search VALUES (?, ?, ?)", self.texts)
                self.backend = "sqlite-fts5"
            except sqlite3.OperationalError:
                pass
        self.counts: list[Counter] = []  # Populated lazily for the fallback.

    def ranked(self, query: str) -> list[tuple[int, float]]:
        """Return matching row indices in score order (OR search tolerates natural prose)."""
        words = sorted(set(tokens(query)))
        if not words:
            return [(i, 0.0) for i in range(len(self.records))]
        if self.backend == "sqlite-fts5":
            expression = " OR ".join('"' + w + '"' for w in words)
            rows = self.db.execute(
                "SELECT rowid, bm25(search, 5, 3, 1) AS rank FROM search "
                "WHERE search MATCH ? ORDER BY rank, rowid", (expression,),
            )
            return [(row - 1, -score) for row, score in rows]
        if not self.counts:
            self.counts = [Counter(((a + " ") * 5 + (b + " ") * 3 + c).split())
                           for a, b, c in self.texts]
        lengths = [sum(c.values()) for c in self.counts]
        average = sum(lengths) / max(1, len(lengths)) or 1
        frequencies = {w: sum(w in c for c in self.counts) for w in words}
        scored = []
        for i, counts in enumerate(self.counts):
            score = 0.0
            for word in words:
                frequency = counts[word]
                idf = math.log(1 + (len(lengths) - frequencies[word] + .5)
                               / (frequencies[word] + .5))
                score += idf * frequency * 2.2 / (
                    frequency + 1.2 * (.25 + .75 * lengths[i] / average))
            if score:
                scored.append((i, score))
        return sorted(scored, key=lambda pair: (-pair[1], pair[0]))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--polytool", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = time.perf_counter()
    index = build_index(args.repo, args.polytool)
    write_index(index, args.output)
    print(json.dumps({"bytes": args.output.stat().st_size,
                      "seconds": round(time.perf_counter() - started, 3),
                      "pages": len(index["pages"]),
                      "declarations": len(index["declarations"])}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
