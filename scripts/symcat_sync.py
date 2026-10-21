#!/usr/bin/env python3
"""Refresh the catalog's symmetricfunctions.com label and bibliography snapshots."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any
from urllib.parse import urljoin, urlsplit
from urllib.request import urlopen

sys.dont_write_bytecode = True

from challenge_catalog import CatalogError, extract_sf_labels, load_catalog


LIVE_ROOT = "https://www.symmetricfunctions.com/"
CSL_FIELDS = (
    "author",
    "title",
    "container-title",
    "volume",
    "issue",
    "page",
    "issued",
    "DOI",
    "URL",
    "type",
)


def _source_at(root: str, filename: str) -> str:
    parsed = urlsplit(root)
    if parsed.scheme in {"http", "https"}:
        return urljoin(root.rstrip("/") + "/", filename)
    return str(pathlib.Path(root) / filename)


def _read_json(source: str) -> Any:
    parsed = urlsplit(source)
    try:
        if parsed.scheme in {"http", "https"}:
            with urlopen(source, timeout=60) as response:
                return json.load(response)
        return json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise CatalogError(f"cannot read {source}: {error}") from error


def build_snapshots(
    repo_root: pathlib.Path,
    labels_upstream: Any,
    bibliography_upstream: Any,
    keep: tuple[str, ...] = (),
) -> tuple[dict[str, str], dict[str, Any]]:
    """Select and normalize the upstream data needed by the current catalog."""
    if not isinstance(labels_upstream, dict):
        raise CatalogError("upstream site-labels.json must contain an object")
    if (
        not isinstance(bibliography_upstream, dict)
        or bibliography_upstream.get("schema_version") != 1
        or not isinstance(bibliography_upstream.get("entries"), dict)
    ):
        raise CatalogError("upstream bibliography.json has an invalid schema")

    pages = load_catalog(repo_root)
    used_labels = sorted(
        {
            label
            for page in pages
            for label in (
                *(item.symcat for item in page.items if item.symcat),
                *extract_sf_labels(page.content),
            )
        }
    )
    cited_keys = sorted({citation.key for page in pages for citation in page.citations} | set(keep))

    missing_labels = [label for label in used_labels if label not in labels_upstream]
    if missing_labels:
        raise CatalogError("upstream labels missing: " + ", ".join(missing_labels))
    upstream_entries = bibliography_upstream["entries"]
    missing_keys = [key for key in cited_keys if key not in upstream_entries]
    if missing_keys:
        raise CatalogError("upstream bibliography missing: " + ", ".join(missing_keys))

    labels: dict[str, str] = {}
    for label in sorted(labels_upstream):
        record = labels_upstream[label]
        href = record.get("href") if isinstance(record, dict) else None
        if not isinstance(label, str) or not isinstance(href, str) or not href:
            raise CatalogError(f"invalid upstream label record {label!r}")
        labels[label] = href

    selected: dict[str, dict[str, Any]] = {}
    for key in cited_keys:
        record = upstream_entries[key]
        if not isinstance(record, dict):
            raise CatalogError(f"invalid upstream bibliography entry {key!r}")
        label = record.get("label")
        csl = record.get("csl")
        bibtex = record.get("bibtex")
        if (
            not isinstance(label, str)
            or not label
            or not isinstance(csl, dict)
            or not isinstance(bibtex, str)
        ):
            raise CatalogError(f"invalid upstream bibliography entry {key!r}")
        selected[key] = {
            "label": label,
            "csl": {field: csl[field] for field in CSL_FIELDS if field in csl},
            "bibtex": bibtex.strip() + "\n",
        }
    return labels, {"schema_version": 1, "entries": selected}


def write_snapshots(
    repo_root: pathlib.Path, labels: dict[str, str], bibliography: dict[str, Any]
) -> None:
    target = repo_root / "website" / "symcat"
    target.mkdir(parents=True, exist_ok=True)
    (target / "labels.json").write_text(
        json.dumps(labels, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    (target / "bibliography.json").write_text(
        json.dumps(bibliography, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "source",
        nargs="?",
        default=LIVE_ROOT,
        help="directory or URL containing site-labels.json and bibliography.json",
    )
    parser.add_argument(
        "--repo-root",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--labels-source", help="override the labels JSON path or URL")
    parser.add_argument("--bibliography-source", help="override the bibliography JSON path or URL")
    parser.add_argument("--keep", action="append", default=[], metavar="KEY")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    labels_source = args.labels_source or _source_at(args.source, "site-labels.json")
    bibliography_source = args.bibliography_source or _source_at(
        args.source, "bibliography.json"
    )
    try:
        labels, bibliography = build_snapshots(
            args.repo_root.resolve(),
            _read_json(labels_source),
            _read_json(bibliography_source),
            tuple(args.keep),
        )
        write_snapshots(args.repo_root.resolve(), labels, bibliography)
        print(
            f"ok: wrote {len(labels)} labels and {len(bibliography['entries'])} bibliography entries"
        )
        return 0
    except CatalogError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
