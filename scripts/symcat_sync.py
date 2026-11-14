#!/usr/bin/env python3
"""Refresh the catalog's symmetricfunctions.com label and bibliography snapshots."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from http.client import HTTPException
from typing import Any
from urllib.parse import urljoin, urlsplit
from urllib.request import urlopen

sys.dont_write_bytecode = True

from challenge_catalog import CatalogError, load_catalog, load_symcat_snapshots


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
    except (OSError, ValueError, HTTPException) as error:
        raise CatalogError(f"cannot read {source}: {error}") from error


def build_snapshots(
    repo_root: pathlib.Path,
    labels_upstream: Any,
    bibliography_upstream: Any,
    keep: tuple[str, ...] = (),
    *,
    snapshots: tuple[dict[str, str], dict[str, dict[str, Any]]] | None = None,
) -> tuple[dict[str, str], dict[str, Any]]:
    """Merge live records over snapshots, retaining records removed upstream."""
    if not isinstance(labels_upstream, dict):
        raise CatalogError("upstream site-labels.json must contain an object")
    if (
        not isinstance(bibliography_upstream, dict)
        or bibliography_upstream.get("schema_version") != 1
        or not isinstance(bibliography_upstream.get("entries"), dict)
    ):
        raise CatalogError("upstream bibliography.json has an invalid schema")

    old_labels, old_entries = snapshots if snapshots is not None else ({}, {})
    upstream_entries = bibliography_upstream["entries"]
    pages = load_catalog(repo_root)
    used_labels = sorted({label for page in pages for label in page.symcat_labels})
    cited_keys = sorted(
        {citation.key for page in pages for citation in page.citations}
        | set(keep) | set(old_entries)
    )

    labels = dict(old_labels)
    for label in sorted(labels_upstream):
        record = labels_upstream[label]
        href = record.get("href") if isinstance(record, dict) else None
        if not isinstance(label, str) or not isinstance(href, str) or not href:
            raise CatalogError(f"invalid upstream label record {label!r}")
        labels[label] = href

    missing_labels = [label for label in used_labels if label not in labels]
    if missing_labels:
        raise CatalogError(
            "SymCat labels missing from live export and snapshot: " + ", ".join(missing_labels)
        )
    missing_keys = [
        key for key in cited_keys if key not in upstream_entries and key not in old_entries
    ]
    if missing_keys:
        raise CatalogError(
            "SymCat bibliography missing from live export and snapshot: " + ", ".join(missing_keys)
        )

    selected: dict[str, dict[str, Any]] = {}
    for key in cited_keys:
        if key not in upstream_entries:
            selected[key] = old_entries[key]
            continue
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
    for kind, removed in (
        ("labels", sorted(set(old_labels) - set(labels_upstream))),
        ("bibliography keys", sorted(set(old_entries) - set(upstream_entries))),
    ):
        if removed:
            print(
                f"warning: SymCat {kind} removed upstream; retaining snapshot records: "
                + ", ".join(removed),
                file=sys.stderr,
            )
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
    actions = parser.add_mutually_exclusive_group()
    actions.add_argument(
        "--check", action="store_true",
        help="report snapshot changes without writing or failing on staleness; tolerate offline access",
    )
    actions.add_argument(
        "--fallback-to-snapshot", action="store_true",
        help="leave snapshots unchanged if the live exports cannot be read (site builds still validate references)",
    )
    parser.add_argument("--keep", action="append", default=[], metavar="KEY")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    labels_source = args.labels_source or _source_at(args.source, "site-labels.json")
    bibliography_source = args.bibliography_source or _source_at(
        args.source, "bibliography.json"
    )
    try:
        root = args.repo_root.resolve()
        snapshot_dir = root / "website" / "symcat"
        snapshots = (
            load_symcat_snapshots(root)
            if any(
                (snapshot_dir / name).exists() for name in ("labels.json", "bibliography.json")
            )
            else None
        )
        try:
            labels_live = _read_json(labels_source)
            bibliography_live = _read_json(bibliography_source)
        except CatalogError as error:
            if args.check:
                print(f"warning: SymCat snapshot freshness unavailable: {error}", file=sys.stderr)
                return 0
            if args.fallback_to_snapshot and snapshots is not None:
                print(
                    f"warning: SymCat refresh unavailable: {error}; "
                    "falling back to committed snapshots (unchanged); "
                    "the site build will still validate all keys and labels",
                    file=sys.stderr,
                )
                return 0
            raise
        labels, bibliography = build_snapshots(
            root,
            labels_live,
            bibliography_live,
            tuple(args.keep),
            snapshots=snapshots,
        )
        if args.check:
            old_labels, old_entries = snapshots if snapshots is not None else ({}, {})
            changes = []
            for kind, old, new in (
                ("labels", old_labels, labels),
                ("bibliography entries", old_entries, bibliography["entries"]),
            ):
                added = len(set(new) - set(old))
                updated = sum(old[key] != new[key] for key in set(old) & set(new))
                changes.append(f"{kind}: {added} added, {updated} updated")
            if labels != old_labels or bibliography["entries"] != old_entries:
                print("warning: SymCat snapshots are stale (" + "; ".join(changes) + ")")
                print("refresh: python3 scripts/symcat_sync.py")
            else:
                print("ok: SymCat snapshots are current")
            return 0
        write_snapshots(root, labels, bibliography)
        print(
            f"ok: wrote {len(labels)} labels and {len(bibliography['entries'])} bibliography entries"
        )
        return 0
    except CatalogError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
