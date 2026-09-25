#!/usr/bin/env python3
"""Validate or render the curated RealRooted challenge catalogue."""

from __future__ import annotations

import argparse
import pathlib
import sys

sys.dont_write_bytecode = True

from challenge_catalog import (
    CatalogError,
    load_catalogue,
    render_site,
    revision_at,
    validate_audit_report,
    validate_sources,
    write_site,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parents[1],
        help="repository root (defaults to this script's parent)",
    )
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--check", action="store_true", help="validate sources without writing output")
    actions.add_argument("--output", type=pathlib.Path, help="directory for generated static files")
    parser.add_argument(
        "--audit-report",
        type=pathlib.Path,
        help="post-Lean audit report required for publishable output",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.repo_root.resolve()
    try:
        pages = load_catalogue(root)
        resolved = validate_sources(root, pages)
        revision = revision_at(root)
        if args.audit_report is not None:
            validate_audit_report(args.audit_report, pages, resolved, revision)
        if args.check:
            print(f"ok: validated {len(pages)} curated catalogue pages")
            return 0
        files = render_site(root, pages, resolved, revision)
        write_site(args.output.resolve(), files)
        print(f"ok: wrote {len(files)} catalogue files to {args.output}")
        return 0
    except CatalogError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
