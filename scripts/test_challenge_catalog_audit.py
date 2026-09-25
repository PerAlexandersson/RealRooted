#!/usr/bin/env python3
"""Focused source-only tests for the challenge catalogue audit driver."""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import audit_challenge_catalog as audit
import challenge_catalog


class ChallengeCatalogAuditTests(unittest.TestCase):
    def test_audit_reuses_canonical_loader_and_digest(self) -> None:
        root = pathlib.Path(__file__).resolve().parents[1]
        self.assertIs(audit.load_pages, challenge_catalog.load_catalogue)
        self.assertIs(audit.catalogue_digest, challenge_catalog.catalog_digest)
        pages = audit.load_pages(root)
        self.assertEqual(audit.catalogue_digest(pages), challenge_catalog.catalog_digest(pages))
        self.assertEqual(len(audit.resolve_records(root, pages)), 23)

    def test_raw_audit_parser_rejects_duplicate_results(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "audit.raw"
            path.write_text(
                "CATALOG_AUDIT|RealRooted.foo|theorem|propext\n"
                "CATALOG_AUDIT|RealRooted.foo|theorem|propext\n",
                encoding="utf-8",
            )
            with self.assertRaises(ValueError):
                audit.parse_raw(path)

if __name__ == "__main__":
    unittest.main()
