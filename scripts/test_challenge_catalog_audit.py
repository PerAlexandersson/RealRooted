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
        self.assertEqual(len(pages), 18)
        self.assertEqual(len(audit.resolve_records(root, pages)), 72)

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

    def test_generated_kind_match_covers_recursor_constants(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            path = root / "Audit.lean"
            records = [
                audit.Record(
                    "RealRooted.Challenges.Sample.a_representative_public_theorem",
                    "theorem",
                    "RealRooted.Challenges.Sample",
                    root / "RealRooted/Challenges/Sample.lean",
                    1,
                )
            ]
            audit.generate_module(root, path, records)
            source = path.read_text(encoding="utf-8")
            self.assertIn(".recInfo _ => \"other\"", source)
            self.assertIn(
                '`RealRooted.Challenges.Sample\n'
                '      "a_representative_public_theorem",',
                source,
            )
            self.assertLessEqual(max(map(len, source.splitlines())), 100)

if __name__ == "__main__":
    unittest.main()
