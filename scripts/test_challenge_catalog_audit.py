#!/usr/bin/env python3
"""Focused source-only tests for the challenge catalogue audit driver."""

from __future__ import annotations

import pathlib
import tempfile
import unittest

import audit_challenge_catalog as audit


class ChallengeCatalogAuditTests(unittest.TestCase):
    def test_comment_and_string_names_are_not_declarations(self) -> None:
        source = """\
/- theorem Fake : True := by sorry -/
def real : Prop := True
def quoted : String := "theorem AlsoFake"
"""
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "Fixture.lean"
            path.write_text(source, encoding="utf-8")
            locations = audit.declaration_locations(path)
        self.assertIn("real", locations)
        self.assertIn("quoted", locations)
        self.assertNotIn("Fake", locations)
        self.assertNotIn("AlsoFake", locations)

    def test_catalogue_digest_is_deterministic(self) -> None:
        page = audit.Page(
            pathlib.Path("Fixture.lean"),
            "concepts",
            "fixture",
            ({"name": "RealRooted.Fixture"},),
            (),
            "# Fixture\n\n## References\n\nReference.\n",
        )
        self.assertEqual(audit.catalogue_digest([page]), audit.catalogue_digest([page]))

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

    def test_scaffold_definition_is_excluded_by_policy(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "RealRooted" / "Challenges").mkdir(parents=True)
            (root / "RealRooted.lean").write_text("", encoding="utf-8")
            (root / "RealRooted" / "Challenges" / "Fixture.lean").write_text(
                "import RealRooted.Basic.ProperPosition\n\n/-!\n"
                "<!-- realrooted-catalog\nversion = 1\nsection = \"concepts\"\nslug = \"fixture\"\n"
                "[[definitions]]\nname = \"RealRooted.FooTarget\"\n-->\n"
                "<!-- realrooted-catalog-content -->\n# Fixture\n\n## References\n\nRef.\n"
                "<!-- /realrooted-catalog-content -->\n-/\n",
                encoding="utf-8",
            )
            with self.assertRaises(ValueError):
                audit.resolve_records(root, audit.load_pages(root))


if __name__ == "__main__":
    unittest.main()
