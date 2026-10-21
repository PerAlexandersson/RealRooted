#!/usr/bin/env python3
"""Unit tests for the symmetricfunctions.com snapshot synchronizer."""

from __future__ import annotations

import json
import pathlib
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

from challenge_catalog import CatalogError
from symcat_sync import build_snapshots, write_snapshots


SOURCE = '''/-!
<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "sample"
formalized = "2026-01-02"
references = ["Cited"]

[[theorems]]
name = "RealRooted.Challenges.Sample.proven"
symcat = "statement"
-->

<!-- realrooted-catalog-content -->
# Sample

See [context](sf:context) and [@Inline].

## References
<!-- /realrooted-catalog-content -->
-/
namespace RealRooted.Challenges.Sample
theorem proven : True := by trivial
end RealRooted.Challenges.Sample
'''


def bibliography_entry(key: str) -> dict:
    return {
        "label": key[:3],
        "csl": {
            "id": key,
            "author": [{"family": "Example", "given": "A."}],
            "title": f"{key} title",
            "issued": {"date-parts": [[2026]]},
            "DOI": f"10.1000/{key}",
            "unused": "drop me",
        },
        "bibtex": f"@misc{{{key}}}\n\n",
    }


class SymcatSyncTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tempdir.name)
        path = self.root / "RealRooted" / "Challenges" / "Sample.lean"
        path.parent.mkdir(parents=True)
        path.write_text(SOURCE, encoding="utf-8")

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def upstream(self) -> tuple[dict, dict]:
        labels = {
            "unused": {"href": "unused.htm#unused", "page": "unused", "title": "Unused"},
            "context": {"href": "context.htm#context", "page": "context", "title": "Context"},
            "statement": {
                "href": "statement.htm#statement",
                "page": "statement",
                "title": "Statement",
            },
        }
        entries = {
            key: bibliography_entry(key) for key in ("Cited", "Inline", "Kept", "Unused")
        }
        return labels, {"schema_version": 1, "entries": entries}

    def test_selects_citations_keeps_extras_and_trims_csl(self) -> None:
        labels_upstream, bibliography_upstream = self.upstream()
        labels, bibliography = build_snapshots(
            self.root, labels_upstream, bibliography_upstream, ("Kept",)
        )
        self.assertEqual(list(labels), ["context", "statement", "unused"])
        self.assertEqual(list(bibliography["entries"]), ["Cited", "Inline", "Kept"])
        self.assertNotIn("id", bibliography["entries"]["Cited"]["csl"])
        self.assertNotIn("unused", bibliography["entries"]["Cited"]["csl"])
        self.assertTrue(bibliography["entries"]["Cited"]["bibtex"].endswith("\n"))

        write_snapshots(self.root, labels, bibliography)
        first = (self.root / "website" / "symcat" / "bibliography.json").read_text()
        write_snapshots(self.root, labels, bibliography)
        self.assertEqual(
            first, (self.root / "website" / "symcat" / "bibliography.json").read_text()
        )
        self.assertEqual(json.loads(first), bibliography)

    def test_missing_cited_key_or_used_label_is_an_error(self) -> None:
        labels, bibliography = self.upstream()
        del bibliography["entries"]["Inline"]
        with self.assertRaisesRegex(CatalogError, "upstream bibliography missing: Inline"):
            build_snapshots(self.root, labels, bibliography)
        labels, bibliography = self.upstream()
        del labels["context"]
        with self.assertRaisesRegex(CatalogError, "upstream labels missing: context"):
            build_snapshots(self.root, labels, bibliography)


if __name__ == "__main__":
    unittest.main()
