#!/usr/bin/env python3
"""Unit tests for the symmetricfunctions.com snapshot synchronizer."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import sys
import tempfile
import unittest
from http.client import IncompleteRead
from unittest.mock import patch

sys.dont_write_bytecode = True

from challenge_catalog import CatalogError, load_catalog, render_site
from symcat_sync import build_snapshots, main, write_snapshots


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

    def seed_snapshots(self) -> tuple[dict, dict]:
        snapshots = build_snapshots(self.root, *self.upstream(), ("Kept",))
        write_snapshots(self.root, *snapshots)
        return snapshots[0], snapshots[1]["entries"]

    def write_upstream(self, labels: dict, bibliography: dict) -> pathlib.Path:
        directory = self.root / "exports"
        directory.mkdir(exist_ok=True)
        (directory / "site-labels.json").write_text(json.dumps(labels), encoding="utf-8")
        (directory / "bibliography.json").write_text(json.dumps(bibliography), encoding="utf-8")
        return directory

    def snapshot_bytes(self) -> tuple[bytes, bytes]:
        directory = self.root / "website/symcat"
        return (
            (directory / "labels.json").read_bytes(),
            (directory / "bibliography.json").read_bytes(),
        )

    def run_sync(self, source: pathlib.Path | str, *options: str) -> tuple[int, str, str]:
        stdout, stderr = io.StringIO(), io.StringIO()
        argv = ["symcat_sync.py", str(source), "--repo-root", str(self.root), *options]
        with (
            patch.object(sys, "argv", argv),
            contextlib.redirect_stdout(stdout),
            contextlib.redirect_stderr(stderr),
        ):
            result = main()
        return result, stdout.getvalue(), stderr.getvalue()

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
        with self.assertRaisesRegex(CatalogError, "bibliography missing from live export and snapshot: Inline"):
            build_snapshots(self.root, labels, bibliography)
        labels, bibliography = self.upstream()
        del labels["context"]
        with self.assertRaisesRegex(CatalogError, "labels missing from live export and snapshot: context"):
            build_snapshots(self.root, labels, bibliography)

    def test_live_records_override_snapshot_and_upstream_removals_are_retained(self) -> None:
        old_labels, old_entries = self.seed_snapshots()
        labels, bibliography = self.upstream()
        labels["statement"]["href"] = "new.htm#statement"
        labels["new"] = {"href": "new.htm#new"}
        del labels["context"]
        del bibliography["entries"]["Inline"]
        del bibliography["entries"]["Kept"]
        bibliography["entries"]["Cited"]["csl"]["title"] = "Updated title"
        source = self.write_upstream(labels, bibliography)

        status, stdout, stderr = self.run_sync(source)
        self.assertEqual(status, 0, stderr)
        self.assertIn("ok: wrote", stdout)
        self.assertIn("labels removed upstream; retaining snapshot records: context", stderr)
        self.assertIn("bibliography keys removed upstream; retaining snapshot records: Inline, Kept", stderr)
        saved_labels, saved_bibliography = (json.loads(data) for data in self.snapshot_bytes())
        self.assertEqual(saved_labels["statement"], "new.htm#statement")
        self.assertEqual(saved_labels["context"], old_labels["context"])
        self.assertEqual(saved_labels["new"], "new.htm#new")
        self.assertEqual(saved_bibliography["entries"]["Cited"]["csl"]["title"], "Updated title")
        self.assertEqual(saved_bibliography["entries"]["Inline"], old_entries["Inline"])
        self.assertEqual(saved_bibliography["entries"]["Kept"], old_entries["Kept"])
        self.assertNotIn("Unused", saved_bibliography["entries"])

    def test_live_only_cited_key_is_added(self) -> None:
        labels, entries = self.seed_snapshots()
        del entries["Inline"]
        write_snapshots(self.root, labels, {"schema_version": 1, "entries": entries})
        source = self.write_upstream(*self.upstream())
        status, _, stderr = self.run_sync(source, "--fallback-to-snapshot")
        self.assertEqual(status, 0, stderr)
        self.assertIn("Inline", json.loads(self.snapshot_bytes()[1])["entries"])

    def test_missing_from_both_sources_still_fails_with_fallback_enabled(self) -> None:
        for kind, key in (("bibliography", "Inline"), ("labels", "context")):
            with self.subTest(kind=kind):
                old_labels, old_entries = self.seed_snapshots()
                labels, bibliography = self.upstream()
                if kind == "bibliography":
                    del old_entries[key]
                    del bibliography["entries"][key]
                else:
                    del old_labels[key]
                    del labels[key]
                write_snapshots(self.root, old_labels, {"schema_version": 1, "entries": old_entries})
                before = self.snapshot_bytes()
                status, _, stderr = self.run_sync(self.write_upstream(labels, bibliography), "--fallback-to-snapshot")
                self.assertEqual(status, 1)
                self.assertIn(f"missing from live export and snapshot: {key}", stderr)
                self.assertEqual(self.snapshot_bytes(), before)

    def test_page_level_labels_are_required(self) -> None:
        path = self.root / "RealRooted/Challenges/Sample.lean"
        path.write_text(SOURCE.replace('version = 1', 'version = 1\nsymcat = ["pageOnly"]'), encoding="utf-8")
        with self.assertRaisesRegex(CatalogError, "missing from live export and snapshot: pageOnly"):
            build_snapshots(self.root, *self.upstream())

    def test_fetch_failure_or_invalid_json_keeps_both_snapshots_unchanged(self) -> None:
        self.seed_snapshots()
        labels, bibliography = self.upstream()
        labels["statement"]["href"] = "changed.htm"
        source = self.write_upstream(labels, bibliography)
        before = self.snapshot_bytes()
        bibliography_path = source / "bibliography.json"
        for failure in ("missing", "invalid JSON"):
            with self.subTest(failure=failure):
                if failure == "missing":
                    bibliography_path.unlink()
                else:
                    bibliography_path.write_text("not JSON", encoding="utf-8")
                status, _, stderr = self.run_sync(source, "--fallback-to-snapshot")
                self.assertEqual(status, 0, stderr)
                self.assertIn("falling back to committed snapshots (unchanged)", stderr)
                self.assertEqual(self.snapshot_bytes(), before)

    def test_network_outage_falls_back_and_manual_refresh_still_fails(self) -> None:
        self.seed_snapshots()
        before = self.snapshot_bytes()
        with patch("symcat_sync.urlopen", side_effect=OSError("network unavailable")):
            status, _, stderr = self.run_sync("https://example.invalid/", "--fallback-to-snapshot")
            self.assertEqual(status, 0)
            self.assertIn("falling back to committed snapshots", stderr)
            status, _, stderr = self.run_sync("https://example.invalid/")
            self.assertEqual(status, 1)
            self.assertIn("network unavailable", stderr)
        self.assertEqual(self.snapshot_bytes(), before)

    def test_incomplete_http_response_falls_back(self) -> None:
        self.seed_snapshots()
        before = self.snapshot_bytes()
        with patch("symcat_sync.urlopen", side_effect=IncompleteRead(b"partial JSON")):
            status, _, stderr = self.run_sync("https://example.invalid/", "--fallback-to-snapshot")
        self.assertEqual(status, 0)
        self.assertIn("falling back to committed snapshots", stderr)
        self.assertEqual(self.snapshot_bytes(), before)

    def test_fallback_requires_valid_snapshots(self) -> None:
        status, _, _ = self.run_sync(self.root / "missing", "--fallback-to-snapshot")
        self.assertEqual(status, 1)
        self.seed_snapshots()
        (self.root / "website/symcat/labels.json").write_text("[]", encoding="utf-8")
        status, _, stderr = self.run_sync(self.root / "missing", "--fallback-to-snapshot")
        self.assertEqual(status, 1)
        self.assertIn("expected a mapping", stderr)

    def test_offline_fallback_does_not_hide_invalid_references_from_renderer(self) -> None:
        for kind, key in (("bibliography", "Inline"), ("labels", "context")):
            with self.subTest(kind=kind):
                labels, entries = self.seed_snapshots()
                if kind == "bibliography":
                    del entries[key]
                else:
                    del labels[key]
                write_snapshots(self.root, labels, {"schema_version": 1, "entries": entries})
                status, _, stderr = self.run_sync(self.root / "missing", "--fallback-to-snapshot")
                self.assertEqual(status, 0, stderr)
                with self.assertRaisesRegex(CatalogError, f"unknown .*{key}"):
                    render_site(self.root, load_catalog(self.root), {}, "0" * 40)

    def test_check_compares_both_exports_without_writing_or_failing_on_staleness(self) -> None:
        self.seed_snapshots()
        before = self.snapshot_bytes()
        labels, bibliography = self.upstream()
        labels["statement"]["href"] = "changed.htm"
        labels["new"] = {"href": "new.htm"}
        bibliography["entries"]["Inline"]["bibtex"] = "@misc{Inline, title={Revised}}"
        status, stdout, stderr = self.run_sync(self.write_upstream(labels, bibliography), "--check")
        self.assertEqual(status, 0, stderr)
        self.assertIn("snapshots are stale", stdout)
        self.assertIn("labels: 1 added, 1 updated", stdout)
        self.assertIn("bibliography entries: 0 added, 1 updated", stdout)
        self.assertIn("python3 scripts/symcat_sync.py", stdout)
        self.assertEqual(self.snapshot_bytes(), before)

    def test_check_current_and_unavailable_bibliography(self) -> None:
        self.seed_snapshots()
        before = self.snapshot_bytes()
        source = self.write_upstream(*self.upstream())
        status, stdout, stderr = self.run_sync(source, "--check")
        self.assertEqual(status, 0, stderr)
        self.assertIn("snapshots are current", stdout)
        (source / "bibliography.json").unlink()
        status, _, stderr = self.run_sync(source, "--check")
        self.assertEqual(status, 0)
        self.assertIn("snapshot freshness unavailable", stderr)
        self.assertEqual(self.snapshot_bytes(), before)

    def test_invalid_live_schema_remains_an_error(self) -> None:
        self.seed_snapshots()
        before = self.snapshot_bytes()
        source = self.write_upstream(self.upstream()[0], {"entries": {}})
        status, _, stderr = self.run_sync(source, "--fallback-to-snapshot")
        self.assertEqual(status, 1)
        self.assertIn("invalid schema", stderr)
        self.assertEqual(self.snapshot_bytes(), before)


if __name__ == "__main__":
    unittest.main()
