#!/usr/bin/env python3
"""Source-only acceptance, cache-refresh, ranking and MCP tests for rr-nav."""

from __future__ import annotations

import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True

import agent_index
import challenge_catalog as catalog
from rr_nav import Navigator, ROOT, VERSIONS, serve

ACCEPTANCE = [
    ("Narayana polynomials real-rooted", {}, "RealRooted.splits_narayanaPolynomial", "narayana"),
    ("matching polynomial real roots", {},
     "RealRooted.Graph.weightedMatchingPolynomialByEdges_splits", "heilmann-lieb"),
    ("every real linear combination of f and g is real-rooted", {},
     "RealRooted.allComboRealRooted_iff_interl_or_reverse", "hermite-kakeya-obreschkoff"),
    ("Hurwitz stable even and odd parts interlace", {},
     "RealRooted.isHurwitzStable_oddEvenPolynomial_iff", "hermite-biehler-hurwitz"),
    ("Eulerian polynomials", {"property": "interlacing"},
     "RealRooted.interlaces_eulerianTilde_succ", "eulerian"),
]


class AcceptanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temp = tempfile.TemporaryDirectory(prefix="rr-nav-acceptance-")
        polytool = os.environ.get("RR_NAV_POLYTOOL")
        cls.nav = Navigator(ROOT, Path(polytool) if polytool else None, Path(cls.temp.name))

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temp.cleanup()

    def test_catalog_queries_top_three(self) -> None:
        for query, filters, name, slug in ACCEPTANCE:
            with self.subTest(query=query):
                hits = self.nav.call("find_start", {"query": query, "limit": 3, **filters})["hits"]
                self.assertIn(name, [h.get("name") for h in hits])
                hit = next(h for h in hits if h.get("name") == name)
                self.assertEqual(hit["page"]["slug"], slug)
        decl = self.nav.call("get_declaration", {"name": ACCEPTANCE[0][2]})["declaration"]
        self.assertEqual(decl["module"], "RealRooted.NarayanaTransformation.Endpoints")

    def test_python_bm25_acceptance(self) -> None:
        search = self.nav.start_search
        original = search.backend
        search.backend = "python-bm25"
        try:
            self.test_catalog_queries_top_three()
        finally:
            search.backend = original

    def test_solved_conjectures(self) -> None:
        hits = self.nav.call("find_start", {"kind": "conjecture"})["hits"]
        self.assertEqual(len(hits), 8)
        self.assertTrue(all(h["type"] == "page" for h in hits))
        self.assertTrue({"boros-moll", "zigzag-eulerian"}.issubset(
            {h["page"]["slug"] for h in hits}))

    def test_layer_two_search_and_definition(self) -> None:
        hits = self.nav.call("search_declarations", {
            "query": "fixed delay recurrence strict interlacing",
            "conclusion_key": "StrictInterl", "limit": 3,
        })["hits"]
        name = "RealRooted.strictInterl_of_fixedDelay_recurrence"
        self.assertIn(name, [h["name"] for h in hits])
        hit = next(h for h in hits if h["name"] == name)
        self.assertIn("variableDelay", hit["routes"]["tactic"])
        self.assertGreater(hit["source_line"], 0)
        decl = self.nav.call("get_declaration", {"name": "RealRooted.StrictInterl"})
        self.assertIsNotNone(decl["declaration"])
        self.assertFalse(decl["unresolved_at_head"])

    def test_pages_filters_and_limits(self) -> None:
        result = self.nav.call("get_page", {"slug": "families/narayana", "limit": 1})
        self.assertEqual(result["page"]["slug"], "narayana")
        self.assertEqual(len(result["declarations"]), 1)
        by_name = self.nav.call("get_page", {"name": ACCEPTANCE[0][2]})
        self.assertEqual(by_name["page"]["slug"], "narayana")
        self.assertTrue(by_name["families"])
        families = self.nav.call("find_start", {"property": "interlacing"})["hits"]
        self.assertTrue(families)
        self.assertTrue(all(h["property"] == "interlacing" for h in families))
        for arguments in ({"limit": 0}, {"limit": 51}, {"limit": True}, {"bad": 1}):
            with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                self.nav.call("find_start", arguments)
        self.assertEqual(self.nav.call("find_start", {"query": "zzzznomatch"})["hits"], [])
        filtered = self.nav.call("search_declarations", {
            "query": "fixed delay", "module_prefix": "RealRooted.Interlacing.VariableDelay",
        })["hits"]
        self.assertTrue(filtered)
        self.assertTrue(all(h["module"].startswith("RealRooted.Interlacing.VariableDelay")
                            for h in filtered))

    def test_real_polytool_acceptance_when_configured(self) -> None:
        if self.nav.polytool is None:
            self.skipTest("set RR_NAV_POLYTOOL to also check the current external checkout")
        self.assertEqual(len([r for r in self.nav.poly_routes
                              if not r.startswith("polytool/")]), 18)
        route = self.nav.call("route_links", {"name": "index_section_lift"})
        self.assertIn("pathPower", [r["name"] for r in route["tactic_routes"]])
        self.assertIn("LinearRecurrence.ofMatrix_pow_isSolution_subsequence",
                      [d["name"] for d in route["declarations"]])
        self.assertTrue(any(r["rust_path"].endswith("parent_theorems/index_section.rs")
                            for r in route["polytool_routes"]))
        name = "RealRooted.Toeplitz.Circle.strictInterl_of_circleNonneg"
        links = self.nav.call("route_links", {"name": name})
        self.assertIn("hessenberg-circle-criterion", [p["slug"] for p in links["pages"]])
        self.assertEqual(links["pages"][0]["kind"], "original")
        self.assertTrue(any(r["rust_path"].endswith("bkw/certified/toeplitz.rs")
                            for r in links["polytool_routes"]))
        missing = self.nav.call("route_links", {
            "name": "RealRooted.evenDerivative_preservesPF_tfae",
        })
        self.assertTrue(missing["declarations"][0]["unresolved_at_head"])
        self.assertTrue(any(r["rust_path"].endswith("basis_map/theorems/published.rs")
                            for r in missing["polytool_routes"]))
        delay = self.nav.call("route_links", {
            "name": "RealRooted.strictInterl_of_fixedDelay_recurrence",
        })
        self.assertIn("variable_delay", [r["name"] for r in delay["polytool_routes"]])


class RefreshAndProtocolTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="rr-nav-fixture-")
        self.base = Path(self.temp.name)
        self.root = self.base / "repo"
        self.root.mkdir()
        (self.root / "RealRooted/Challenges").mkdir(parents=True)
        (self.root / "scripts").mkdir()
        shutil.copytree(ROOT / "website", self.root / "website")
        (self.root / "website/redirects.toml").write_text("[redirects]\n")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.26.0\n")
        self.lean = self.root / "RealRooted/Challenges/Sample.lean"
        self.lean.write_text('''module
/-!
<!-- realrooted-catalog
version = 1
kind = "original"
section = "theorems"
slug = "sample"
formalized = "2026-01-01"
[[theorems]]
name = "RealRooted.sample"
label = "A sample theorem"
headline = true
-->
<!-- realrooted-catalog-content -->
# Sample

A source-only fixture.

## References

- [Paper](https://example.org/)
<!-- /realrooted-catalog-content -->
-/
namespace RealRooted
theorem sample : True := by trivial
end RealRooted
''')
        self.routes = self.root / "scripts/tactic_routes.json"
        self.routes.write_text(json.dumps({"routes": [{
            "name": "pathPower", "theorems": ["RealRooted.sample"],
            "module": "RealRooted.Challenges.Sample", "summary": "Sample route",
            "requires": "True", "conclusion": "True", "frontEnds": [], "examples": [],
        }]}, indent=2))
        toeplitz = self.root / "RealRooted/Challenges/Toeplitz.lean"
        toeplitz.write_text(self.lean.read_text().replace(
            'slug = "sample"', 'slug = "hessenberg-circle-criterion"').replace(
            "RealRooted.sample", "RealRooted.Toeplitz.Circle.strictInterl_of_circleNonneg").replace(
            "namespace RealRooted\ntheorem sample", "namespace RealRooted.Toeplitz.Circle\n"
            "theorem strictInterl_of_circleNonneg").replace(
            "end RealRooted", "end RealRooted.Toeplitz.Circle"))
        (self.root / "RealRooted/Section.lean").write_text(
            "namespace LinearRecurrence\ntheorem ofMatrix_pow_isSolution_subsequence : "
            "True := by trivial\nend LinearRecurrence\n")
        self.poly = self.base / "polytool"
        parent = self.poly / "src/recurrence/lift/parent_theorems"
        parent.mkdir(parents=True)
        (parent / "registry.rs").write_text(
            'IndexSectionLift, index_section, "index_section_lift",\n"Index section", { };\n')
        self.rust = parent / "index_section.rs"
        self.rust.write_text('const REFERENCE: &str = "RealRooted route pathPower '
                             '(RealRooted.sample, LinearRecurrence.missing, '
                             'LinearRecurrence.ofMatrix_pow_isSolution_subsequence)";\n')
        rust_toeplitz = self.poly / "src/bkw/certified/toeplitz.rs"
        rust_toeplitz.parent.mkdir(parents=True)
        rust_toeplitz.write_text('// RealRooted.Toeplitz.Circle.strictInterl_of_circleNonneg\n')
        published = self.poly / "src/recurrence/lift/basis_map/theorems/published.rs"
        published.parent.mkdir(parents=True)
        published.write_text('// RealRooted.evenDerivative_preservesPF_tfae\n')
        self.revision = "a" * 40
        self.revision_patch = patch.object(catalog, "revision_at",
                                           side_effect=lambda p: self.revision)
        self.revision_patch.start()
        self.files_patch = patch.object(agent_index.lemma_index, "git_files",
                                        side_effect=lambda root: sorted(root.rglob("*.lean")))
        self.files_patch.start()
        self.nav = Navigator(self.root, self.poly, self.base / "cache")

    def tearDown(self) -> None:
        self.files_patch.stop()
        self.revision_patch.stop()
        self.temp.cleanup()

    def test_dirty_content_add_delete_and_revision_rebuilds(self) -> None:
        self.nav.call("index_status", {})
        self.assertEqual(self.nav.rebuilds, 1)
        original = self.lean.read_text()
        before = self.lean.stat()
        self.lean.write_text(original.replace(": True :=", ": 1 = 1 :="))
        os.utime(self.lean, ns=(before.st_atime_ns, before.st_mtime_ns))
        result = self.nav.call("get_declaration", {"name": "RealRooted.sample"})
        self.assertIn("1 = 1", result["declaration"]["statement"])
        self.assertEqual(self.nav.rebuilds, 2)
        new = self.root / "RealRooted/New.lean"
        new.write_text("namespace RealRooted\n"
                       "theorem newLemma : True := by trivial\nend RealRooted\n")
        self.assertFalse(self.nav.call("get_declaration", {
            "name": "RealRooted.newLemma"})["unresolved_at_head"])
        new.unlink()
        self.assertTrue(self.nav.call("get_declaration", {
            "name": "RealRooted.newLemma"})["unresolved_at_head"])
        self.revision = "b" * 40
        self.assertEqual(self.nav.call("index_status", {})["checkout_head"], self.revision)
        self.assertEqual(self.nav.rebuilds, 5)

    def test_polytool_refresh_and_unresolved_flag(self) -> None:
        result = self.nav.call("route_links", {"name": "index_section_lift"})
        self.assertEqual(result["tactic_routes"][0]["name"], "pathPower")
        self.assertTrue(next(d for d in result["declarations"]
                             if d["name"] == "LinearRecurrence.missing")["unresolved_at_head"])
        self.rust.write_text(self.rust.read_text().replace("missing", "newMissing"))
        result = self.nav.call("route_links", {"name": "LinearRecurrence.newMissing"})
        self.assertTrue(result["polytool_routes"])
        self.assertEqual(self.nav.rebuilds, 2)
        self.assertEqual(result["polytool_routes"][0]["citations"][0]["source_line"], 1)

    def test_polytool_acceptance_without_external_checkout(self) -> None:
        route = self.nav.call("route_links", {"name": "index_section_lift"})
        self.assertIn("pathPower", [r["name"] for r in route["tactic_routes"]])
        self.assertIn("LinearRecurrence.ofMatrix_pow_isSolution_subsequence",
                      [d["name"] for d in route["declarations"]])
        links = self.nav.call("route_links", {
            "name": "RealRooted.Toeplitz.Circle.strictInterl_of_circleNonneg",
        })
        self.assertEqual(links["pages"][0]["slug"], "hessenberg-circle-criterion")
        self.assertEqual(links["pages"][0]["kind"], "original")
        self.assertEqual(links["polytool_routes"][0]["rust_path"],
                         "polytool/src/bkw/certified/toeplitz.rs")
        missing = self.nav.call("route_links", {
            "name": "RealRooted.evenDerivative_preservesPF_tfae",
        })
        self.assertTrue(missing["declarations"][0]["unresolved_at_head"])
        self.assertEqual(missing["polytool_routes"][0]["rust_path"],
                         "polytool/src/recurrence/lift/basis_map/theorems/published.rs")

    def test_rust_directory_route(self) -> None:
        directory = self.rust.parent / "index_section"
        directory.mkdir()
        self.rust.rename(directory / "mod.rs")
        (directory / "theorems.rs").write_text('// RealRooted.sample\n')
        links = self.nav.call("route_links", {"name": "index_section_lift"})
        route = next(r for r in links["polytool_routes"] if r["name"] == "index_section_lift")
        self.assertTrue(route["rust_path"].endswith("index_section/mod.rs"))
        self.assertTrue(any(c["rust_path"].endswith("index_section/theorems.rs")
                            for c in route["citations"]))

    def test_cached_startup_and_failed_refresh(self) -> None:
        cached = Navigator(self.root, self.poly, self.base / "cache")
        self.assertEqual(cached.rebuilds, 0)
        self.lean.write_text(self.lean.read_text().replace(
            "theorem sample", "theorem renamedSample"))
        with self.assertRaises(catalog.CatalogError):
            cached.call("index_status", {})
        # The previous cache is untouched; failure never produces a stale response.
        self.assertEqual(json.loads(cached.path.read_text())["revision"], self.revision)

    def test_no_polytool_and_cache_location(self) -> None:
        nav = Navigator(self.root, cache=self.base / "no-poly-cache")
        self.assertEqual(nav.call("index_status", {})["counts"]["polytool_routes"], 0)
        with self.assertRaises(ValueError):
            Navigator(self.root, cache=self.root / "cache")
        with self.assertRaises(ValueError):
            Navigator(self.root, cache=self.base / "Dropbox/cache")

    def test_mcp_handshake_and_round_trip(self) -> None:
        requests = [
            {"id": 1, "method": "initialize", "params": {
                "protocolVersion": "2024-11-05", "capabilities": {},
                "clientInfo": {"name": "test", "version": "1"}}},
            {"method": "notifications/initialized"},
            {"id": 2, "method": "tools/list"},
            {"id": 3, "method": "tools/call", "params": {
                "name": "get_declaration", "arguments": {"name": "RealRooted.sample"}}},
            {"id": 4, "method": "ping"},
            {"id": 5, "method": "tools/call", "params": {
                "name": "find_start", "arguments": {"limit": 51}}},
            {"id": 6, "method": "bad"},
        ]
        source = io.StringIO("".join(json.dumps({"jsonrpc": "2.0", **r}) + "\n"
                                     for r in requests))
        sink = io.StringIO()
        serve(self.nav, source, sink)
        responses = [json.loads(line) for line in sink.getvalue().splitlines()]
        self.assertEqual([r["id"] for r in responses], [1, 2, 3, 4, 5, 6])
        self.assertEqual(responses[0]["result"]["protocolVersion"], "2024-11-05")
        self.assertEqual(len(responses[1]["result"]["tools"]), 6)
        content = json.loads(responses[2]["result"]["content"][0]["text"])
        self.assertEqual(content["declaration"]["name"], "RealRooted.sample")
        self.assertEqual(content["index_revision"], self.revision)
        self.assertEqual(responses[3]["result"], {})
        self.assertTrue(responses[4]["result"]["isError"])
        self.assertEqual(responses[5]["error"]["code"], -32601)

    def test_protocol_errors_and_negotiation(self) -> None:
        source = io.StringIO('invalid\n[]\n'
                             '{"jsonrpc":"2.0","id":1,"method":"tools/list"}\n'
                             '{"jsonrpc":"2.0","id":2,"method":"initialize",'
                             '"params":{"protocolVersion":"unknown"}}\n'
                             '{"jsonrpc":"2.0","id":null,"method":"ping"}\n'
                             '{"jsonrpc":"2.0","id":1.5,"method":"ping"}\n')
        sink = io.StringIO()
        serve(self.nav, source, sink)
        responses = [json.loads(line) for line in sink.getvalue().splitlines()]
        self.assertEqual([r["error"]["code"] for r in responses[:3]],
                         [-32700, -32600, -32000])
        self.assertEqual(responses[3]["result"]["protocolVersion"], VERSIONS[0])
        self.assertEqual(responses[4], {"jsonrpc": "2.0", "id": None, "result": {}})
        self.assertEqual(responses[5], {"jsonrpc": "2.0", "id": 1.5, "result": {}})


class CompatibilityTests(unittest.TestCase):
    def test_python_310_toml_fallback(self) -> None:
        # Simulate the absent 3.11 module in a fresh interpreter, using only stdlib imports.
        code = '''
import importlib.abc
import sys
class NoTomllib(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path, target=None):
        if fullname == "tomllib":
            raise ModuleNotFoundError(fullname)
sys.meta_path.insert(0, NoTomllib())
import challenge_catalog as c
from pathlib import Path
assert len(c.load_catalog(Path(sys.argv[1]))) == 71
'''
        result = subprocess.run([sys.executable, "-B", "-c", code, str(ROOT)],
                                cwd=ROOT / "scripts", capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
