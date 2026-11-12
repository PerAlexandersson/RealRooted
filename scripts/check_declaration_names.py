#!/usr/bin/env python3
"""Ratchet naming findings for declarations published in the catalog."""
import argparse
from collections import Counter
from pathlib import Path
import re
import sys
import unittest

sys.dont_write_bytecode = True
from challenge_catalog import CatalogItem, load_catalog

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "scripts/declaration_names_baseline.txt"
RULES = ("oeis", "length", "workflow", "preserves", "challenges", "family")
WORKFLOW_WORDS = {
    "internal", "backend", "legacy", "hyp", "bridge", "statement", "auxiliary"
}
NAME_SEGMENT_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z]|$)|[A-Z]?[a-z]+|[A-Z]+")


def has_workflow_segment(name):
    """Match whole name segments, preserving the mathematical term internal zeros."""
    for component in name.split("."):
        # Preserve the original underscore-led scope of the abbreviated _aux/_core rules.
        # In particular, Mathlib's existing NewtonAux namespace is outside that scope.
        for segment in component.split("_"):
            segment_words = NAME_SEGMENT_RE.findall(segment)
            if segment_words and segment_words[0].lower() in {"aux", "core"}:
                return True
        words = [word.lower() for word in NAME_SEGMENT_RE.findall(component)]
        for index, word in enumerate(words):
            if word == "internal" and index + 1 < len(words):
                if words[index + 1].startswith("zero"):
                    continue
            if word in WORKFLOW_WORDS:
                return True
    return False


def findings(pages, family=False):
    result = set()
    for page in pages:
        for item in page.items:
            name = item.name
            leaf = name.rsplit(".", 1)[-1]
            owner_path = (
                item.module.replace(".", "/") + ".lean"
                if item.module else page.source_path
            )
            rules = []
            if re.search(r"A\d{6}", name) and not owner_path.startswith(
                "RealRooted/Applications/OEIS/"
            ):
                rules.append("oeis")
            if len(leaf) > 60: rules.append("length")
            if has_workflow_segment(name):
                rules.append("workflow")
            if "preserves" in name.lower(): rules.append("preserves")
            if item.expected_kind == "theorem" and name.startswith("RealRooted.Challenges."):
                rules.append("challenges")
            if family and page.section == "families" and item.headline:
                # Provisional convention: a namespace segment equals the normalized slug.
                normalized = lambda x: re.sub(r"[^a-z0-9]", "", x.lower())
                if normalized(page.slug) not in [normalized(x) for x in name.split(".")[:-1]]:
                    rules.append("family")
            result.update(f"{rule}\t{name}" for rule in rules)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true")
    parser.add_argument(
        "--family", action="store_true", help="enable provisional slug-based family namespace rule"
    )
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        class Tests(unittest.TestCase):
            def test_rules(self):
                from types import SimpleNamespace
                item = CatalogItem(
                    "RealRooted.Challenges.A123456.Backend_preserves_" + "x" * 61,
                    "theorem", None, headline=True,
                )
                page = SimpleNamespace(
                    items=[item], section="families", slug="sample", source_path="Sample.lean"
                )
                self.assertEqual({x.split("\t")[0] for x in findings([page], True)}, set(RULES))
                good = CatalogItem("RealRooted.Foo.good", "theorem", None)
                self.assertFalse(findings([SimpleNamespace(
                    items=[good], section="theorems", slug="foo", source_path="Foo.lean"
                )]))

            def test_oeis_owner_exemption(self):
                from types import SimpleNamespace
                name = "RealRooted.Applications.OEIS.A123456.polynomial_splits"
                oeis_path = "RealRooted/Applications/OEIS/A123456.lean"
                cases = (
                    (None, oeis_path, False),
                    ("RealRooted.Applications.OEIS.A123456", "Catalog.lean", False),
                    ("RealRooted.Theory.A123456", oeis_path, True),
                    (None, "RealRooted/Applications/OEISExtra/A123456.lean", True),
                    (None, "RealRooted/Theory/A123456.lean", True),
                )
                for module, source_path, expected in cases:
                    with self.subTest(module=module, source_path=source_path):
                        item = CatalogItem(name, "theorem", module)
                        page = SimpleNamespace(items=[item], source_path=source_path)
                        self.assertEqual(f"oeis\t{name}" in findings([page]), expected)

            def test_workflow_segments(self):
                from types import SimpleNamespace
                positive = (
                    "Internal", "Backend", "Legacy", "Hyp", "Bridge", "Statement",
                    "aux", "core", "auxiliary", "fooHyp", "fooHypBar", "fooHyp_bar",
                    "fooInternalBar", "fooBackendBar", "foo_aux_bar", "foo_core_bar",
                    "foo_auxBar", "foo_coreBar",
                    "fooAuxiliaryBar", "BACKEND", "fooBACKENDBar", "Backend.HyperbolicAt",
                    "InternalZerosBackend", "NoInternalZeros_backend",
                )
                negative = (
                    "Hyperbolic", "HyperbolicAt", "hyperbolicAt", "hyperbolicityCone",
                    "Hyperbolicity", "Hyperplane", "HyperplaneStable", "Hypergeometric",
                    "hypergeometricPolynomial", "Hypothesis", "Hypotheses",
                    "InternalZero", "InternalZeros", "InternalZeroPolynomial",
                    "NoInternalZeros", "coeffNoInternalZerosUpTo_mul",
                    "no_internal_zeros", "auxiliaryish", "backendish", "legacyish",
                    "bridgeless", "statementwise", "score", "exHypothesis",
                    "NewtonAux.newton_esymm_ineq",
                    "MvPolynomial.HyperbolicAt.of_joinedIn",
                    "MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary",
                )
                for expected, names in ((True, positive), (False, negative)):
                    for leaf in names:
                        with self.subTest(name=leaf, expected=expected):
                            name = "RealRooted." + leaf
                            item = CatalogItem(name, "theorem", None)
                            page = SimpleNamespace(items=[item], source_path="Sample.lean")
                            self.assertEqual(f"workflow\t{name}" in findings([page]), expected)
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
        return 0 if unittest.TextTestRunner().run(suite).wasSuccessful() else 1
    current = findings(load_catalog(ROOT), args.family)
    # Family findings are evaluated separately until the scheme is adopted.
    baseline = set(BASELINE.read_text().splitlines()) if BASELINE.exists() else set()
    if not args.family:
        baseline = {x for x in baseline if not x.startswith("family\t")}
    if args.update:
        if not args.family and BASELINE.exists():
            current |= {x for x in BASELINE.read_text().splitlines() if x.startswith("family\t")}
        BASELINE.write_text("".join(x + "\n" for x in sorted(current)))
        baseline = current
    counts = Counter(x.split("\t")[0] for x in current)
    print("Rule          Findings")
    for rule in RULES:
        disabled = " (disabled)" if rule == "family" and not args.family else ""
        print(f"{rule:12} {counts[rule]:8}" + disabled)
    for label, entries in (("new", current - baseline), ("stale", baseline - current)):
        for entry in sorted(entries): print(f"{label}: {entry}")
    return int(current != baseline)


if __name__ == "__main__":
    raise SystemExit(main())
