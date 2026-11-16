#!/usr/bin/env python3
"""Ratchet naming findings for declarations published in the catalog."""
import argparse
from collections import Counter
from pathlib import Path
import re
import sys
import unittest

sys.dont_write_bytecode = True
from challenge_catalog import (
    CatalogItem, SourceDeclaration, load_catalog, source_declarations,
    strip_comments_and_strings,
)

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


def declared_result(declaration):
    """Read the explicit result after the binders, without inspecting a proof/body."""
    source = strip_comments_and_strings(declaration.source_code)
    depth = 0
    for index, char in enumerate(source):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == ":" and depth == 0:
            return source[index + 1:].split(":=", 1)[0].strip()
    return ""


def preservation_predicates(declarations):
    """Only explicitly Prop-valued definitions establish preservation-predicate names."""
    return {
        name for name, declaration in declarations.items()
        if declaration.actual_kind == "definition"
        and name.rsplit(".", 1)[-1].startswith("Preserves")
        and declared_result(declaration) == "Prop"
    }


def preserves_violation(item, declarations, predicates):
    """Distinguish operation closure names from literal predicates in conclusions."""
    leaf = item.name.rsplit(".", 1)[-1]
    if "preserves" not in leaf.lower():
        return False
    declaration = declarations.get(item.name)
    if declaration is None:
        return True
    if item.name in predicates:
        return False
    if declaration.actual_kind == "theorem":
        # A conclusion-named theorem may mention a literal preservation predicate,
        # e.g. ncard_preservesInterlacing or preservesRealRootedOrZero_iff_....
        # Require both the complete name segment and the constant in the result;
        # foo_preserves_pf and sampleOperator_preserves remain closure violations.
        result_names = set(re.findall(r"[\w.]+", declared_result(declaration)))
        for predicate in predicates:
            constant = predicate.rsplit(".", 1)[-1]
            segment = constant[0].lower() + constant[1:]
            if segment not in leaf.split("_"):
                continue
            if any(name == predicate or name.rsplit(".", 1)[-1] == constant
                   for name in result_names):
                return False
    return True


def naming_declarations(pages, root):
    """Load selected declarations and definitions that can own literal predicate names."""
    paths = {
        root / (item.module.replace(".", "/") + ".lean"
                if item.module else page.source_path)
        for page in pages for item in page.items
    }
    for path in (root / "RealRooted").rglob("*.lean"):
        if re.search(r"\b(?:def|abbrev)\s+(?:[\w.]*\.)?Preserves\w*\b",
                     path.read_text(encoding="utf-8")):
            paths.add(path)
    declarations = {}
    for path in sorted(paths):
        declarations.update(source_declarations(root, path))
    return declarations


def findings(pages, family=False, declarations=None):
    declarations = declarations or {}
    predicates = preservation_predicates(declarations)
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
            if preserves_violation(item, declarations, predicates):
                rules.append("preserves")
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

            def test_preserves_predicate_namespace(self):
                from types import SimpleNamespace
                cases = (
                    ("PreservesOrderedPF.mul", False),
                    ("PreservesOrderedPF.iff_differentialTests", False),
                    ("IsPFPolynomial.narayanaTransform", False),
                    ("foo_preserves_pf", True),
                )
                for suffix, expected in cases:
                    with self.subTest(suffix=suffix):
                        name = "RealRooted." + suffix
                        item = CatalogItem(name, "theorem", None)
                        page = SimpleNamespace(items=[item], source_path="Sample.lean")
                        self.assertEqual(f"preserves\t{name}" in findings([page]), expected)

            def test_preserves_semantic_role(self):
                from types import SimpleNamespace
                prefix = "RealRooted."
                cases = (
                    ("PreservesOrderedPF", "definition",
                     "def PreservesOrderedPF (T : ℕ → ℕ) : Prop := ∀ n, T n = n", False),
                    ("PreservesData", "definition", "def PreservesData : ℕ := 0", True),
                    ("foo_preserves_pf", "theorem",
                     "theorem foo_preserves_pf : PreservesOrderedPF id", True),
                    ("sampleOperator_preserves", "theorem",
                     "theorem sampleOperator_preserves : True", True),
                    ("ncard_preservesOrderedPF", "theorem",
                     "theorem ncard_preservesOrderedPF : {T | PreservesOrderedPF T}.ncard = 1",
                     False),
                    ("preservesOrderedPF_iff_eq", "theorem",
                     "theorem preservesOrderedPF_iff_eq : PreservesOrderedPF T ↔ T = id",
                     False),
                    ("foo_preservesOrderedPF", "theorem",
                     "theorem foo_preservesOrderedPF (h : PreservesOrderedPF T) : True", True),
                    ("preservesDataCount", "definition",
                     "def preservesDataCount : ℕ := 0", True),
                )
                declarations = {
                    prefix + suffix: SourceDeclaration(
                        prefix + suffix, kind, "Sample.lean", 1, False, source
                    )
                    for suffix, kind, source, _ in cases
                }
                for suffix, kind, _, expected in cases:
                    with self.subTest(suffix=suffix):
                        name = prefix + suffix
                        item = CatalogItem(name, kind, None)
                        page = SimpleNamespace(items=[item], source_path="Sample.lean")
                        self.assertEqual(f"preserves\t{name}" in findings(
                            [page], declarations=declarations
                        ), expected)

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
    pages = load_catalog(ROOT)
    current = findings(pages, args.family, naming_declarations(pages, ROOT))
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
