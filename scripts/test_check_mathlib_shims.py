#!/usr/bin/env python3
"""Unit tests for the source-only Mathlib shim checker."""

from __future__ import annotations

import json
import pathlib
import sys
import tempfile
import unittest


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from check_mathlib_shims import (  # noqa: E402
    check_registry,
    classify_match,
    mathlib_declaration_index,
    public_declarations,
    registry_coverage,
)


class NameExtractorTests(unittest.TestCase):
    def names(self, text: str):
        return public_declarations(text)

    def test_namespaces_sections_root_private_and_protected(self) -> None:
        declarations = self.names(
            """namespace Outer
section
theorem visible : True := trivial
protected theorem Thing.method : True := trivial
private theorem hidden : True := trivial
theorem _root_.rooted : True := trivial
end
end Outer
"""
        )
        self.assertEqual(
            [(item.name, item.kind) for item in declarations],
            [("Outer.visible", "theorem"), ("Outer.Thing.method", "theorem"), ("rooted", "theorem")],
        )

    def test_nested_namespaces_and_sections_do_not_change_names(self) -> None:
        declarations = self.names(
            """namespace One
namespace Two
section local
lemma three : True := trivial
end local
end Two
end One
"""
        )
        self.assertEqual([item.name for item in declarations], ["One.Two.three"])

    def test_attributes_aliases_and_deprecation(self) -> None:
        declarations = self.names(
            """namespace N
@[simp,
  local_attr]
theorem decorated : True := trivial
alias old ← decorated
@[deprecated decorated (since := "2026-10-13")]
alias older := decorated
private alias secret := decorated
end N
"""
        )
        self.assertEqual([item.name for item in declarations], ["N.decorated", "N.old", "N.older"])
        self.assertFalse(declarations[1].deprecated_alias)
        self.assertTrue(declarations[2].deprecated_alias)

    def test_named_and_anonymous_instances(self) -> None:
        declarations = self.names(
            """namespace N
instance namedInstance : Inhabited Nat := ⟨0⟩
instance : OfNat Nat 0 := ⟨0⟩
end N
"""
        )
        self.assertEqual([item.name for item in declarations], ["N.namedInstance"])

    def test_unicode_punctuation_subscripts_and_quoted_components(self) -> None:
        declarations = self.names(
            """namespace α.ℝ
theorem head?_signedRemainderSequence : True := trivial
theorem bang! : True := trivial
theorem forall₂_le_iff_countP_le : True := trivial
theorem getLast?_tail : True := trivial
theorem indexed₀₉ₐₜᵢ : True := trivial
theorem «quoted component !?».«nested name» : True := trivial
end α.ℝ
"""
        )
        self.assertEqual(
            [item.name for item in declarations],
            [
                "α.ℝ.head?_signedRemainderSequence",
                "α.ℝ.bang!",
                "α.ℝ.forall₂_le_iff_countP_le",
                "α.ℝ.getLast?_tail",
                "α.ℝ.indexed₀₉ₐₜᵢ",
                "α.ℝ.«quoted component !?».«nested name»",
            ],
        )

    def test_mathlib_protected_declarations_remain_qualified(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            mathlib = root / "Mathlib"
            mathlib.mkdir()
            (mathlib / "Protected.lean").write_text(
                "namespace ENNReal\nprotected theorem div_le_iff : True := trivial\nend ENNReal\n",
                encoding="utf-8",
            )
            names = mathlib_declaration_index(root)
        self.assertIn("ENNReal.div_le_iff", names)
        self.assertNotIn("div_le_iff", names)


class RegistryClassificationTests(unittest.TestCase):
    def write(self, root: pathlib.Path, relative: str, text: str) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def fixture(self):
        temp = tempfile.TemporaryDirectory()
        root = pathlib.Path(temp.name)
        self.write(root, "RealRooted/Mathlib/A.lean", "namespace A\ntheorem present : True := trivial\nend A\n")
        self.write(root, "RealRooted/Mathlib/B.lean", "namespace B\ntheorem absent : True := trivial\nend B\n")
        self.write(root, "Mathlib/A.lean", "namespace A\ntheorem present : True := trivial\nend A\n")
        return temp, root

    def test_exact_strict_speculative_and_sentinel(self) -> None:
        temp, root = self.fixture()
        self.addCleanup(temp.cleanup)
        registry = {
            "entries": [
                {"sources": ["RealRooted/Mathlib/A.lean"], "note": "exact"},
                {
                    "sources": ["RealRooted/Mathlib/B.lean"],
                    "declarations": ["A.present"],
                    "note": "speculative",
                    "speculative": True,
                },
            ]
        }
        findings, errors = check_registry(root, root, registry, strict=True)
        self.assertEqual(errors, [])
        self.assertEqual([(item.probe, item.kind, item.severity) for item in findings], [
            ("A.present", "exact", "error"),
            ("A.present", "speculative", "warning"),
        ])
        self.assertEqual(classify_match(speculative=False, landing_sentinel=True, strict=True), ("landing-sentinel", "warning"))

    def test_speculative_module_is_a_warning(self) -> None:
        temp, root = self.fixture()
        self.addCleanup(temp.cleanup)
        registry = {
            "entries": [{
                "sources": ["RealRooted/Mathlib/A.lean"],
                "modules": ["Mathlib.A"],
                "note": "module target",
                "speculative": True,
            }]
        }
        hidden, errors = check_registry(root, root, registry, strict=True)
        self.assertEqual(errors, [])
        self.assertNotIn("Mathlib.A", [item.probe for item in hidden])
        findings, errors = check_registry(root, root, registry, strict=True, show_modules=True)
        self.assertEqual(errors, [])
        self.assertIn(("Mathlib.A", "target-module", "warning"), [(x.probe, x.kind, x.severity) for x in findings])

    def test_coverage_requires_each_source_exactly_once(self) -> None:
        temp, root = self.fixture()
        self.addCleanup(temp.cleanup)
        registry = {"entries": [{"sources": ["RealRooted/Mathlib/A.lean"], "note": "only A"}]}
        errors = registry_coverage(root, registry)
        self.assertIn("uncovered shim source: RealRooted/Mathlib/B.lean", errors)
        registry["entries"].append({"sources": ["RealRooted/Mathlib/A.lean", "RealRooted/Mathlib/B.lean"], "note": "duplicate"})
        self.assertTrue(any("appears in entries" in error for error in registry_coverage(root, registry)))


if __name__ == "__main__":
    unittest.main()
