#!/usr/bin/env python3
"""Unit tests for the parser of the private-import ratchet."""

from __future__ import annotations

import pathlib
import sys
import unittest


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from check_private_imports import findings  # noqa: E402


class FindingsTests(unittest.TestCase):
    def test_plain_downgrade_is_reported(self) -> None:
        report = (
            "/repo/RealRooted/A.lean:\n"
            "  remove #[public import RealRooted.B, import Mathlib.Tactic.Ring]\n"
            "  add #[import RealRooted.B, import Mathlib.Tactic.Ring.Basic]\n"
        )
        self.assertEqual(findings(report), {"RealRooted/A.lean: RealRooted.B"})

    def test_replacement_by_narrower_public_import_is_not_a_downgrade(self) -> None:
        # Shake moves `RealRooted.C` to a plain import but needs a public import of the module
        # that declares a name used in a statement; the downgrade alone would break the build.
        report = (
            "/repo/RealRooted/A.lean:\n"
            "  remove #[public import RealRooted.C]\n"
            "  add #[import RealRooted.C, public import Mathlib.Algebra.Polynomial.Roots]\n"
        )
        self.assertEqual(findings(report), set())

    def test_removal_without_matching_plain_import_is_ignored(self) -> None:
        report = (
            "/repo/RealRooted/A.lean:\n"
            "  remove #[public import RealRooted.D]\n"
            "  add #[import Mathlib.Tactic.Ring]\n"
        )
        self.assertEqual(findings(report), set())

    def test_modules_are_independent(self) -> None:
        report = (
            "/repo/RealRooted/A.lean:\n"
            "  remove #[public import RealRooted.B]\n"
            "  add #[import RealRooted.B]\n"
            "/repo/RealRooted/E.lean:\n"
            "  remove #[public import RealRooted.F]\n"
            "  add #[import RealRooted.F, public import RealRooted.G]\n"
        )
        self.assertEqual(findings(report), {"RealRooted/A.lean: RealRooted.B"})


if __name__ == "__main__":
    unittest.main()
