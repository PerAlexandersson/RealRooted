"""Regression fixtures for the message-driven fixers (no Lean needed)."""

import unittest

from apply_lint_fixes import unused_simp_arg_edit
from lean_messages import apply_edits, suggestions
from replay_row_tactics import find_sites, placed

TRY_THESE = (
    "Try these:\n"
    "  [apply] rr_row_interlaces (thm := RealRooted.threeTerm_interlaces_of_nonnegCoeffs)\n"
    "  [apply] rcases n with _ | n\n"
    "    · rr_row_side\n"
    "    apply\n"
    "        RealRooted.foo (P := fun m => A (m + 1)) <;>\n"
    "      rr_row_side"
)


class SuggestionTests(unittest.TestCase):
    def test_try_these(self):
        first, second = suggestions(TRY_THESE)
        self.assertEqual(first, [
            "rr_row_interlaces (thm := RealRooted.threeTerm_interlaces_of_nonnegCoeffs)"])
        self.assertEqual(second, [
            "rcases n with _ | n",
            "· rr_row_side",
            "apply",
            "    RealRooted.foo (P := fun m => A (m + 1)) <;>",
            "  rr_row_side",
        ])

    def test_hint(self):
        text = ("This simp argument is unused:\n  Nat.reduceMul\n\nHint: Omit it.\n"
                "  [apply] simp only [add_zero, h]\n\nNote: linter")
        self.assertEqual(suggestions(text), [["simp only [add_zero, h]"]])


class SimpArgTests(unittest.TestCase):
    def delete(self, text, arg):
        start = text.index(arg)
        edit = unused_simp_arg_edit(text, start, start + len(arg))
        return apply_edits(text, [edit])[0]

    def test_middle_and_last(self):
        self.assertEqual(self.delete("simp only [a, X, b]", "X"), "simp only [a, b]")
        self.assertEqual(self.delete("simp only [a, X]", "X"), "simp only [a]")

    def test_first_and_only(self):
        self.assertEqual(self.delete("simp only [X, b] at h", "X"), "simp only [b] at h")
        self.assertEqual(self.delete("simp [X] at h", "X"), "simp at h")

    def test_wrapped(self):
        text = "simp only [a, b,\n    X, c]"
        self.assertEqual(self.delete(text, "X"), "simp only [a, b,\n    c]")
        text = "simp only [a, b,\n    X,\n    c]"
        self.assertEqual(self.delete(text, "X"), "simp only [a, b,\n    c]")
        self.assertEqual(self.delete("simp only [a,\n    X]", "X"), "simp only [a]")


class ReplayLayoutTests(unittest.TestCase):
    def test_find_sites(self):
        text = "theorem t : P := by rr_row_splits\n"
        self.assertEqual(find_sites(text, [(1, 20)]), [(20, 33)])
        self.assertEqual(find_sites(text, [(1, None)]), [(20, 33)])

    def test_inline_by(self):
        text = "theorem t : P := by rr_row_splits\n"
        start = text.index("rr_row")
        new_start, code = placed(text, start, ["apply foo", "· bar"])
        self.assertEqual(text[:new_start] + code, "theorem t : P := by\n  apply foo\n  · bar")

    def test_line_start(self):
        text = "theorem t : P := by\n  rr_row_splits\n"
        start = text.index("rr_row")
        new_start, code = placed(text, start, ["apply foo", "  bar"])
        self.assertEqual(text[:new_start] + code, "theorem t : P := by\n  apply foo\n    bar")

    def test_after_combinator(self):
        text = "  foo <;> rr_row_side\n"
        start = text.index("rr_row")
        _, code = placed(text, start, ["apply foo", "· bar"])
        self.assertEqual(code, "(apply foo\n           · bar)")


if __name__ == "__main__":
    unittest.main()
