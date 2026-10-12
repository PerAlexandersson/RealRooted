"""Regression fixtures for the lightweight Lean declaration scanner."""

import unittest

from lean_decl import declaration_starts, find_value_assignment, value_assignment_end


def split_declaration(text):
    assignment = find_value_assignment(text)
    if assignment is None:
        raise AssertionError("fixture has no declaration assignment")
    return text[:assignment], text[value_assignment_end(text, assignment) :]


def statement_key(text):
    statement, _ = split_declaration(text)
    return statement.split("\n", 1)[1].strip()


class LeanDeclarationScannerTest(unittest.TestCase):
    def test_degree_box_statements_with_named_arguments_differ(self):
        first = statement_key("""theorem rename_algebraicSymbol_sourcePolarizedOperator_eq_sum
    (h : sourceDiagonalVariableMap (τ := τ) (n := n) = q) : q = explicitSum := by
  exact h
""")
        second = statement_key("""theorem rename_algebraicSymbol_sourcePolarizedOperator
    (h : sourceDiagonalVariableMap (τ := τ) (n := n) = q) : q = originalSymbol := by
  exact h
""")
        self.assertIn("explicitSum", first)
        self.assertIn("originalSymbol", second)
        self.assertNotEqual(first, second)

    def test_named_argument_duplicate_statements_keep_their_conclusion(self):
        left = statement_key("""theorem left
    (h : f (τ := τ) (n := n)) : q = r := by
  exact h
""")
        right = statement_key("""theorem right
    (h : f (τ := τ) (n := n)) : q = r := by
  exact h
""")
        self.assertEqual(left, right)

    def test_named_argument_duplicate_proofs_keep_their_body(self):
        _, left = split_declaration("""theorem left
    (h : f (τ := τ) (n := n)) : q = r := by
  simpa using h
""")
        _, right = split_declaration("""theorem right
    (h : f (τ := τ) (n := n)) : q = s := by
  simpa using h
""")
        self.assertEqual(left, right)

    def test_let_comment_and_string_assignments_do_not_split_the_type(self):
        statement, proof = split_declaration("""theorem lets : let x := 1
  -- := is only a comment
  let message := ":="
  x = 1 := by
  simp
""")
        self.assertIn("x = 1", statement)
        self.assertEqual(proof.strip(), "by\n  simp")

    def test_equation_compiler_bodies_end_the_declaration_header(self):
        statement, body = split_declaration("""def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci n + fibonacci (n + 1)
""")
        self.assertEqual(statement.strip(), "def fibonacci : ℕ → ℕ")
        self.assertTrue(body.lstrip().startswith("| 0 =>"))

    def test_every_recognized_declaration_ends_a_theorem_block(self):
        starts = list(declaration_starts([
            "/- theorem ignored : True := by trivial",
            "still a comment -/",
            "theorem before : True := by trivial",
            "def unrelated := 1",
            "private theorem after : True := by trivial",
        ]))
        self.assertEqual([(number, match.group("kind")) for number, match in starts],
                         [(2, "theorem"), (3, "def"), (4, "theorem")])


if __name__ == "__main__":
    unittest.main()
