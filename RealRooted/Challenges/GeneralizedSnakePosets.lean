import RealRooted.GeneralizedSnakePosets.Narayana.Claim7
import RealRooted.GeneralizedSnakePosets.Narayana.PFFacts
import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence
import RealRooted.GeneralizedSnakePosets.Narayana.Turan
import RealRooted.GeneralizedSnakePosets.SnakeBoard
import RealRooted.GeneralizedSnakePosets.SnakeTheorem41

/-!
# Generalized snake poset challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "generalized-snake-posets"
authors = ["Braun", "Jal"]
years = [2026]

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.SnakeLetter"
module = "RealRooted.GeneralizedSnakePosets.SnakeWord"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.generalizedSnakeBoard"
module = "RealRooted.GeneralizedSnakePosets.SnakeBoard"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.rookPolynomial"
module = "RealRooted.GeneralizedSnakePosets.FiniteBoard"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.modifiedNarayanaPolynomial"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Modified"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.auxiliaryG"
module = "RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Auxiliary"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.modifiedNarayanaPolynomial_isPFPolynomial"
module = "RealRooted.GeneralizedSnakePosets.Narayana.PFFacts"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.modifiedNarayanaPolynomial_strictInterl_succ"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Recurrence"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.lemma34ModifiedNarayanaInterlacing_modified"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Turan"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Recurrence"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.theorem41NonNestingRook_modified_of_sourceInputs"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Claim7"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.narayanaAuxiliaryGRecurrence_modified"
module = "RealRooted.GeneralizedSnakePosets.TruncatedStaircase.ColumnRecurrence"

[[theorems]]
name = """RealRooted.GeneralizedSnakePosets.\
generalizedSnakeRookModel_snakePolynomial_of_isConstant"""
module = "RealRooted.GeneralizedSnakePosets.SnakeConstant"

[[theorems]]
name = """RealRooted.GeneralizedSnakePosets.\
theorem41_generalizedSnakeRookModel_of_theorem35"""
module = "RealRooted.GeneralizedSnakePosets.SnakeTheorem41"
-->

<!-- realrooted-catalog-content -->
# Generalized snake posets

A generalized snake poset `P(w)` is a width-two poset built from a word `w` in
the letters `L` and `R`. By Braun and Jal, the `h^*`-polynomial of its order
polytope is the non-nesting rook polynomial `M_w` of a skew board whose cells
are the incomparable cross-chain pairs of `P(w)`.

**Theorem (Braun–Jal, Theorem 4.1).** Each `M_w` is real-rooted, and deleting
the last letter of `w` gives a polynomial interlacing `M_w`.

The proof runs through the **modified Narayana polynomials**
`P_n = t^{-1} N_{n+1}`, which are the rook polynomials of the full truncated
staircase boards. The following analytic core is fully formalized:

- every `P_n` is a PF polynomial, and `P_n ≪ P_{n+1}`;
- **Lemma 3.4:** for `m ≥ 2`, `λ ≥ 0` and `ν ≥ -1`,
  `(λx + ν) P_{m-1} + P_m ≪ (λx + ν) P_m + P_{m+1}`;
- **Claim (7) and the matrix induction:** Theorem 4.1 for any family `M`,
  from the combinatorial inputs below.

For the concrete snake board, all of these inputs except the snake-word
recurrence (Theorem 3.5) are now proved:

- the auxiliary recurrence `x G_{n-1} = P_n - (1 + x) P_{n-1}` and the
  nonnegativity of `G_n - G_{n-1}`, for every `n`, from a column recurrence
  for truncated-staircase rook polynomials;
- constant words give `P_{n+1}`: the board is the full staircase, or its
  half-turn;
- the degree identity, which follows from Theorem 3.5.

So Theorem 4.1 for the concrete board is proved relative to Theorem 3.5
alone. The board is the set of incomparable cross pairs of `P(w)` with the
column order reversed. With that orientation the non-nesting rook polynomial
equals the `h^*`-polynomial of the order polytope. This was checked
independently for every word of length at most 11. Without the reversal the
two disagree.

## References

Braun and Jal, [“Order polytopes of generalized snake posets are
h*-real-rooted,”](https://arxiv.org/abs/2607.00922) arXiv:2607.00922 (2026).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.GeneralizedSnakePosets`.
-/
