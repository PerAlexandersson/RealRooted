import RealRooted.GeneralizedSnakePosets.Narayana.Claim7
import RealRooted.GeneralizedSnakePosets.Narayana.PFFacts
import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence
import RealRooted.GeneralizedSnakePosets.Narayana.Turan
import RealRooted.GeneralizedSnakePosets.SnakeBoard
import RealRooted.GeneralizedSnakePosets.SnakeTheorem35

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
name = """RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.\
truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial"""
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
name = "RealRooted.GeneralizedSnakePosets.generalizedSnakeTheorem35"
module = "RealRooted.GeneralizedSnakePosets.SnakeTheorem35"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.theorem41_generalizedSnakeRookModel"
module = "RealRooted.GeneralizedSnakePosets.SnakeTheorem35"
-->

<!-- realrooted-catalog-content -->
# Generalized snake posets

A generalized snake poset `P(w)` is a width-two poset built from a word `w` in
the letters `L` and `R`. By Braun and Jal, the `h^*`-polynomial of its order
polytope is the non-nesting rook polynomial `M_w` of a skew board whose cells
are the incomparable cross-chain pairs of `P(w)`.

**Theorem (Braun–Jal, Theorem 4.1).** Each `M_w` is real-rooted, and deleting
the last letter of `w` gives a polynomial interlacing `M_w`.

This theorem is fully formalized for the concrete snake board
(`theorem41_generalizedSnakeRookModel`).

The proof runs through the **modified Narayana polynomials**
`P_n = t^{-1} N_{n+1}`, which are the rook polynomials of the full truncated
staircase boards, and `G_n = sum_{i<n} R(n, i)`, a sum of truncated-staircase
rook polynomials.

- **Analytic core.** Every `P_n` is a PF polynomial and `P_n ≪ P_{n+1}`.
  Lemma 3.4: for `m ≥ 2`, `λ ≥ 0` and `ν ≥ -1`,
  `(λx + ν) P_{m-1} + P_m ≪ (λx + ν) P_m + P_{m+1}`. Claim (7) and a matrix
  induction then give Theorem 4.1 for any family satisfying the combinatorial
  inputs below.
- **Theorem 3.5** (`generalizedSnakeTheorem35`). If `k` is the last position
  where `w` differs from its final letter and `s = |w| - k - 1`, then
  `M_w = M_{w[:k+1]} P_s + x M_{w[:k]} G_s`.
- **Staircase inputs.** `x G_{n-1} = P_n - (1 + x) P_{n-1}`, and `G_n - G_{n-1}`
  has nonnegative coefficients, both from a column recurrence for
  truncated-staircase rook polynomials. Constant words give `P_{n+1}`.

For Theorem 3.5, the incomparable pairs `(i, j)` of `P(w)` are the cells whose
gaps between `i` and `j` all carry one letter: `R` above the diagonal, `L`
below it. The Braun–Jal board reverses the column order, which turns
non-nesting placements into chains that increase in both coordinates. The
final constant block cuts this band into a staircase, one column of cells, and
the band of the prefix, and the recurrence follows by expanding along that
column.

The reversed column orientation matters. The non-nesting rook polynomial of the
reversed board agrees with an independent `h^*`-polynomial computation for
every word of length at most 11. The non-nesting rook polynomial of the
unreversed board does not.

## References

Braun and Jal, [“Order polytopes of generalized snake posets are
h*-real-rooted,”](https://arxiv.org/abs/2607.00922) arXiv:2607.00922 (2026).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.GeneralizedSnakePosets`.
-/
