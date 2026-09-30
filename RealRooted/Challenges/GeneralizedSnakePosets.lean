import RealRooted.GeneralizedSnakePosets.Narayana.Claim7
import RealRooted.GeneralizedSnakePosets.Narayana.PFFacts
import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence
import RealRooted.GeneralizedSnakePosets.Narayana.Turan
import RealRooted.GeneralizedSnakePosets.SnakeBoard

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

Those inputs are not yet formalized for the concrete board model, so
Theorem 4.1 is proved here relative to them:

- the auxiliary recurrence `x G_{n-1} = P_n - (1 + x) P_{n-1}`, checked for
  `n ≤ 8`;
- nonnegativity of `G_n - G_{n-1}`;
- the snake-word recurrence (Theorem 3.5);
- the degree and constant-word identities.

None of these assumes real-rootedness, interlacing, or splitting.

## References

Braun and Jal, [“Order polytopes of generalized snake posets are
h*-real-rooted,”](https://arxiv.org/abs/2607.00922) arXiv:2607.00922 (2026).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.GeneralizedSnakePosets`.
-/
