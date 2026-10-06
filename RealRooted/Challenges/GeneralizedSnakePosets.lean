import RealRooted.GeneralizedSnakePosets.Narayana.ShiftedDifferenceInterlacing
import RealRooted.GeneralizedSnakePosets.Narayana.PFFacts
import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence
import RealRooted.GeneralizedSnakePosets.Narayana.Turan
import RealRooted.GeneralizedSnakePosets.SnakeBoard
import RealRooted.GeneralizedSnakePosets.SnakeRecurrence
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.ColumnRecurrence

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
label = "Letters L and R of a snake word"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.SnakeWord.IsConstant"
module = "RealRooted.GeneralizedSnakePosets.SnakeWord"
label = "Constant snake words"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.SnakeWord.IsLastChangeIndex"
module = "RealRooted.GeneralizedSnakePosets.SnakeWord"
label = "Last position differing from the final letter"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.generalizedSnakeBoard"
module = "RealRooted.GeneralizedSnakePosets.SnakeBoard"
label = "Board of a generalized snake poset"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.rookPolynomial"
module = "RealRooted.GeneralizedSnakePosets.FiniteBoard"
label = "Non-nesting rook polynomial of a board"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.modifiedNarayanaPolynomial"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Modified"
label = "Modified Narayana polynomials Pₙ"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.auxiliaryG"
module = "RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Auxiliary"
label = "Auxiliary polynomials Gₙ"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.modifiedNarayanaPolynomial_isPFPolynomial"
module = "RealRooted.GeneralizedSnakePosets.Narayana.PFFacts"
label = "Modified Narayana polynomials are Pólya-frequency"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.modifiedNarayanaPolynomial_strictInterl_succ"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Modified"
label = "Consecutive modified Narayana polynomials interlace"

[[theorems]]
name = "RealRooted.Challenges.GeneralizedSnakePosets.modifiedNarayana_affine_strictInterl"
module = "RealRooted.Challenges.GeneralizedSnakePosets"
label = "Affine combinations of consecutive modified Narayana polynomials interlace"

[[theorems]]
name = """RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.\
truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial"""
module = "RealRooted.GeneralizedSnakePosets.Narayana.Recurrence"
label = "Full truncated staircases have rook polynomial Pₙ"

[[theorems]]
name = "RealRooted.Challenges.GeneralizedSnakePosets.auxiliaryG_recurrence"
module = "RealRooted.Challenges.GeneralizedSnakePosets"
label = "The auxiliary polynomials Gₙ in terms of Pₙ"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.auxiliaryG_strictInterl_modifiedNarayana"
module = "RealRooted.GeneralizedSnakePosets.Narayana.ShiftedDifferenceInterlacing"
label = "The auxiliary polynomial Gₙ interlaces Pₙ"

[[theorems]]
name = """RealRooted.Challenges.GeneralizedSnakePosets.\
rookPolynomial_generalizedSnakeBoard_of_isConstant"""
module = "RealRooted.Challenges.GeneralizedSnakePosets"
label = "Constant words give modified Narayana polynomials"

[[theorems]]
name = """RealRooted.Challenges.GeneralizedSnakePosets.\
rookPolynomial_generalizedSnakeBoard_recurrence"""
module = "RealRooted.Challenges.GeneralizedSnakePosets"
label = "Recurrence for the snake polynomials"
headline = true

[[theorems]]
name = """RealRooted.Challenges.GeneralizedSnakePosets.\
rookPolynomial_generalizedSnakeBoard_splits_and_interlaces"""
module = "RealRooted.Challenges.GeneralizedSnakePosets"
label = "Snake polynomials are real-rooted and interlace"
headline = true
-->

<!-- realrooted-catalog-content -->
# Generalized snake posets

A generalized snake poset $P(w)$ is a width-two poset built from a word $w$ in
the letters $L$ and $R$. Braun and Jal show that the $h^*$-polynomial of its
order polytope is the non-nesting rook polynomial $M_w$ of a skew board whose
cells are the incomparable cross-chain pairs of $P(w)$.

**Theorem (Braun–Jal).** If $w$ is nonempty, then $M_w$ is real-rooted, and
deleting the last letter of $w$ gives a polynomial interlacing $M_w$.

The proof uses the **modified Narayana polynomials** $P_n = t^{-1} N_{n+1}$,
which are the rook polynomials of the full truncated staircase boards, and
auxiliary polynomials $G_n$, which are sums of truncated-staircase rook
polynomials.

- **Recurrence.** If $k$ is the last position where $w$ differs from its final
  letter and $s = |w| - k - 1$, then
  $M_w = M_{w[:k+1]}\, P_s + x\, M_{w[:k]}\, G_s$. Constant words give
  $M_w = P_{|w|+1}$.
- **Narayana input.** Every $P_n$ is a PF polynomial, $P_n \ll P_{n+1}$, and
  for $m \geq 2$, $\lambda \geq 0$ and $\nu \geq -1$,
  $(\lambda x+\nu) P_{m-1} + P_m \ll (\lambda x+\nu) P_m + P_{m+1}$.
- **Staircase input.** $x\, G_{n-1} = P_n - (1+x) P_{n-1}$, and $G_n - G_{n-1}$
  has nonnegative coefficients.
- **Auxiliary interlacing.** For $n \geq 1$, $G_n \ll P_n$.

Induction on the length of $w$ along the recurrence then gives the theorem.

## References

Braun and Jal, [“Order polytopes of generalized snake posets are
h*-real-rooted,”](https://arxiv.org/abs/2607.00922) arXiv:2607.00922 (2026).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.GeneralizedSnakePosets`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace GeneralizedSnakePosets

open RealRooted.GeneralizedSnakePosets

/-- If `w` is nonempty, then the snake polynomial `M_w` is real-rooted, and
deleting the last letter of `w` gives a polynomial interlacing it. -/
theorem rookPolynomial_generalizedSnakeBoard_splits_and_interlaces {w : SnakeWord}
    (hw : w ≠ []) :
    ((generalizedSnakeBoard w).rookPolynomial ≠ 0 ∧
        (generalizedSnakeBoard w).rookPolynomial.Splits) ∧
      Interlaces (generalizedSnakeBoard w.dropLast).rookPolynomial
        (generalizedSnakeBoard w).rookPolynomial := by
  rw [List.dropLast_eq_take]
  exact snakeInterlacing_generalizedSnakeRookModel (List.length_pos_iff.mpr hw)

/-- If `k` is the last position where `w` differs from its final letter, then
`M_w = M_{w[:k+1]} P_s + X M_{w[:k]} G_s` with `s = |w| - k - 1`. -/
theorem rookPolynomial_generalizedSnakeBoard_recurrence {w : SnakeWord} {k : ℕ}
    (hk : w.IsLastChangeIndex k) :
    (generalizedSnakeBoard w).rookPolynomial =
      (generalizedSnakeBoard (w.take (k + 1))).rookPolynomial *
          modifiedNarayanaPolynomial (w.length - (k + 1)) +
        X * (generalizedSnakeBoard (w.take k)).rookPolynomial *
          FiniteSkewBoard.auxiliaryG (w.length - (k + 1)) :=
  generalizedSnakeRecurrence hk.not_isConstant hk

/-- A constant word `w` has snake polynomial `M_w = P_{|w|+1}`. -/
theorem rookPolynomial_generalizedSnakeBoard_of_isConstant {w : SnakeWord}
    (hw : w.IsConstant) :
    (generalizedSnakeBoard w).rookPolynomial = modifiedNarayanaPolynomial (w.length + 1) :=
  generalizedSnakeRookModel_snakePolynomial_of_isConstant hw

/-- Affine combinations of consecutive modified Narayana polynomials interlace. -/
theorem modifiedNarayana_affine_strictInterl {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m)
    (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    StrictInterl
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) + modifiedNarayanaPolynomial m)
      ((C lam * X + C nu) * modifiedNarayanaPolynomial m +
        modifiedNarayanaPolynomial (m + 1)) :=
  affineModifiedNarayanaInterlacing_modified hm hlam hnu

/-- `X G_{n-1} = P_n - (1 + X) P_{n-1}`. -/
theorem auxiliaryG_recurrence {n : ℕ} (hn : n ≠ 0) :
    X * FiniteSkewBoard.auxiliaryG (n - 1) =
      modifiedNarayanaPolynomial n - (1 + X) * modifiedNarayanaPolynomial (n - 1) :=
  FiniteSkewBoard.narayanaAuxiliaryGRecurrence_modified (Nat.one_le_iff_ne_zero.mpr hn)

end GeneralizedSnakePosets
end Challenges
end RealRooted
