module

public import RealRooted.GeneralizedSnakePosets.Narayana.ShiftedDifferenceInterlacing
public import RealRooted.GeneralizedSnakePosets.Narayana.PFFacts
public import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence
import RealRooted.GeneralizedSnakePosets.Narayana.Turan
public import RealRooted.GeneralizedSnakePosets.SnakeBoard
import RealRooted.GeneralizedSnakePosets.SnakeRecurrence
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.ColumnRecurrence
import RealRooted.GeneralizedSnakePosets.SnakeConstant
public import RealRooted.GeneralizedSnakePosets.Narayana.Modified

/-!
# Real-rooted rook polynomials of generalized snake posets

<!-- realrooted-catalog
version = 1
section = "families"
slug = "generalized-snake-posets"
formalized = "2026-10-05"
tags = []
references = [
  "BraunJal2026x",
  "AlexanderssonJal2024x",
]
authors = ["Braun", "Jal", "Alexandersson"]
years = [2024, 2026]

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
module = "RealRooted.Challenges.Combinatorial.GeneralizedSnakePosets"
label = "Affine combinations of consecutive modified Narayana polynomials interlace"

[[theorems]]
name = """RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.\
truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial"""
module = "RealRooted.GeneralizedSnakePosets.Narayana.Recurrence"
label = "Full truncated staircases have rook polynomial Pₙ"

[[theorems]]
name = "RealRooted.Challenges.GeneralizedSnakePosets.auxiliaryG_recurrence"
module = "RealRooted.Challenges.Combinatorial.GeneralizedSnakePosets"
label = "The auxiliary polynomials Gₙ in terms of Pₙ"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.auxiliaryG_strictInterl_modifiedNarayana"
module = "RealRooted.GeneralizedSnakePosets.Narayana.ShiftedDifferenceInterlacing"
label = "The auxiliary polynomial Gₙ interlaces Pₙ"

[[theorems]]
name = """RealRooted.Challenges.GeneralizedSnakePosets.\
rookPolynomial_generalizedSnakeBoard_of_isConstant"""
module = "RealRooted.Challenges.Combinatorial.GeneralizedSnakePosets"
label = "Constant words give modified Narayana polynomials"

[[theorems]]
name = """RealRooted.Challenges.GeneralizedSnakePosets.\
rookPolynomial_generalizedSnakeBoard_recurrence"""
module = "RealRooted.Challenges.Combinatorial.GeneralizedSnakePosets"
label = "Recurrence for the snake polynomials"

[[theorems]]
name = """RealRooted.Challenges.GeneralizedSnakePosets.\
rookPolynomial_generalizedSnakeBoard_splits_and_interlaces"""
module = "RealRooted.Challenges.Combinatorial.GeneralizedSnakePosets"
label = "Snake polynomials are real-rooted and interlace"
headline = true
-->

<!-- realrooted-catalog-content -->
# Real-rooted rook polynomials of generalized snake posets

The non-nesting rook polynomial of a generalized snake word is real-rooted, and deleting the last
letter gives an interlacing polynomial.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated. A
polynomial is a *Pólya frequency (PF) polynomial* if it has nonnegative coefficients and only real
nonpositive roots.

A generalized snake poset $P(w)$ is a width-two poset built from a word $w$ in the letters $L$ and
$R$. Let $M_w$ be the non-nesting rook polynomial $\sum_Px^{|P|}$ of the board of incomparable
cross-chain pairs of $P(w)$, with column order reversed. Here $P$ runs over sets of cells of the
board, no two in a row, with columns strictly decreasing as rows increase. By Braun and Jal,
$M_w$ is the $h^*$-polynomial of the order polytope of $P(w)$ [@BraunJal2026x]. The board comes from
the Alexandersson–Jal correspondence between naturally labeled width-two posets and skew shapes,
under which the $P$-Eulerian polynomial is the non-nesting rook polynomial
[@AlexanderssonJal2024x].

**Theorem (Braun–Jal).** If $w$ is nonempty, then $M_w$ is nonzero and real-rooted, and
$M_{w'}\ll M_w$, where $w'$ is $w$ with its last letter deleted [@BraunJal2026x].

The proof uses the *modified Narayana polynomials* $P_n=t^{-1}N_{n+1}$, where
$N_n(t)=\sum_k\frac1n\binom nk\binom n{k-1}t^k$ is the Narayana polynomial, and auxiliary
polynomials $G_n$, which are sums of rook polynomials of truncated staircase boards.

- **Narayana polynomials.** $P_n$ is the rook polynomial of the full truncated staircase board
  of size $n$. Each $P_n$ is a PF polynomial, and $P_n\ll P_{n+1}$. For $m\ge2$, $\lambda\ge0$ and
  $\nu\ge-1$,
  $$(\lambda x+\nu)P_{m-1}+P_m\ \ll\ (\lambda x+\nu)P_m+P_{m+1}.$$
- **Auxiliary polynomials.** For $n\ge1$, $x\,G_{n-1}=P_n-(1+x)P_{n-1}$, the polynomial
  $G_n-G_{n-1}$ has nonnegative coefficients, and $G_n\ll P_n$.
- **Recurrence.** Number the positions of $w$ from $0$, let $k$ be the last position where $w$
  differs from its final letter, and put $s=|w|-k-1$. Then
  $$M_w=M_{w[:k+1]}\,P_s+x\,M_{w[:k]}\,G_s,$$
  where $w[:j]$ is the prefix of length $j$. For a constant word $w$, $M_w=P_{|w|+1}$.

Induction on the length of $w$ along the recurrence gives the theorem.

## References

- [@BraunJal2026x]
- [@AlexanderssonJal2024x, Art. 59]

See also the [rook matroid section](sf:rookMatroidPolynomials) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.GeneralizedSnakePosets`.
-/

public section

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
