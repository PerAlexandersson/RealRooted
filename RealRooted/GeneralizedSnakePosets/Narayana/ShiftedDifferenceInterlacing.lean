import RealRooted.GeneralizedSnakePosets.Narayana.Turan
import RealRooted.GeneralizedSnakePosets.MatrixInduction
import RealRooted.GeneralizedSnakePosets.Narayana.ShiftedDifferenceInterlacingAnalytic

/-!
# The shifted difference interlacing claim for modified Narayana polynomials

This module combines the analytic affine-Narayana proof from the Turan development
with the endpoint-safe shifted difference-interlacing conversion.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- Root sum of the auxiliary polynomial `G_n` from the auxiliary recurrence.

The recurrence is a hypothesis because this module sits below its proof
`FiniteSkewBoard.narayanaAuxiliaryGRecurrence_modified`
(`TruncatedStaircase.ColumnRecurrence`). -/
theorem auxiliaryG_roots_sum_of_narayanaRecurrence
    (hrec2 : NarayanaAuxiliaryGRecurrence
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {n : ℕ} (hn : 2 ≤ n) :
    (FiniteSkewBoard.auxiliaryG n).roots.sum =
      -(((n : ℝ) + 1) * ((n : ℝ) - 1) / 3) := by
  have hsplit : (FiniteSkewBoard.auxiliaryG n).Splits := by
    simpa using auxiliaryGPencil_splits_of_combinatorial hrec2
      affineModifiedNarayanaInterlacing_modified (m := n) (lam := 0) (nu := 0)
      hn (by norm_num) (by norm_num)
  have hdeg := auxiliaryG_natDegree_of_narayanaRecurrence hrec2 n (by lia)
  have hdegpos : 0 < (FiniteSkewBoard.auxiliaryG n).natDegree := by
    rw [hdeg]
    lia
  have hlead : (FiniteSkewBoard.auxiliaryG n).leadingCoeff = (n : ℝ) := by
    rw [← Polynomial.coeff_natDegree, hdeg]
    exact auxiliaryG_coeff_sub_one_of_narayanaRecurrence hrec2 n (by lia)
  have hnext :
      (FiniteSkewBoard.auxiliaryG n).nextCoeff =
        ((n : ℝ) + 1) * (n : ℝ) * ((n : ℝ) - 1) / 3 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos hdegpos, hdeg]
    simpa [Nat.sub_sub] using
      auxiliaryG_coeff_sub_two_of_narayanaRecurrence hrec2 n hn
  have hvieta := hsplit.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [hnext, hlead] at hvieta
  apply mul_left_cancel₀ (show (n : ℝ) ≠ 0 by positivity)
  linarith

/-- The shifted difference interlacing claim for the concrete modified Narayana family.

The hypotheses are the combinatorial inputs: the auxiliary recurrence and
coefficientwise nonnegativity of `G n - G (n - 1)`.  Both are proved in
`TruncatedStaircase.ColumnRecurrence`, which this module does not import;
all analytic real-rootedness and interlacing steps are proved here. -/
theorem shiftedDifferenceInterlacing_modified
    (hrec2 : NarayanaAuxiliaryGRecurrence
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1))) :
    ShiftedDifferenceInterlacing
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG :=
  shiftedDifferenceInterlacing_modified_of_combinatorial hrec2
    affineModifiedNarayanaInterlacing_modified hH_nonneg

/-- The auxiliary interlacing lemma follows from the shifted difference interlacing claim at `lam =
nu = 0`, apart from
the already proved `n = 1` base case.  The recurrence and difference
nonnegativity hypotheses are the combinatorial inputs documented above; this
deduction from them is entirely analytic. -/
theorem auxiliaryGInterlaces_modified
    (hrec2 : NarayanaAuxiliaryGRecurrence
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1)))
    {n : ℕ} (hn : 1 ≤ n) :
    StrictInterl (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  rcases eq_or_lt_of_le hn with h | hn
  · subst n
    exact auxiliaryGInterlaces_modified_base
  · simpa using
      shiftedDifferenceInterlacing_modified hrec2 hH_nonneg
        (m := n) (lam := 0) (nu := 0) (by lia) (by norm_num) (by norm_num)

/-- Consecutive auxiliary `G` polynomials have real-rooted positive linear
combinations. This is the part of adjacent `G` interlacing supplied
directly by the auxiliary recurrence and the affine Narayana interlacing lemma; orienting the
pencil remains a
separate analytic step. -/
theorem auxiliaryG_posComboRealRooted_of_narayanaRecurrence
    (hrec2 : NarayanaAuxiliaryGRecurrence
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {m : ℕ} (hm : 2 ≤ m) :
    PosComboRealRooted (FiniteSkewBoard.auxiliaryG (m - 1))
      (FiniteSkewBoard.auxiliaryG m) := by
  intro lam mu hlam hmu
  have hmu_ne : mu ≠ 0 := ne_of_gt hmu
  have hratio : 0 < lam / mu := div_pos hlam hmu
  let V : ℝ[X] :=
    C (lam / mu) * FiniteSkewBoard.auxiliaryG (m - 1) +
      FiniteSkewBoard.auxiliaryG m
  have hV_split : V.Splits := by
    simpa [V] using auxiliaryGPencil_splits_of_combinatorial (lam := 0) hrec2
      affineModifiedNarayanaInterlacing_modified hm (by positivity)
      (show -1 ≤ lam / mu by linarith)
  have hV_pos : HasPosLeadingCoeff V := by
    simpa [V] using auxiliaryGPencil_hasPosLeadingCoeff_of_narayanaRecurrence
      (lam := 0) (nu := lam / mu) hrec2 hm (by positivity)
  have hscale :
      C mu * V =
        C lam * FiniteSkewBoard.auxiliaryG (m - 1) +
          C mu * FiniteSkewBoard.auxiliaryG m := by
    dsimp [V]
    rw [mul_add, ← mul_assoc, ← map_mul]
    field_simp
  rw [← hscale]
  exact ⟨mul_ne_zero (by simpa using hmu_ne) hV_pos.ne_zero,
    hV_split.C_mul mu⟩

/-- Snake-interlacing through the source `[P, G; Q, H]` matrix.

The hypotheses are the combinatorial inputs: the auxiliary recurrence,
nonnegativity of the board difference `H`, the snake recurrence, the degree
identity, and the constant-word staircase identity.  No hypothesis assumes
real-rootedness, interlacing, or splitting.  All of them are proved for the
concrete non-nesting-rook model in `snakeInterlacing_generalizedSnakeRookModel`
(`SnakeRecurrence`). -/
theorem nonNestingRookInterlacing_modified_of_sourceInputs
    {M : SnakeWord → ℝ[X]}
    (hrec2 : NarayanaAuxiliaryGRecurrence
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1)))
    (hrec : GeneralizedSnakeRecurrence M
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hM_nonneg : ∀ w : SnakeWord, HasNonnegCoeffs (M w))
    (hdeg : ∀ {w : SnakeWord}, 1 ≤ w.length →
      (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant →
      M w = modifiedNarayanaPolynomial (w.length + 1)) :
    NonNestingRookInterlacing M :=
  snakeInterlacing_of_differenceInterlacing_of_constant_matches_succ_length
    (M := M) (P := modifiedNarayanaPolynomial)
    (G := FiniteSkewBoard.auxiliaryG)
    hrec
    ((snakeDifferenceInterlacing_iff_shiftedDifferenceInterlacing _ _).mpr
      (shiftedDifferenceInterlacing_modified hrec2 hH_nonneg))
    modifiedNarayanaPolynomial_ne_zero
    modifiedNarayanaPolynomial_interlaces_succ
    modifiedNarayanaPolynomial_one FiniteSkewBoard.auxiliaryG_one
    modifiedNarayanaPolynomial_hasNonnegCoeffs
    FiniteSkewBoard.auxiliaryG_hasNonnegCoeffs
    (fun {_m} hm => narayanaDifference_modified_hasNonnegCoeffs (by lia))
    (fun {_m} hm => by
      simpa [auxiliaryDifference] using hH_nonneg _ (by lia))
    hM_nonneg hdeg hM_const

end GeneralizedSnakePosets
end RealRooted
