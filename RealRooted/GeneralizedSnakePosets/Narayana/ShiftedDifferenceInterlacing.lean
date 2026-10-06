import RealRooted.GeneralizedSnakePosets.Narayana.Turan
import RealRooted.GeneralizedSnakePosets.MatrixInduction
import RealRooted.GeneralizedSnakePosets.Narayana.ShiftedDifferenceInterlacingAnalytic
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.ColumnRecurrence

/-!
# The shifted difference interlacing claim for modified Narayana polynomials

This module combines the analytic affine-Narayana proof from the Turan development
with the endpoint-safe shifted difference-interlacing conversion, and discharges
the combinatorial inputs with the column recurrence
(`TruncatedStaircase.ColumnRecurrence`): the auxiliary recurrence
`FiniteSkewBoard.narayanaAuxiliaryGRecurrence_modified` and nonnegativity of
`G_n - G_{n-1}` (`FiniteSkewBoard.auxiliaryG_sub_hasNonnegCoeffs`).
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

open FiniteSkewBoard (narayanaAuxiliaryGRecurrence_modified auxiliaryG_sub_hasNonnegCoeffs)

/-- Root sum of the auxiliary polynomial `G_n`. -/
theorem auxiliaryG_roots_sum {n : ℕ} (hn : 2 ≤ n) :
    (FiniteSkewBoard.auxiliaryG n).roots.sum =
      -(((n : ℝ) + 1) * ((n : ℝ) - 1) / 3) := by
  have hsplit : (FiniteSkewBoard.auxiliaryG n).Splits := by
    simpa using auxiliaryGPencil_splits_of_combinatorial
      narayanaAuxiliaryGRecurrence_modified affineModifiedNarayanaInterlacing_modified
      (m := n) (lam := 0) (nu := 0) hn (by norm_num) (by norm_num)
  have hdeg :=
    auxiliaryG_natDegree_of_narayanaRecurrence narayanaAuxiliaryGRecurrence_modified n (by lia)
  have hdegpos : 0 < (FiniteSkewBoard.auxiliaryG n).natDegree := by
    rw [hdeg]
    lia
  have hlead : (FiniteSkewBoard.auxiliaryG n).leadingCoeff = (n : ℝ) := by
    rw [← Polynomial.coeff_natDegree, hdeg]
    exact auxiliaryG_coeff_sub_one_of_narayanaRecurrence
      narayanaAuxiliaryGRecurrence_modified n (by lia)
  have hnext :
      (FiniteSkewBoard.auxiliaryG n).nextCoeff =
        ((n : ℝ) + 1) * (n : ℝ) * ((n : ℝ) - 1) / 3 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos hdegpos, hdeg]
    simpa [Nat.sub_sub] using
      auxiliaryG_coeff_sub_two_of_narayanaRecurrence narayanaAuxiliaryGRecurrence_modified n hn
  have hvieta := hsplit.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [hnext, hlead] at hvieta
  apply mul_left_cancel₀ (show (n : ℝ) ≠ 0 by positivity)
  linarith

/-- The shifted difference interlacing claim for the concrete modified Narayana
family: for `m ≥ 2`, `λ ≥ 0` and `ν ≥ -1`,
`(λX + ν) G_{m-1} + G_m` strictly interlaces `(λX + ν) P_{m-1} + P_m`. -/
theorem shiftedDifferenceInterlacing_modified :
    ShiftedDifferenceInterlacing
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG :=
  shiftedDifferenceInterlacing_modified_of_combinatorial
    narayanaAuxiliaryGRecurrence_modified affineModifiedNarayanaInterlacing_modified
    fun _ hn => auxiliaryG_sub_hasNonnegCoeffs hn

/-- **The auxiliary interlacing lemma.** For `n ≥ 1`, the auxiliary polynomial
`G_n` strictly interlaces the modified Narayana polynomial `P_n`.  The case
`n = 1` is the base case; for `n ≥ 2` it is the shifted difference interlacing
claim at `λ = ν = 0`. -/
theorem auxiliaryG_strictInterl_modifiedNarayana {n : ℕ} (hn : n ≠ 0) :
    StrictInterl (FiniteSkewBoard.auxiliaryG n) (modifiedNarayanaPolynomial n) := by
  rcases eq_or_ne n 1 with rfl | hn1
  · exact auxiliaryGInterlaces_modified_base
  · simpa using shiftedDifferenceInterlacing_modified
      (m := n) (lam := 0) (nu := 0) (by lia) le_rfl (by norm_num)

/-- Consecutive auxiliary `G` polynomials have real-rooted positive linear
combinations. This is the part of adjacent `G` interlacing supplied
directly by the auxiliary recurrence and the affine Narayana interlacing lemma; orienting the
pencil remains a separate analytic step. -/
theorem auxiliaryG_posComboRealRooted {m : ℕ} (hm : 2 ≤ m) :
    PosComboRealRooted (FiniteSkewBoard.auxiliaryG (m - 1))
      (FiniteSkewBoard.auxiliaryG m) := by
  intro lam mu hlam hmu
  have hmu_ne : mu ≠ 0 := ne_of_gt hmu
  have hratio : 0 < lam / mu := div_pos hlam hmu
  let V : ℝ[X] :=
    C (lam / mu) * FiniteSkewBoard.auxiliaryG (m - 1) +
      FiniteSkewBoard.auxiliaryG m
  have hV_split : V.Splits := by
    simpa [V] using auxiliaryGPencil_splits_of_combinatorial (lam := 0)
      narayanaAuxiliaryGRecurrence_modified affineModifiedNarayanaInterlacing_modified hm
      (by positivity)
      (show -1 ≤ lam / mu by linarith)
  have hV_pos : HasPosLeadingCoeff V := by
    simpa [V] using auxiliaryGPencil_hasPosLeadingCoeff_of_narayanaRecurrence
      (lam := 0) (nu := lam / mu) narayanaAuxiliaryGRecurrence_modified hm (by positivity)
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

The hypotheses are the remaining combinatorial inputs on `M`: the snake
recurrence, nonnegative coefficients, the degree identity, and the
constant-word staircase identity.  No hypothesis assumes real-rootedness,
interlacing, or splitting.  All of them are proved for the concrete
non-nesting-rook model in `snakeInterlacing_generalizedSnakeRookModel`
(`SnakeRecurrence`). -/
theorem nonNestingRookInterlacing_modified_of_sourceInputs
    {M : SnakeWord → ℝ[X]}
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
      shiftedDifferenceInterlacing_modified)
    modifiedNarayanaPolynomial_ne_zero
    modifiedNarayanaPolynomial_interlaces_succ
    modifiedNarayanaPolynomial_one FiniteSkewBoard.auxiliaryG_one
    modifiedNarayanaPolynomial_hasNonnegCoeffs
    FiniteSkewBoard.auxiliaryG_hasNonnegCoeffs
    (fun {_m} hm => narayanaDifference_modified_hasNonnegCoeffs (by lia))
    (fun {m} hm => by
      simpa [auxiliaryDifference] using auxiliaryG_sub_hasNonnegCoeffs (n := m) (by lia))
    hM_nonneg hdeg hM_const

end GeneralizedSnakePosets
end RealRooted
