module

public import RealRooted.ClassicalHurwitzMatrix.Stability.Lace
public import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel
public import RealRooted.Derivative.Interlacing
import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel.Polynomial
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.FinTruncation
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import Mathlib.Tactic

/-! Finite reversal of interleaved coefficient matrices. -/

@[expose] public section

open Polynomial Matrix

namespace RealRooted

/-- Two upper Toeplitz coefficient families, interleaved as columns. -/
def upperLacePair (a b : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  fun i j ↦ if j / 2 ≤ i then
    if j % 2 = 0 then a (i - j / 2) else b (i - j / 2)
  else 0

/-- A finite upper Lace matrix is the reversal of the transpose of the lower
Lace matrix with its coefficient families exchanged. -/
theorem upperLacePair_fin_eq (a b : ℕ → ℝ) (n : ℕ) :
    (upperLacePair a b).submatrix (Fin.val : Fin n → ℕ)
      (Fin.val : Fin (2 * n) → ℕ) =
    ((lacePair b a).submatrix (Fin.val : Fin (2 * n) → ℕ)
      (Fin.val : Fin n → ℕ)).transpose.submatrix Fin.rev Fin.rev := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have hquot : (2 * n - (j.val + 1)) / 2 = n - (j.val / 2 + 1) := by lia
  have hpar : (2 * n - (j.val + 1)) % 2 = 0 ↔ j.val % 2 ≠ 0 := by lia
  have horder : n - (i.val + 1) ≤ n - (j.val / 2 + 1) ↔ j.val / 2 ≤ i.val := by lia
  have hdiff : n - (j.val / 2 + 1) - (n - (i.val + 1)) = i.val - j.val / 2 := by lia
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Fin.val_rev,
    upperLacePair, lacePair, Matrix.of_apply, toeplitz_apply, hquot, hpar,
    horder, hdiff]
  by_cases h : j.val / 2 ≤ i.val
  · by_cases hp : j.val % 2 = 0
    · simp [h, hp]
    · simp [h, hp]
  · simp [h]

/-- Total nonnegativity of the lower Lace pair controls every finite upper
Lace block. -/
theorem FullyInterlacingPair.upperLacePair_fin {a b : ℕ → ℝ}
    (h : FullyInterlacingPair b a) (n : ℕ) :
    ((upperLacePair a b).submatrix (Fin.val : Fin n → ℕ)
      (Fin.val : Fin (2 * n) → ℕ)).IsTotallyNonnegRect := by
  rw [upperLacePair_fin_eq]
  exact ((h.toRect.submatrix
    (rows := (Fin.val : Fin (2 * n) → ℕ)) (cols := (Fin.val : Fin n → ℕ))
    (fun _ _ hij ↦ hij) (fun _ _ hij ↦ hij)).transpose).finRev

/-- The finite derivative/value column family used in the kernel factorization. -/
noncomputable def derivativeValueMatrix (F : ℝ[X]) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (2 * n + 1)) ℝ :=
  (upperLacePair F.derivative.coeff F.coeff).submatrix Fin.val Fin.val

/-- Multiplying the derivative/value column family by the sparse contraction
recovers the leading weighted differential kernel. -/
theorem derivativeValueMatrix_mul_derivativeContraction (F : ℝ[X]) (n : ℕ) (κ : ℝ) :
    derivativeValueMatrix F n * Matrix.derivativeContraction n κ =
      (Matrix.weightedDerivativeKernel κ F.coeff).submatrix
        (Fin.val : Fin (n + 1) → ℕ) (Fin.val : Fin (n + 1) → ℕ) := by
  ext i j
  rw [Matrix.mul_derivativeContraction_apply]
  change
    (if 2 * j.val / 2 ≤ i.val then
      if (2 * j.val) % 2 = 0 then F.derivative.coeff (i.val - 2 * j.val / 2)
        else F.coeff (i.val - 2 * j.val / 2) else 0) * κ + _ = _
  simp only [Nat.mul_div_cancel_left _ two_pos, Nat.mul_mod_right, ite_true]
  by_cases hj : j.val = 0
  · rw [dite_eq_left hj]
    simp only [hj, Nat.zero_le, ite_true, Nat.sub_zero, add_zero]
    simp only [Matrix.submatrix_apply, hj, Matrix.weightedDerivativeKernel_apply_zero,
      Polynomial.coeff_derivative]
    push_cast
    ring
  · rw [dite_eq_right hj]
    have hq : (2 * j.val - 1) / 2 = j.val - 1 := by lia
    have hp : (2 * j.val - 1) % 2 ≠ 0 := by lia
    change (if j.val ≤ i.val then F.derivative.coeff (i.val - j.val) else 0) * κ +
      (if (2 * j.val - 1) / 2 ≤ i.val then
        if (2 * j.val - 1) % 2 = 0 then
          F.derivative.coeff (i.val - (2 * j.val - 1) / 2)
        else F.coeff (i.val - (2 * j.val - 1) / 2) else 0) * (j.val : ℝ) = _
    simp only [hq, hp, ite_false, Matrix.submatrix_apply,
      Matrix.weightedDerivativeKernel]
    by_cases hji : j.val ≤ i.val
    · rw [ite_eq_left hji, ite_eq_left (show j.val - 1 ≤ i.val by lia),
        ite_eq_left (show j.val ≤ i.val + 1 by lia), Polynomial.coeff_derivative]
      have hidx : i.val - j.val + 1 = i.val + 1 - j.val := by lia
      have hidx' : i.val - (j.val - 1) = i.val + 1 - j.val := by lia
      rw [hidx', ← hidx]
      push_cast
      ring
    · rw [ite_eq_right hji]
      by_cases hnext : j.val ≤ i.val + 1
      · have heq : j.val = i.val + 1 := by lia
        rw [ite_eq_left (show j.val - 1 ≤ i.val by lia), ite_eq_left hnext]
        have hidx : i.val - (j.val - 1) = 0 := by lia
        have hidx' : i.val + 1 - j.val = 0 := by lia
        simp only [hidx, hidx', Nat.cast_zero, mul_zero, add_zero, zero_mul, zero_add]
        exact mul_comm _ _
      · rw [ite_eq_right (show ¬j.val - 1 ≤ i.val by lia), ite_eq_right hnext]
        simp

/-- A nonconstant real-rooted polynomial with nonnegative coefficients has a
TN derivative/value coefficient matrix. -/
theorem derivativeValueMatrix_isTotallyNonnegRect {F : ℝ[X]}
    (hF : F.Splits) (hnn : HasNonnegCoeffs F) (hdeg : F.natDegree ≠ 0) (n : ℕ) :
    (derivativeValueMatrix F n).IsTotallyNonnegRect := by
  have hpair :=
    (derivative_interlaces_of_natDegree_ne_zero hF hdeg).toStrictInterl.fullyInterlacingPair
      hnn.derivative hnn
  have hU := hpair.upperLacePair_fin (n + 1)
  let cols : Fin (2 * n + 1) → Fin (2 * (n + 1)) := Fin.castLE (by lia)
  have hcols : StrictMono cols := by intro a b hab; exact hab
  have hsmall := hU.submatrix (strictMono_id) hcols
  exact hsmall


/-- Every finite weighted differential kernel of a real-rooted polynomial
with nonnegative coefficients is totally nonnegative. -/
theorem weightedDerivativeKernel_fin_isTotallyNonneg {F : ℝ[X]} (hF : F.Splits)
    (hnn : HasNonnegCoeffs F) {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) :
    ((Matrix.weightedDerivativeKernel κ F.coeff).submatrix
      (Fin.val : Fin (n + 1) → ℕ) (Fin.val : Fin (n + 1) → ℕ)).IsTotallyNonneg := by
  by_cases hdeg : F.natDegree = 0
  · have hconst := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [hconst]
    exact Matrix.weightedDerivativeKernel_C_fin_isTotallyNonneg _ _ (hnn 0) n
  · rw [← derivativeValueMatrix_mul_derivativeContraction]
    exact ((derivativeValueMatrix_isTotallyNonnegRect hF hnn hdeg n).mul
      (Matrix.derivativeContraction_isTotallyNonnegRect n hκ)).toSquare

/-- The weighted differential kernel of a real-rooted polynomial with
nonnegative coefficients is totally nonnegative for every nonnegative weight. -/
theorem weightedDerivativeKernel_isTotallyNonneg {F : ℝ[X]} (hF : F.Splits)
    (hnn : HasNonnegCoeffs F) {κ : ℝ} (hκ : 0 ≤ κ) :
    (Matrix.weightedDerivativeKernel κ F.coeff).IsTotallyNonneg := by
  apply Matrix.IsTotallyNonneg.of_fin_truncations
    (Matrix.weightedDerivativeKernel κ F.coeff)
    (fun n ↦ (Matrix.weightedDerivativeKernel κ F.coeff).submatrix
      (Fin.val : Fin (n + 1) → ℕ) (Fin.val : Fin (n + 1) → ℕ))
    (fun _ _ _ ↦ rfl)
  exact fun n ↦ weightedDerivativeKernel_fin_isTotallyNonneg hF hnn hκ n


end RealRooted
