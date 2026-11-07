module

public import RealRooted.BrandenLeite.PositivePowerRow
import RealRooted.TotallyNonnegPencil.CheckerboardInterlacing
import RealRooted.Interlacing.ReversalCommonFactor
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-! # Valuation-one negative-power coefficient row interlacing -/

public section

open Polynomial PowerSeries Matrix

namespace RealRooted.BrandenLeite

/-- A numerator series with zero constant coefficient has a lower triangular
weighted derivative kernel. -/
theorem weightedDerivativeKernel_isLowerTriangular_fin
    (κ : ℝ) (B : PowerSeries ℝ) (hB : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ).IsLowerTriangular := by
  intro i j hij
  change i.val < j.val at hij
  have hB₀ : PowerSeries.coeff 0 B = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hB
  simp only [Matrix.submatrix_apply, weightedDerivativeKernel]
  split_ifs with h
  · have hidx : i.val + 1 - j.val = 0 := by lia
    rw [hidx, hB₀, mul_zero]
  · rfl

/-- A positive exponent and positive first numerator coefficient give positive
determinants of every finite numerator kernel section. -/
theorem det_weightedDerivativeKernel_fin_pos_of_coeff_one_pos
    {κ : ℝ} (hκ : 0 < κ) (B : PowerSeries ℝ)
    (hB : PowerSeries.constantCoeff B = 0) (hB₁ : 0 < PowerSeries.coeff 1 B)
    (n : ℕ) :
    0 < ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ).det := by
  rw [Matrix.det_of_isLowerTriangular _
    (weightedDerivativeKernel_isLowerTriangular_fin κ B hB n)]
  apply Finset.prod_pos
  intro i _
  have hidx : i.val + 1 - i.val = 1 := by lia
  simp only [Matrix.submatrix_apply, weightedDerivativeKernel,
    show i.val ≤ i.val + 1 by lia, ite_true, hidx, Nat.cast_one, mul_one]
  exact mul_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hκ) hB₁

/-- TN signed denominator and numerator kernels force consecutive canonical
rows to interlace when the numerator has valuation one.

Both rows have their full degrees `n` and `n+1`; no reflection of the row
variable is required, since the pencil uses `M + t checkerboard(L)`. -/
theorem interlaces_affineNegativePowerCoeff_succ_of_kernels
    {κ : ℝ} (hκ : 0 < κ) (Q B : PowerSeries ℝ)
    (hQ : PowerSeries.constantCoeff Q = 1) (hB : PowerSeries.constantCoeff B = 0)
    (hB₁ : 0 < PowerSeries.coeff 1 B) (n : ℕ)
    (hM : ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).IsTotallyNonneg)
    (hL : ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
      Fin.val Fin.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).IsTotallyNonneg) :
    Interlaces (affineNegativePowerCoeff κ Q B n)
      (affineNegativePowerCoeff κ Q B (n + 1)) := by
  have hi := Matrix.IsLowerTriangular.leading_det_map_add_X_smul_checkerboard_interlaces
    (weightedDerivativeKernel_isLowerTriangular_fin κ B hB (n + 1)) hL
      (det_weightedDerivativeKernel_fin_pos_of_coeff_one_pos hκ B hB hB₁ (n + 1)) hM
  change Interlaces
    (Matrix.det ((((weightedDerivativeKernel κ
        (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix
          Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ).map Polynomial.C) +
      (Polynomial.X : ℝ[X]) • (checkerboard
        ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
          Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ)).map Polynomial.C))
    (Matrix.det ((((weightedDerivativeKernel κ
        (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix
          Fin.val Fin.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).map Polynomial.C) +
      (Polynomial.X : ℝ[X]) • (checkerboard
        ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
          Fin.val Fin.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).map Polynomial.C)) at hi
  rw [det_weightedDerivativeKernel_affineNegativePowerCoeff κ Q B hQ hB n,
    det_weightedDerivativeKernel_affineNegativePowerCoeff κ Q B hQ hB (n + 1)] at hi
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hfs : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hi' := hi.C_mul_both (inv_ne_zero hf) (inv_ne_zero hfs)
  simpa only [← map_natCast Polynomial.C, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hf, inv_mul_cancel₀ hfs, map_one, one_mul] using hi'

/-- The same canonical valuation-one conclusion in the oriented zero-aware
interlacing relation used by coefficient-limit closure. -/
theorem interl_affineNegativePowerCoeff_succ_of_kernels
    {κ : ℝ} (hκ : 0 < κ) (Q B : PowerSeries ℝ)
    (hQ : PowerSeries.constantCoeff Q = 1) (hB : PowerSeries.constantCoeff B = 0)
    (hB₁ : 0 < PowerSeries.coeff 1 B) (n : ℕ)
    (hM : ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).IsTotallyNonneg)
    (hL : ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
      Fin.val Fin.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).IsTotallyNonneg) :
    Interl (affineNegativePowerCoeff κ Q B n)
      (affineNegativePowerCoeff κ Q B (n + 1)) :=
  (interlaces_affineNegativePowerCoeff_succ_of_kernels
    hκ Q B hQ hB hB₁ n hM hL).toStrictInterl.toInterl

/-- Split signed-denominator and numerator polynomials give consecutive
negative-power row interlacing when the numerator has a simple zero at zero. -/
theorem interlaces_affineNegativePowerCoeff_succ
    {κ : ℝ} (hκ : 0 < κ) (Q B : ℝ[X])
    (hQ : Q.coeff 0 = 1) (hB : B.coeff 0 = 0) (hB₁ : 0 < B.coeff 1)
    (hQs : (Q.comp (-Polynomial.X)).Splits)
    (hQnn : HasNonnegCoeffs (Q.comp (-Polynomial.X)))
    (hBs : B.Splits) (hBnn : HasNonnegCoeffs B) (n : ℕ) :
    Interlaces (affineNegativePowerCoeff κ (Q : PowerSeries ℝ) B n)
      (affineNegativePowerCoeff κ (Q : PowerSeries ℝ) B (n + 1)) := by
  have hq := weightedDerivativeKernel_isTotallyNonneg hQs hQnn hκ.le
  have hb := weightedDerivativeKernel_isTotallyNonneg hBs hBnn hκ.le
  have hsign : (Q.comp (-Polynomial.X)).coeff = fun k => (-1 : ℝ) ^ k * Q.coeff k := by
    funext k
    rw [Polynomial.coeff_comp_neg_X, mul_comm]
  rw [hsign] at hq
  apply interlaces_affineNegativePowerCoeff_succ_of_kernels hκ Q B
    (by simpa using hQ) (by simpa using hB) (by simpa using hB₁) n
  · simpa only [Polynomial.coeff_coe] using
      (hq.toRect.submatrix (rows := (Fin.val : Fin (n + 1) → ℕ)) (cols := Fin.val)
        (fun _ _ h => h) (fun _ _ h => h)).toSquare
  · simpa only [Polynomial.coeff_coe] using
      (hb.toRect.submatrix (rows := (Fin.val : Fin (n + 1) → ℕ)) (cols := Fin.val)
        (fun _ _ h => h) (fun _ _ h => h)).toSquare

end RealRooted.BrandenLeite
