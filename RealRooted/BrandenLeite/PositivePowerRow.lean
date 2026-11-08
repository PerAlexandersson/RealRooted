module

import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import RealRooted.PFPolynomial
public import RealRooted.Mathlib.RingTheory.PowerSeries.AffineNegativePower
import RealRooted.BrandenLeite.WeightedDerivativeKernel
import RealRooted.BrandenLeite.PositiveLinearFactors
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDegree
import RealRooted.TotallyNonnegPencil.Checkerboard
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Positivity

/-! Real-rooted coefficient rows from weighted-kernel pencils. -/

public section

open Polynomial PowerSeries Matrix

namespace RealRooted.BrandenLeite

/-- Totally nonnegative weighted kernels with a positive constant determinant
force the canonical negative-power coefficient row to be PF. -/
theorem isPFPolynomial_affineNegativePowerCoeff_of_kernels
    (κ : ℝ) (Q B : PowerSeries ℝ) (hQ : PowerSeries.constantCoeff Q = 1)
    (hB : PowerSeries.constantCoeff B = 0) (n : ℕ)
    (hM : ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin n) (Fin n) ℝ).IsTotallyNonneg)
    (hL : ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ).IsTotallyNonneg)
    (hdet : 0 < ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin n) (Fin n) ℝ).det) :
    IsPFPolynomial (affineNegativePowerCoeff κ Q B n) := by
  have hp := hM.isPFPolynomial_det_map_add_X_smul_checkerboard hL hdet
  rw [det_weightedDerivativeKernel_affineNegativePowerCoeff κ Q B hQ hB n] at hp
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hp' := hp.const_mul (inv_pos.mpr hf)
  simpa only [← map_natCast Polynomial.C, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hf.ne', map_one, one_mul] using hp'

/-- Finite sections of the weighted kernel of a split polynomial with nonnegative
coefficients are totally nonnegative, written for the formal series of the polynomial. -/
theorem weightedDerivativeKernel_submatrix_isTotallyNonneg
    {B : ℝ[X]} (hBs : B.Splits) (hBnn : HasNonnegCoeffs B) {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) :
    ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k (B : PowerSeries ℝ))).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ).IsTotallyNonneg := by
  simpa only [Polynomial.coeff_coe] using
    ((weightedDerivativeKernel_isTotallyNonneg hBs hBnn hκ).toRect.submatrix
      (rows := (Fin.val : Fin n → ℕ)) (cols := Fin.val)
      (fun _ _ h => h) (fun _ _ h => h)).toSquare

/-- Finite sections of the signed weighted kernel of `Q`, whose reflection `Q(-X)` splits
with nonnegative coefficients, are totally nonnegative. -/
theorem weightedDerivativeKernel_submatrix_signed_isTotallyNonneg
    {Q : ℝ[X]} (hQs : (Q.comp (-Polynomial.X)).Splits)
    (hQnn : HasNonnegCoeffs (Q.comp (-Polynomial.X))) {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) :
    ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k (Q : PowerSeries ℝ))).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ).IsTotallyNonneg := by
  have hfun : (fun k => PowerSeries.coeff k ((Q.comp (-Polynomial.X) : ℝ[X]) : PowerSeries ℝ)) =
      fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k (Q : PowerSeries ℝ) := by
    funext k
    rw [Polynomial.coeff_coe, Polynomial.coeff_coe]
    exact congrFun (Polynomial.coeff_comp_neg_X_eq_neg_one_pow_mul Q) k
  simpa only [hfun] using weightedDerivativeKernel_submatrix_isTotallyNonneg hQs hQnn hκ n

/-- Split signed-denominator and numerator polynomials give the required
kernel total nonnegativity for the negative-power coefficient rows. -/
theorem isPFPolynomial_affineNegativePowerCoeff
    {κ : ℝ} (hκ : 0 ≤ κ) (Q B : ℝ[X])
    (hQ : Q.coeff 0 = 1) (hB : B.coeff 0 = 0)
    (hQs : (Q.comp (-Polynomial.X)).Splits) (hQnn : HasNonnegCoeffs (Q.comp (-Polynomial.X)))
    (hBs : B.Splits) (hBnn : HasNonnegCoeffs B) (n : ℕ)
    (hdet : 0 < ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * Q.coeff k)).submatrix Fin.val Fin.val :
        Matrix (Fin n) (Fin n) ℝ).det) :
    IsPFPolynomial (affineNegativePowerCoeff κ (Q : PowerSeries ℝ) B n) := by
  apply isPFPolynomial_affineNegativePowerCoeff_of_kernels κ Q B
    (by simpa using hQ) (by simpa using hB) n
  · exact weightedDerivativeKernel_submatrix_signed_isTotallyNonneg hQs hQnn hκ n
  · exact weightedDerivativeKernel_submatrix_isTotallyNonneg hBs hBnn hκ n
  · simpa only [Polynomial.coeff_coe] using hdet

/-- Positive real powers of a product denominator give PF coefficient rows for
any split numerator with nonnegative coefficients and zero constant term. -/
theorem isPFPolynomial_affineNegativePowerCoeff_prod_linear
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) {κ : ℝ} (hκ : 0 < κ)
    (B : ℝ[X]) (hB : B.coeff 0 = 0) (hBs : B.Splits)
    (hBnn : HasNonnegCoeffs B) (n : ℕ) :
    IsPFPolynomial (affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - Polynomial.C (α i) * Polynomial.X) : ℝ[X]) : PowerSeries ℝ)
      B n) := by
  obtain ⟨hQs, hQnn⟩ :=
    splits_and_hasNonnegCoeffs_prod_one_sub_C_mul_X_comp_neg_X s α fun i hi => (hα i hi).le
  refine isPFPolynomial_affineNegativePowerCoeff hκ.le _ B
    (Polynomial.coeff_zero_prod_one_sub_C_mul_X s α) hB hQs hQnn hBs hBnn n ?_
  rw [← Polynomial.coeff_comp_neg_X_eq_neg_one_pow_mul]
  exact det_weightedDerivativeKernel_prod_linear_comp_neg_X_pos s hs α hα hκ n

/-- The canonical positive-power rows are nonzero and split, and every root
is strictly negative. No valuation bound on the numerator is needed. -/
theorem affineNegativePowerCoeff_prod_linear_splits_and_roots_neg
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) {κ : ℝ} (hκ : 0 < κ)
    (B : ℝ[X]) (hB : B.coeff 0 = 0) (hBs : B.Splits)
    (hBnn : HasNonnegCoeffs B) (n : ℕ) :
    let q := affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - Polynomial.C (α i) * Polynomial.X) : ℝ[X]) : PowerSeries ℝ) B n
    q ≠ 0 ∧ q.Splits ∧ ∀ x ∈ q.roots, x < 0 := by
  dsimp
  have hpf := isPFPolynomial_affineNegativePowerCoeff_prod_linear s hs α hα hκ
    B hB hBs hBnn n
  have hc := PowerSeries.coeff_zero_affineNegativePowerCoeff_prod_linear_pos
    s hs α hα (B : PowerSeries ℝ) (by simpa using hB) hκ n
  rw [← Polynomial.coe_prod_one_sub_C_mul_X] at hc
  have hn : affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - Polynomial.C (α i) * Polynomial.X) : ℝ[X]) : PowerSeries ℝ)
      B n ≠ 0 := by
    intro hz
    simp only [hz, Polynomial.coeff_zero, lt_self_iff_false] at hc
  exact ⟨hn, (hpf.ne_zero_and_splits hn).2,
    roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hpf.hasNonnegCoeffs hc.ne'⟩

end RealRooted.BrandenLeite
