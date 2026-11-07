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
  have hq := weightedDerivativeKernel_isTotallyNonneg hQs hQnn hκ
  have hb := weightedDerivativeKernel_isTotallyNonneg hBs hBnn hκ
  have hsign : (Q.comp (-Polynomial.X)).coeff = fun k => (-1 : ℝ) ^ k * Q.coeff k := by
    funext k
    rw [Polynomial.coeff_comp_neg_X, mul_comm]
  rw [hsign] at hq
  apply isPFPolynomial_affineNegativePowerCoeff_of_kernels κ Q B
    (by simpa using hQ) (by simpa using hB) n
  · simpa only [Polynomial.coeff_coe] using
      (hq.toRect.submatrix (rows := (Fin.val : Fin n → ℕ)) (cols := Fin.val)
        (fun _ _ h => h) (fun _ _ h => h)).toSquare
  · simpa only [Polynomial.coeff_coe] using
      (hb.toRect.submatrix (rows := (Fin.val : Fin n → ℕ)) (cols := Fin.val)
        (fun _ _ h => h) (fun _ _ h => h)).toSquare
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
  refine isPFPolynomial_affineNegativePowerCoeff hκ.le _ B ?_ hB ?_ ?_ hBs hBnn n ?_
  · simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  · rw [Polynomial.prod_one_sub_C_mul_X_comp_neg_X]
    exact Polynomial.splits_prod_one_add_C_mul_X s α
  · rw [Polynomial.prod_one_sub_C_mul_X_comp_neg_X]
    exact hasNonnegCoeffs_prod_one_add_C_mul_X s α (fun i hi => (hα i hi).le)
  · have hd := det_weightedDerivativeKernel_prod_linear_comp_neg_X_pos s hs α hα hκ n
    have heq :
        ((∏ i ∈ s, (1 - Polynomial.C (α i) * Polynomial.X) : ℝ[X]).comp
          (-Polynomial.X)).coeff = fun k => (-1 : ℝ) ^ k *
            (∏ i ∈ s, (1 - Polynomial.C (α i) * Polynomial.X) : ℝ[X]).coeff k := by
      funext k
      rw [Polynomial.coeff_comp_neg_X, mul_comm]
    rw [heq] at hd
    exact hd

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
