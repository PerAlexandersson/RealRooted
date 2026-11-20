module

public import RealRooted.EffectiveBKW.PathCube.GeometricExpansion
public import RealRooted.EffectiveBKW.PathCube.ResidueBound
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The rational remainder for one conjugate pair and two real modes

The exact finite expansion identifies the real remainder with the two cofactor
modes. Their opposite signs give the uniform tail estimate without an analytic
infinite-series argument.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube.RationalSeries

/-- The normalized conjugate pair followed by the two real cofactor roots. -/
noncomputable def normalizedRoots (a c x y : ℝ) : Fin 4 → ℂ :=
  ![(a : ℂ) + c * Complex.I, (a : ℂ) - c * Complex.I, (x : ℂ), (y : ℂ)]

/-- A cubic numerator with real coefficients and constant coefficient one. -/
noncomputable def cubicPolynomial (u v w : ℝ) : Polynomial ℂ :=
  1 + Polynomial.C (u : ℂ) * Polynomial.X + Polynomial.C (v : ℂ) * Polynomial.X ^ 2 +
    Polynomial.C (w : ℂ) * Polynomial.X ^ 3

private theorem natDegree_cubicPolynomial_le (u v w : ℝ) :
    (cubicPolynomial u v w).natDegree ≤ 3 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      exact max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

private theorem residue_conjugate (a c x y u v w : ℝ) :
    residue (normalizedRoots a c x y) (cubicPolynomial u v w) 1 =
      starRingEnd ℂ (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0) := by
  have hconj : starRingEnd ℂ ((a : ℂ) + c * Complex.I) =
      (a : ℂ) - c * Complex.I := by simp [sub_eq_add_neg]
  simp [residue, cofactorPolynomial, cubicPolynomial, normalizedRoots, linearPolynomial,
    Fin.prod_univ_succ, hconj, map_add, map_sub, map_mul, map_pow, map_div₀]

private theorem residue_real_two {a c x y u v w : ℝ} (hx : x ≠ 0) :
    residue (normalizedRoots a c x y) (cubicPolynomial u v w) 2 =
      (realResidue a c u v w x y : ℂ) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hp : (x : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ hxC
  have hN : (cubicPolynomial u v w).eval (x : ℂ)⁻¹ * (x : ℂ) ^ 3 =
      (numeratorValue u v w x : ℂ) := by
    simp only [cubicPolynomial, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
      numeratorValue, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp
  have hC : (cofactorPolynomial (normalizedRoots a c x y) 2).eval (x : ℂ)⁻¹ *
      (x : ℂ) ^ 3 = (pairDistance a c x * (x - y) : ℝ) := by
    simp [cofactorPolynomial, normalizedRoots, linearPolynomial, Fin.prod_univ_succ]
    field_simp
    apply Complex.ext
    · simp [pairDistance, pow_two, Complex.mul_re, Complex.mul_im]
      ring
    · simp only [pairDistance, pow_two, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.I_re, Complex.I_im]
      ring
  unfold residue
  change (cubicPolynomial u v w).eval (x : ℂ)⁻¹ /
    (cofactorPolynomial (normalizedRoots a c x y) 2).eval (x : ℂ)⁻¹ = _
  rw [(eq_div_iff hp).mpr hN, (eq_div_iff hp).mpr hC,
    div_div_div_cancel_right₀ hp]
  simp [realResidue]

private theorem residue_real_three {a c x y u v w : ℝ} (hy : y ≠ 0) :
    residue (normalizedRoots a c x y) (cubicPolynomial u v w) 3 =
      (realResidue a c u v w y x : ℂ) := by
  have he : residue (normalizedRoots a c x y) (cubicPolynomial u v w) 3 =
      residue (normalizedRoots a c y x) (cubicPolynomial u v w) 2 := by
    simp [residue, cofactorPolynomial, normalizedRoots, linearPolynomial,
      Fin.prod_univ_succ]
  rw [he, residue_real_two hy]

/-- Extract the exact real remainder directly from the rational generating function. -/
theorem coeff_re_sub_pair_eq {a c x y u v w : ℝ}
    (hz : ∀ i, normalizedRoots a c x y i ≠ 0)
    (hinj : Function.Injective (normalizedRoots a c x y)) (hx : x ≠ 0) (hy : y ≠ 0)
    (p : PowerSeries ℂ)
    (hp : (denominatorPolynomial (normalizedRoots a c x y) : PowerSeries ℂ) * p =
      cubicPolynomial u v w) (n : ℕ) :
    (PowerSeries.coeff n p).re -
        2 * (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0 *
          ((a : ℂ) + c * Complex.I) ^ n).re = modeRemainder a c u v w x y n := by
  rw [coeff_eq_sum_residue_mul_pow hz hinj _ (natDegree_cubicPolynomial_le u v w) p hp n]
  simp only [Fin.sum_univ_succ]
  change (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0 *
      ((a : ℂ) + c * Complex.I) ^ n +
    (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 1 *
      ((a : ℂ) - c * Complex.I) ^ n +
    (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 2 * (x : ℂ) ^ n +
    (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 3 * (y : ℂ) ^ n + 0)))).re -
      2 * (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0 *
        ((a : ℂ) + c * Complex.I) ^ n).re = _
  rw [residue_conjugate, residue_real_two hx, residue_real_three hy]
  have hconj : ((a : ℂ) - c * Complex.I) ^ n =
      starRingEnd ℂ (((a : ℂ) + c * Complex.I) ^ n) := by simp [sub_eq_add_neg]
  have hpair :
      (starRingEnd ℂ (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0) *
        ((a : ℂ) - c * Complex.I) ^ n).re =
      (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0 *
        ((a : ℂ) + c * Complex.I) ^ n).re := by
    rw [hconj, ← map_mul]
    rfl
  simp only [Complex.add_re, hpair, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.zero_re, modeRemainder]
  ring

/-- A rational quartic series has the Phase 2 tail bound for its exact paired remainder. -/
theorem abs_coeff_re_sub_pair_le_tail {a c q x y u v w β₁ β₂ β₃ : ℝ}
    (hu : a ^ 2 + c ^ 2 = 1) (hc : 0 < c) (hq : 0 ≤ q) (hq1 : q < 1)
    (hx : 0 < x) (hy : y < 0) (hxq : |x| ≤ q) (hyq : |y| ≤ q)
    (h₁ : |u| ≤ β₁) (h₂ : |v| ≤ β₂) (h₃ : |w| ≤ β₃)
    (hz : ∀ i, normalizedRoots a c x y i ≠ 0)
    (hinj : Function.Injective (normalizedRoots a c x y))
    (p : PowerSeries ℂ)
    (hp : (denominatorPolynomial (normalizedRoots a c x y) : PowerSeries ℂ) * p =
      cubicPolynomial u v w) (k : ℕ) :
    c * |(PowerSeries.coeff (k + 1) p).re -
        2 * (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0 *
          ((a : ℂ) + c * Complex.I) ^ (k + 1)).re| ≤
      tail q [1, β₁, β₂, β₃] 2 (k + 1) := by
  rw [coeff_re_sub_pair_eq hz hinj hx.ne' hy.ne p hp]
  exact two_real_modes_le_tail hu hc hq hq1 hx hy hxq hyq h₁ h₂ h₃ k

end RealRooted.EffectiveBKW.PathCube.RationalSeries
