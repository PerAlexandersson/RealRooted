/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import RealRooted.Mathlib.NumberTheory.Chebyshev.Unsmoothing
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.RieszExplicitFormula
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroKernel
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ZeroDifferenceSqrt
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.ResidualDifference
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# RH bounds for differences of the integrated Chebyshev error

Subtracting the quadratic main term from the integrated explicit formula leaves
the negative zero series and the negative logarithmic-derivative line integral.
Both endpoint series are summable and both endpoint integrands are integrable,
so the normalized differences can be moved through the sums and integrals.
The zero bound and residual bound then supply the actual RH inputs needed for
unsmoothing; no prime-counting estimate is assumed.
-/

public section

open Complex Set MeasureTheory

namespace RiemannHypothesis

private abbrev PositiveZero := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re}

private noncomputable def zeroTerm (x : ℝ) (ρ : PositiveZero) : ℂ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) * (x : ℂ) ^ ((ρ : ℂ) + 1) /
    ((ρ : ℂ) * ((ρ : ℂ) + 1))

private noncomputable def leftTerm (x t : ℝ) : ℂ :=
  let s := (9 / 20 : ℂ) + t * I
  (-logDeriv riemannZeta s) * (x : ℂ) ^ (s + 1) / (s * (s + 1))

private noncomputable def zeroDifference (y z h : ℝ) (ρ : PositiveZero) : ℂ :=
  (zeroTerm y ρ - zeroTerm z ρ) / (h : ℂ)

private noncomputable def leftDifference (y z h t : ℝ) : ℂ :=
  (leftTerm y t - leftTerm z t) / (h : ℂ)

private theorem ofReal_psiIntegralError_eq (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 1 ≤ x) :
    (Chebyshev.psiIntegralError x : ℂ) = -(∑' ρ, zeroTerm x ρ) +
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t, leftTerm x t := by
  rw [Chebyshev.psiIntegralError, ofReal_sub, ofReal_div, ofReal_pow, ofReal_ofNat,
    hRH.integral_psi_eq_main_sub_zero_sum_add_integral hx]
  dsimp only [zeroTerm, leftTerm]
  ring

private theorem ofReal_error_difference_eq (hRH : RiemannHypothesis)
    {y z : ℝ} (hy : 1 ≤ y) (hz : 1 ≤ z) (h : ℝ) :
    (((Chebyshev.psiIntegralError y - Chebyshev.psiIntegralError z) / h : ℝ) : ℂ) =
      -(∑' ρ, zeroDifference y z h ρ) +
        (2 * (Real.pi : ℂ))⁻¹ * ∫ t, leftDifference y z h t := by
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hsy : Summable (zeroTerm y) := hRH.summable_riemannZeta_order_mul_cpow_div hy0
  have hsz : Summable (zeroTerm z) := hRH.summable_riemannZeta_order_mul_cpow_div hz0
  have hiy : Integrable (leftTerm y) := (hRH.integrable_riesz_vertical_edges hy0).2
  have hiz : Integrable (leftTerm z) := (hRH.integrable_riesz_vertical_edges hz0).2
  rw [ofReal_div, ofReal_sub, ofReal_psiIntegralError_eq hRH hy,
    ofReal_psiIntegralError_eq hRH hz]
  simp_rw [zeroDifference, leftDifference]
  rw [tsum_div_const, Summable.tsum_sub hsy hsz, integral_div, integral_sub hiy hiz]
  ring

private theorem zero_difference_norm_bound {C x y z : ℝ}
    (hbound :
      let f := fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re} ↦
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) *
          (((y : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) * ((ρ : ℂ) + 1)) -
            (z : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) * ((ρ : ℂ) + 1))) / (Real.sqrt x : ℂ))
      Summable (fun ρ ↦ ‖f ρ‖) ∧ (∑' ρ, ‖f ρ‖) ≤ C * (Real.sqrt x * Real.log x ^ 2)) :
    ‖∑' ρ, zeroDifference y z (Real.sqrt x) ρ‖ ≤ C * (Real.sqrt x * Real.log x ^ 2) := by
  have heq (ρ : PositiveZero) : zeroDifference y z (Real.sqrt x) ρ =
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) *
        (((y : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) * ((ρ : ℂ) + 1)) -
          (z : ℂ) ^ ((ρ : ℂ) + 1) / ((ρ : ℂ) * ((ρ : ℂ) + 1))) / (Real.sqrt x : ℂ)) := by
    dsimp [zeroDifference, zeroTerm]
    ring
  simp_rw [heq]
  exact (norm_tsum_le_tsum_norm hbound.1).trans hbound.2

private theorem left_difference_norm_bound {C x y z : ℝ}
    (hbound :
      let g := fun t : ℝ ↦
        let s := (9 / 20 : ℂ) + t * I
        logDeriv riemannZeta s * (((y : ℂ) ^ (s + 1) / (s * (s + 1)) -
          (z : ℂ) ^ (s + 1) / (s * (s + 1))) / (Real.sqrt x : ℂ))
      Integrable g ∧ ‖∫ t, g t‖ ≤ C * Real.sqrt x) :
    ‖∫ t, leftDifference y z (Real.sqrt x) t‖ ≤ C * Real.sqrt x := by
  have heq : (fun t ↦ leftDifference y z (Real.sqrt x) t) =
      (fun t : ℝ ↦
        let s := (9 / 20 : ℂ) + t * I
        (-(logDeriv riemannZeta s * (((y : ℂ) ^ (s + 1) / (s * (s + 1)) -
          (z : ℂ) ^ (s + 1) / (s * (s + 1))) / (Real.sqrt x : ℂ))))) := by
    funext t
    dsimp [leftDifference, leftTerm]
    ring
  rw [heq, integral_neg, norm_neg]
  exact hbound.2

/-- Mathlib's RH bounds square-root-step differences of the actual integrated Chebyshev
error by `C sqrt(x) log(x)^2`, uniformly in a multiplicative neighborhood. -/
theorem exists_abs_psiIntegralError_sqrt_difference_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y z : ℝ, 25 ≤ x →
      y ∈ Icc (x / 2) (2 * x) → z ∈ Icc (x / 2) (2 * x) → |y - z| ≤ Real.sqrt x →
      |(Chebyshev.psiIntegralError y - Chebyshev.psiIntegralError z) / Real.sqrt x| ≤
        C * (Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨Cz, hCz, hzero⟩ := hRH.exists_tsum_norm_riemannZeta_sqrt_difference_le
  obtain ⟨Ci, hCi, hint⟩ := hRH.exists_norm_integral_logDeriv_sqrt_difference_le
  let P : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖
  have hP : 0 ≤ P := norm_nonneg _
  refine ⟨Cz + P * Ci, by positivity, fun x y z hx hy hz hyz ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hz1 : 1 ≤ z := by linarith [hz.1]
  have hzsum := zero_difference_norm_bound (hzero x y z hx hy hz hyz)
  have hiint := left_difference_norm_bound (hint x y z hx0 hy hz hyz)
  have hlog : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr (by linarith [Real.exp_one_lt_three])
  have hsqrt : Real.sqrt x ≤ Real.sqrt x * Real.log x ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (by nlinarith : 1 ≤ Real.log x ^ 2) (Real.sqrt_nonneg x)
  calc
    |(Chebyshev.psiIntegralError y - Chebyshev.psiIntegralError z) / Real.sqrt x| =
        ‖(((Chebyshev.psiIntegralError y - Chebyshev.psiIntegralError z) /
          Real.sqrt x : ℝ) : ℂ)‖ := by
      rw [norm_real, Real.norm_eq_abs]
    _ = ‖-(∑' ρ, zeroDifference y z (Real.sqrt x) ρ) +
        (2 * (Real.pi : ℂ))⁻¹ * ∫ t, leftDifference y z (Real.sqrt x) t‖ := by
      rw [ofReal_error_difference_eq hRH hy1 hz1]
    _ ≤ ‖∑' ρ, zeroDifference y z (Real.sqrt x) ρ‖ +
        P * ‖∫ t, leftDifference y z (Real.sqrt x) t‖ := by
      simpa only [norm_neg, norm_mul, P] using norm_add_le
        (-(∑' ρ, zeroDifference y z (Real.sqrt x) ρ))
        ((2 * (Real.pi : ℂ))⁻¹ * ∫ t, leftDifference y z (Real.sqrt x) t)
    _ ≤ Cz * (Real.sqrt x * Real.log x ^ 2) + P * (Ci * Real.sqrt x) :=
      add_le_add hzsum (mul_le_mul_of_nonneg_left hiint hP)
    _ ≤ Cz * (Real.sqrt x * Real.log x ^ 2) + P * (Ci * (Real.sqrt x * Real.log x ^ 2)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsqrt hCi.le) hP)
    _ = (Cz + P * Ci) * (Real.sqrt x * Real.log x ^ 2) := by ring

/-- The preceding neighborhood bound supplies both actual square-root difference hypotheses
needed by the unconditional Chebyshev unsmoothing theorem. -/
theorem exists_psiIntegralError_sqrt_bounds (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, 25 ≤ x →
        |(Chebyshev.psiIntegralError x - Chebyshev.psiIntegralError (x - Real.sqrt x)) /
          Real.sqrt x| ≤
          C * (Real.sqrt x * Real.log x ^ 2)) ∧
      (∀ x : ℝ, 25 ≤ x →
        |(Chebyshev.psiIntegralError (x + Real.sqrt x) - Chebyshev.psiIntegralError x) /
          Real.sqrt x| ≤
          C * (Real.sqrt x * Real.log x ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := hRH.exists_abs_psiIntegralError_sqrt_difference_le
  have hstep (x : ℝ) (hx : 25 ≤ x) : 0 ≤ Real.sqrt x ∧ Real.sqrt x ≤ x / 2 := by
    refine ⟨Real.sqrt_nonneg x, ?_⟩
    apply (Real.sqrt_le_left (by linarith : 0 ≤ x / 2)).mpr
    nlinarith [sq_nonneg (x - 3)]
  refine ⟨C, hC, ?_, ?_⟩
  · intro x hx
    obtain ⟨hs0, hs⟩ := hstep x hx
    apply hbound x x (x - Real.sqrt x) hx
    · constructor <;> linarith
    · constructor <;> linarith
    · rw [sub_sub_cancel, abs_of_nonneg hs0]
  · intro x hx
    obtain ⟨hs0, hs⟩ := hstep x hx
    apply hbound x (x + Real.sqrt x) x hx
    · constructor <;> linarith
    · constructor <;> linarith
    · rw [add_sub_cancel_left, abs_of_nonneg hs0]

end RiemannHypothesis
