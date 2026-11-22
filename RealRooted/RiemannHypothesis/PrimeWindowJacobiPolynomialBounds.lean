/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowWeightedOrthogonal
public import RealRooted.Jacobi.Orthogonality.Integral
import RealRooted.RiemannHypothesis.PrimeWindowJacobi
import RealRooted.RiemannHypothesis.PrimeWindowJacobiBounds
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.CoefficientRates
import RealRooted.Jacobi.MomentPolynomial
import Mathlib.Tactic.Linarith

/-!
# Quantitative Jacobi limits for prime-window polynomial coefficients

For fixed nonnegative Jacobi parameters and fixed degree, RH gives a common
`O(1 / log X)` error for every coefficient of the actual weighted prime-window
polynomial. The reference is the native monic shifted Jacobi family.
-/

public section

open Filter Topology Polynomial

namespace RiemannHypothesis

/-- Under RH, every coefficient of a fixed-degree Jacobi-weighted prime-window
polynomial differs from its actual shifted Jacobi reference by at most `C / log X`. -/
theorem eventually_coeff_primeWindowWeightedPolynomial_sub_le
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ k : ℕ,
      |(Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) n).coeff k -
          (shiftedJacobiMonic n α β).coeff k| ≤ C / Real.log X := by
  obtain ⟨B, hB, hmom⟩ := hRH.eventually_primeWindowWeightedMoment_jacobi_sub_le hα hβ
  have hδ : ∀ᶠ X : ℝ in atTop, 0 ≤ B / Real.log X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact (div_pos hB (Real.log_pos hX)).le
  have herr : ∀ᶠ X : ℝ in atTop, ∀ k < 2 * n,
      |Chebyshev.primeWindowWeightedMoment (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) k -
        RealRooted.shiftedJacobiMoment α β k| ≤ B / Real.log X :=
    hmom.mono fun _ h k _ ↦ h k
  have hdet : IsUnit (momentHankelMatrix (RealRooted.shiftedJacobiMoment α β) n).det :=
    isUnit_iff_ne_zero.mpr
      (RealRooted.shiftedJacobiMoment_hankel_posDef n (by linarith) (by linarith)).det_pos.ne'
  obtain ⟨A, hA, hcoeff⟩ := eventually_coeff_monicMomentPolynomial_sub_le
    (fun k _ ↦ hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k) hdet hδ herr
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  filter_upwards [hcoeff] with X hX k
  have h := hX k
  rw [← RealRooted.shiftedJacobiMonic_eq_monicMomentPolynomial n
    (by linarith : -1 < α) (by linarith : -1 < β)] at h
  simpa only [Chebyshev.primeWindowWeightedPolynomial, mul_div_assoc] using h

end RiemannHypothesis
