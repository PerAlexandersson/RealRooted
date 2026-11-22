/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Jacobi.Orthogonality.Integral

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowWeightedOrthogonal
import RealRooted.RiemannHypothesis.PrimeWindowJacobi
import RealRooted.Jacobi.MomentPolynomial
import RealRooted.Mathlib.Analysis.Asymptotics.IncrementBounds
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Perturbation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith

/-!
# Jacobi limits for weighted prime-window polynomials

For fixed nonnegative Jacobi exponents, RH supplies the prime-window moment
limits. The finite Hankel construction then converges to the classical monic
Jacobi polynomial and is eventually genuinely orthogonal in the weighted sum.
The algebraic moment construction and classical Jacobi properties are unconditional.
-/

public section

open Filter Topology Polynomial

namespace RiemannHypothesis

/-- Under RH, every coefficient of a fixed-degree Jacobi-weighted prime-window
polynomial tends to its classical monic shifted Jacobi coefficient. -/
theorem tendsto_coeff_primeWindowWeightedPolynomial (hRH : RiemannHypothesis)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n k : ℕ) :
    Tendsto (fun X : ℝ ↦
      (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
        X (Real.sqrt X * Real.log X ^ 3) n).coeff k)
      atTop (𝓝 ((shiftedJacobiMonic n α β).coeff k)) := by
  exact RealRooted.tendsto_coeff_monicMomentPolynomial_shiftedJacobi
    (by linarith) (by linarith)
    (fun j _ ↦ hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ j) k

/-- RH makes every fixed finite Jacobi-weighted prime-window moment matrix
eventually nonsingular. Empty and small windows are not asserted nonsingular. -/
theorem eventually_primeWindowWeightedMoment_hankel_isUnit
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      IsUnit (momentHankelMatrix
        (Chebyshev.primeWindowWeightedMoment (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3)) n).det := by
  have hdet : IsUnit (momentHankelMatrix (RealRooted.shiftedJacobiMoment α β) n).det :=
    isUnit_iff_ne_zero.mpr
      (RealRooted.shiftedJacobiMoment_hankel_posDef n (by linarith) (by linarith)).det_pos.ne'
  obtain ⟨_, _, hbound⟩ := eventually_isUnit_momentHankelMatrix_det_and_inv_bound
    (n := n) (fun k _ ↦ hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k) hdet
  exact hbound.mono fun _ h ↦ h.1

/-- Under RH the actual nonnegative Jacobi-weighted prime-window moment matrix
is eventually positive definite in every fixed size, including the empty size. -/
theorem eventually_primeWindowWeightedMoment_hankel_posDef
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      (momentHankelMatrix
        (Chebyshev.primeWindowWeightedMoment (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3)) n).PosDef := by
  filter_upwards [hRH.eventually_primeWindowWeightedMoment_hankel_isUnit hα hβ n,
    Real.eventually_sqrt_mul_log_cube_pos_le] with X hdet hH
  have hW : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ RealRooted.shiftedJacobiWeight α β x := by
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg hx.1 α) (Real.rpow_nonneg (sub_nonneg.mpr hx.2) β)
  have hpsd := Chebyshev.primeWindowWeightedMoment_hankel_posSemidef (X := X) hH.1 hW n
  exact hpsd.posDef_iff_det_ne_zero.mpr (isUnit_iff_ne_zero.mp hdet)

/-- The RH limiting argument supplies genuine eventual orthogonality for the
constructed weighted prime polynomial. The pairing is the finite weighted prime
sum by `Chebyshev.momentPairing_primeWindowWeightedMoment`. -/
theorem eventually_primeWindowWeightedPolynomial_orthogonal
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ p : ℝ[X], p.degree < n →
      momentPairing
        (Chebyshev.primeWindowWeightedMoment (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3)) p
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) n) = 0 := by
  filter_upwards [hRH.eventually_primeWindowWeightedMoment_hankel_isUnit hα hβ n]
    with X hdet p hp
  exact momentPairing_monicMomentPolynomial _ n hdet hp

end RiemannHypothesis
