/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Perturbation

/-!
# Error rates for all coefficients of a monic moment polynomial

A common error bound for the finite moment prefix gives a common error bound
for every polynomial coefficient near a nonsingular reference moment system.
Coefficients at or above the fixed monic degree agree identically.
-/

public section

open Filter Topology

namespace Polynomial

/-- A finite moment error rate controls every coefficient of the monic moment
polynomial. The constants depend on the fixed reference system and degree. -/
theorem eventually_coeff_monicMomentPolynomial_sub_le
    {ι : Type*} {l : Filter ι} {μ : ι → ℕ → ℝ} {μ₀ : ℕ → ℝ} {n : ℕ}
    (hμ : ∀ k < 2 * n, Tendsto (fun t ↦ μ t k) l (𝓝 (μ₀ k)))
    (hdet : IsUnit (momentHankelMatrix μ₀ n).det)
    {δ : ι → ℝ} (hδ : ∀ᶠ t in l, 0 ≤ δ t)
    (herror : ∀ᶠ t in l, ∀ k < 2 * n, |μ t k - μ₀ k| ≤ δ t) :
    ∃ C > 0, ∀ᶠ t in l, ∀ k : ℕ,
      |(monicMomentPolynomial (μ t) n).coeff k -
          (monicMomentPolynomial μ₀ n).coeff k| ≤ C * δ t := by
  obtain ⟨C, hC, hcoeff⟩ := eventually_abs_coeff_sub_monicMomentPolynomial_le hμ hdet
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcoeff, hδ, herror] with t ht hδt herr k
  by_cases hk : k < n
  · exact ht.2 (δ t) hδt herr ⟨k, hk⟩
  · have heq := (isMonicOfDegree_monicMomentPolynomial (μ t) n).coeff_eq
      (isMonicOfDegree_monicMomentPolynomial μ₀ n) (Nat.le_of_not_gt hk)
    rw [heq, sub_self, abs_zero]
    exact mul_nonneg hC.le hδt

end Polynomial
