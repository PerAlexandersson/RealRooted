/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowWeightedOrthogonal
public import RealRooted.Jacobi.Orthogonality.Integral
import RealRooted.RiemannHypothesis.PrimeWindowJacobiPolynomial
import RealRooted.RiemannHypothesis.PrimeWindowJacobiPolynomialBounds
import RealRooted.Jacobi.RootRates
import Mathlib.Tactic.Linarith

/-!
# Quantitative Jacobi limits for weighted prime-window roots

For fixed nonnegative Jacobi parameters and fixed degree, RH produces an
eventually simple real-rooted prime-window polynomial whose ordered roots
approach the actual shifted Jacobi roots at rate `O(1 / log X)`.
No reference factorization or real-rootedness premise is supplied by the caller.
-/

public section

open Filter Topology Polynomial

namespace RiemannHypothesis

/-- RH gives an ordered family of actual Jacobi-weighted prime-window roots,
with `C / log X` error and coordinatewise convergence to the classical Jacobi roots. -/
theorem exists_primeWindowWeightedPolynomial_roots_tendsto
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∃ (r : Fin n → ℝ) (s : ℝ → Fin n → ℝ) (C : ℝ), 0 < C ∧ StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n α β).IsRoot (r i)) ∧
      (∀ᶠ X : ℝ in atTop,
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) n).Splits ∧
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) n).roots.Nodup ∧
        StrictMono (s X) ∧
        (∀ i, (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) n).IsRoot (s X i)) ∧
        ∀ i, |s X i - r i| ≤ C / Real.log X) ∧
      ∀ i, Tendsto (fun X : ℝ ↦ s X i) atTop (𝓝 (r i)) := by
  obtain ⟨B, hB, hcoeff⟩ := hRH.eventually_coeff_primeWindowWeightedPolynomial_sub_le hα hβ n
  have hδ : ∀ᶠ X : ℝ in atTop, 0 ≤ B / Real.log X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact (div_pos hB (Real.log_pos hX)).le
  have hδlim : Tendsto (fun X : ℝ ↦ B / Real.log X) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop B
  obtain ⟨r, s, A, hA, hr, href, hevent, hslim⟩ :=
    RealRooted.exists_ordered_roots_tendsto_shiftedJacobi
      (by linarith : -1 < α) (by linarith : -1 < β)
      (Filter.Eventually.of_forall fun X : ℝ ↦
        (Chebyshev.isMonicOfDegree_primeWindowWeightedPolynomial
          (RealRooted.shiftedJacobiWeight α β) X (Real.sqrt X * Real.log X ^ 3) n).natDegree_eq.le)
      (fun k _ ↦ hRH.tendsto_coeff_primeWindowWeightedPolynomial hα hβ n k)
      hδ (hcoeff.mono fun _ h k _ ↦ h k) hδlim
  refine ⟨r, s, A * B, mul_pos hA hB, hr, href, ?_, hslim⟩
  filter_upwards [hevent] with X hX
  refine ⟨hX.2.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2.1, ?_⟩
  intro i
  simpa only [mul_div_assoc] using hX.2.2.2.2.2 i

/-- The ordered root-rate conclusion without making a global choice of the
perturbed root family. Degree zero is included. -/
theorem exists_primeWindowWeightedPolynomial_roots_sub_le
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∃ r : Fin n → ℝ, StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n α β).IsRoot (r i)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) n).Splits ∧
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) n).roots.Nodup ∧
        ∃ s : Fin n → ℝ, StrictMono s ∧
          (∀ i, (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
            X (Real.sqrt X * Real.log X ^ 3) n).IsRoot (s i)) ∧
          ∀ i, |s i - r i| ≤ C / Real.log X := by
  obtain ⟨r, s, C, hC, hr, href, hevent, _⟩ :=
    hRH.exists_primeWindowWeightedPolynomial_roots_tendsto hα hβ n
  refine ⟨r, hr, href, C, hC, ?_⟩
  filter_upwards [hevent] with X hX
  exact ⟨hX.1, hX.2.1, s X, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2⟩

end RiemannHypothesis
