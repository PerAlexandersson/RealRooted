/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowWeightedOrthogonal
public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature
import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowWeightedQuadrature
public import RealRooted.Jacobi.Orthogonality.Integral
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.GaussianLimits
import RealRooted.RiemannHypothesis.PrimeWindowJacobiRoots
import RealRooted.RiemannHypothesis.PrimeWindowJacobi
import RealRooted.RiemannHypothesis.PrimeWindowJacobiPolynomial
import RealRooted.RiemannHypothesis.PrimeWindowJacobiBounds
import RealRooted.Jacobi.MomentPolynomial
import Mathlib.Tactic.Linarith

/-!
# Jacobi-weighted prime Gaussian quadrature under RH

For fixed nonnegative Jacobi parameters and fixed degree, the actual weighted
prime-window Gaussian rule converges to the classical Gauss-Jacobi rule for
the native beta integral. One common `C / log X` bounds both nodes and weights
of the same chosen rule. The prime masses and beta masses remain unnormalized.
-/

public section

open Filter Topology Polynomial

namespace RiemannHypothesis

/-- RH gives positive Gaussian quadrature for actual Jacobi-weighted prime sums,
converging to the actual beta-integral rule with a common node and weight rate.
The degree is fixed, both exponents are nonnegative, and degrees zero and one
are included without exceptions. -/
theorem exists_primeWindow_jacobi_gaussian_quadrature
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    let W : ℝ → ℝ := RealRooted.shiftedJacobiWeight α β
    let H : ℝ → ℝ := fun X ↦ Real.sqrt X * Real.log X ^ 3
    let L : ℝ → ℝ[X] →ₗ[ℝ] ℝ :=
      fun X ↦ momentFunctionalLinearMap (Chebyshev.primeWindowWeightedMoment W X (H X))
    let L₀ : ℝ[X] →ₗ[ℝ] ℝ :=
      momentFunctionalLinearMap (RealRooted.shiftedJacobiMoment α β)
    ∃ (r : Fin n → ℝ) (s : ℝ → Fin n → ℝ) (C : ℝ), 0 < C ∧ StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n α β).IsRoot (r i)) ∧
      (∀ i, 0 < Lagrange.quadratureWeight L₀ r i) ∧
      (∀ p : ℝ[X], p.degree < (2 * n : ℕ) →
        (∫ t : ℝ in 0..1, p.eval t * W t) =
          ∑ i : Fin n, Lagrange.quadratureWeight L₀ r i * p.eval (r i)) ∧
      (∀ᶠ X : ℝ in atTop, StrictMono (s X) ∧
        (∀ i, (Chebyshev.primeWindowWeightedPolynomial W X (H X) n).IsRoot (s X i)) ∧
        (∀ i, 0 < Lagrange.quadratureWeight (L X) (s X) i) ∧
        (∀ p : ℝ[X], p.degree < (2 * n : ℕ) →
          (∑ a ∈ Chebyshev.primeWindow X (H X),
            ((Real.log a / H X) * W (((a : ℝ) - X) / H X)) *
              p.eval (((a : ℝ) - X) / H X)) =
            ∑ i : Fin n, Lagrange.quadratureWeight (L X) (s X) i * p.eval (s X i)) ∧
        (∀ i, |s X i - r i| ≤ C / Real.log X) ∧
        ∀ i, |Lagrange.quadratureWeight (L X) (s X) i -
          Lagrange.quadratureWeight L₀ r i| ≤ C / Real.log X) ∧
      ∀ i, Tendsto (fun X : ℝ ↦ s X i) atTop (𝓝 (r i)) ∧
        Tendsto (fun X : ℝ ↦ Lagrange.quadratureWeight (L X) (s X) i) atTop
          (𝓝 (Lagrange.quadratureWeight L₀ r i)) := by
  dsimp only
  let W : ℝ → ℝ := RealRooted.shiftedJacobiWeight α β
  let H : ℝ → ℝ := fun X ↦ Real.sqrt X * Real.log X ^ 3
  let μ : ℝ → ℕ → ℝ := fun X ↦ Chebyshev.primeWindowWeightedMoment W X (H X)
  let μ₀ : ℕ → ℝ := RealRooted.shiftedJacobiMoment α β
  obtain ⟨r, s, A, hA, hr, href, hroots, hslim⟩ :=
    hRH.exists_primeWindowWeightedPolynomial_roots_tendsto hα hβ n
  obtain ⟨B, hB, hmom⟩ := hRH.eventually_primeWindowWeightedMoment_jacobi_sub_le hα hβ
  have hδ : ∀ᶠ X : ℝ in atTop, 0 ≤ (A + B) / Real.log X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    exact (div_pos (add_pos hA hB) (Real.log_pos hX)).le
  have hnode : ∀ᶠ X : ℝ in atTop, ∀ i, |s X i - r i| ≤ (A + B) / Real.log X := by
    filter_upwards [hroots, eventually_gt_atTop (1 : ℝ)] with X hX hX1 i
    exact (hX.2.2.2.2 i).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_right hB.le) (Real.log_pos hX1).le)
  have hmoment : ∀ᶠ X : ℝ in atTop, ∀ k < n, |μ X k - μ₀ k| ≤ (A + B) / Real.log X := by
    filter_upwards [hmom, eventually_gt_atTop (1 : ℝ)] with X hX hX1 k _
    exact (hX k).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_left hA.le) (Real.log_pos hX1).le)
  have href' : ∀ i, (monicMomentPolynomial μ₀ n).IsRoot (r i) := by
    intro i
    simpa only [RealRooted.shiftedJacobiMonic_eq_monicMomentPolynomial n
      (by linarith : -1 < α) (by linarith : -1 < β)] using href i
  have hroots' : ∀ᶠ X : ℝ in atTop, StrictMono (s X) ∧
      ∀ i, (monicMomentPolynomial (μ X) n).IsRoot (s X i) :=
    hroots.mono fun _ h ↦ ⟨h.2.2.1, h.2.2.2.1⟩
  obtain ⟨D, hD, hposref, hexactref, hgauss, hwlim⟩ :=
    Lagrange.eventually_gaussian_quadrature_of_moment_bounds
      (fun k _ ↦ hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k)
      (RealRooted.shiftedJacobiMoment_hankel_posDef n (by linarith) (by linarith))
      (hRH.eventually_primeWindowWeightedMoment_hankel_posDef hα hβ n)
      hr.injective href' hroots' hslim hδ hnode hmoment
  refine ⟨r, s, D * (A + B), mul_pos hD (add_pos hA hB), hr, href, hposref, ?_, ?_, ?_⟩
  · intro p hp
    calc
      (∫ t : ℝ in 0..1, p.eval t * RealRooted.shiftedJacobiWeight α β t) =
          RealRooted.shiftedJacobiFunctional α β p := by
        simpa only [RealRooted.shiftedJacobiIntegrand] using
          (RealRooted.shiftedJacobiFunctional_eq_integral
            (by linarith : -1 < α) (by linarith : -1 < β) p).symm
      _ = _ := hexactref p hp
  · filter_upwards [hgauss] with X hX
    refine ⟨hX.1, hX.2.1, hX.2.2.1, ?_, ?_, ?_⟩
    · intro p hp
      rw [← Chebyshev.momentFunctional_primeWindowWeightedMoment]
      exact hX.2.2.2.1 p hp
    · intro i
      simpa only [mul_div_assoc] using hX.2.2.2.2.1 i
    · intro i
      simpa only [mul_div_assoc] using hX.2.2.2.2.2 i
  · intro i
    exact ⟨hslim i, hwlim i⟩

end RiemannHypothesis
