/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Gaussian
import RealRooted.Mathlib.LinearAlgebra.Lagrange.QuadraturePerturbation

/-!
# Quantitative convergence of Gaussian rules from finite moments

Positive finite moment systems and their actual ordered orthogonal roots give
positive Gaussian rules. A common error bound for nodes and the first moments
gives one common bound for nodes and weights. This result does not assume
quadrature exactness or positivity of the weights.
-/

public section

open Filter Topology Polynomial

namespace Lagrange

/-- Moment and node convergence, eventual positive definiteness, and a common
moment/node error bound give convergent positive Gaussian rules with one common
error constant for nodes and weights. -/
theorem eventually_gaussian_quadrature_of_moment_bounds
    {ι : Type*} {l : Filter ι} {n : ℕ} {μ : ι → ℕ → ℝ} {μ₀ : ℕ → ℝ}
    {r : Fin n → ℝ} {s : ι → Fin n → ℝ}
    (hμ : ∀ k < n, Tendsto (fun t ↦ μ t k) l (𝓝 (μ₀ k)))
    (hpos₀ : (momentHankelMatrix μ₀ n).PosDef)
    (hpos : ∀ᶠ t in l, (momentHankelMatrix (μ t) n).PosDef)
    (hr : Function.Injective r) (href : ∀ i, (monicMomentPolynomial μ₀ n).IsRoot (r i))
    (hroots : ∀ᶠ t in l, StrictMono (s t) ∧
      ∀ i, (monicMomentPolynomial (μ t) n).IsRoot (s t i))
    (hslim : ∀ i, Tendsto (fun t ↦ s t i) l (𝓝 (r i)))
    {δ : ι → ℝ} (hδ : ∀ᶠ t in l, 0 ≤ δ t)
    (hnode : ∀ᶠ t in l, ∀ i, |s t i - r i| ≤ δ t)
    (hmoment : ∀ᶠ t in l, ∀ k < n, |μ t k - μ₀ k| ≤ δ t) :
    ∃ C : ℝ, 0 < C ∧
      (∀ i, 0 < quadratureWeight (momentFunctionalLinearMap μ₀) r i) ∧
      (∀ p : ℝ[X], p.degree < (2 * n : ℕ) → momentFunctional μ₀ p =
        ∑ i : Fin n, quadratureWeight (momentFunctionalLinearMap μ₀) r i * p.eval (r i)) ∧
      (∀ᶠ t in l, StrictMono (s t) ∧
        (∀ i, (monicMomentPolynomial (μ t) n).IsRoot (s t i)) ∧
        (∀ i, 0 < quadratureWeight (momentFunctionalLinearMap (μ t)) (s t) i) ∧
        (∀ p : ℝ[X], p.degree < (2 * n : ℕ) → momentFunctional (μ t) p =
          ∑ i : Fin n, quadratureWeight (momentFunctionalLinearMap (μ t)) (s t) i *
            p.eval (s t i)) ∧
        (∀ i, |s t i - r i| ≤ C * δ t) ∧
        ∀ i, |quadratureWeight (momentFunctionalLinearMap (μ t)) (s t) i -
          quadratureWeight (momentFunctionalLinearMap μ₀) r i| ≤ C * δ t) ∧
      ∀ i, Tendsto (fun t ↦ quadratureWeight (momentFunctionalLinearMap (μ t)) (s t) i)
        l (𝓝 (quadratureWeight (momentFunctionalLinearMap μ₀) r i)) := by
  obtain ⟨M, hM, hweights⟩ :=
    eventually_abs_quadratureWeight_sub_le (momentFunctionalLinearMap μ₀) hr hslim
  have hLm : ∀ i : Fin n,
      Tendsto (fun t ↦ momentFunctionalLinearMap (μ t) (Polynomial.X ^ i.val)) l
        (𝓝 (momentFunctionalLinearMap μ₀ (Polynomial.X ^ i.val))) := by
    intro i
    simpa only [momentFunctionalLinearMap_apply, momentFunctional_X_pow] using hμ i.val i.is_lt
  have hwlim : Tendsto
      (fun t ↦ quadratureWeight (momentFunctionalLinearMap (μ t)) (s t)) l
      (𝓝 (quadratureWeight (momentFunctionalLinearMap μ₀) r)) :=
    tendsto_quadratureWeight hr hslim hLm
  refine ⟨M + 1, by linarith, ?_, ?_, ?_, ?_⟩
  · exact quadratureWeight_pos_monicMomentPolynomial μ₀ hpos₀ r hr href
  · intro p hp
    exact quadrature_exact_monicMomentPolynomial μ₀
      (isUnit_iff_ne_zero.mpr hpos₀.det_pos.ne') r hr href hp
  · filter_upwards [hpos, hroots, hweights, hδ, hnode, hmoment]
      with t hpt hrt hwt hδt hnt hmt
    have hm : ∀ i : Fin n,
        |momentFunctionalLinearMap (μ t) (Polynomial.X ^ i.val) -
          momentFunctionalLinearMap μ₀ (Polynomial.X ^ i.val)| ≤ δ t := by
      intro i
      simpa only [momentFunctionalLinearMap_apply, momentFunctional_X_pow] using hmt i.val i.is_lt
    have hweight := hwt.2 (momentFunctionalLinearMap (μ t)) (δ t) hδt hnt hm
    refine ⟨hrt.1, hrt.2, ?_, ?_, ?_, ?_⟩
    · exact quadratureWeight_pos_monicMomentPolynomial (μ t) hpt (s t) hrt.1.injective hrt.2
    · intro p hp
      exact quadrature_exact_monicMomentPolynomial (μ t)
        (isUnit_iff_ne_zero.mpr hpt.det_pos.ne') (s t) hrt.1.injective hrt.2 hp
    · intro i
      exact (hnt i).trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (by linarith : 1 ≤ M + 1) hδt)
    · intro i
      exact (hweight i).trans (mul_le_mul_of_nonneg_right (by linarith : M ≤ M + 1) hδt)
  · intro i
    exact tendsto_pi_nhds.mp hwlim i

end Lagrange
