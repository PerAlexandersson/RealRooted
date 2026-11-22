/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import RealRooted.Interlacing.RootPerturbation

public import RealRooted.SimpleRoots

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment

public import RealRooted.Jacobi.Orthogonality

import RealRooted.Jacobi.MomentPolynomial
import RealRooted.Interlacing.SimplePencil
import RealRooted.Jacobi

/-!
# Cross-family stability at a Jacobi moment limit

Two independently perturbed moment functionals approaching the same Jacobi
weight give genuine strict interlacing and simple pencils eventually.
-/

public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

/-- Moment functionals approaching the same Jacobi weight independently yield
strict adjacent-degree cross-family interlacing. No positivity or splitting of
the approximating moment polynomials is assumed. -/
theorem eventually_interlaces_jacobi_moment_polynomials
    {ι : Type*} {l : Filter ι} {μ ν : ι → ℕ → ℝ} {α β : ℝ} {n : ℕ}
    (hα : -1 < α) (hβ : -1 < β)
    (hμ : ∀ k < 2 * n, Tendsto (fun t => μ t k) l (𝓝 (shiftedJacobiMoment α β k)))
    (hν : ∀ k < 2 * (n + 1),
      Tendsto (fun t => ν t k) l (𝓝 (shiftedJacobiMoment α β k))) :
    ∀ᶠ t in l, Interlaces (monicMomentPolynomial (μ t) n)
        (monicMomentPolynomial (ν t) (n + 1)) ∧
      ∀ x, (monicMomentPolynomial (μ t) n).IsRoot x →
        ¬ (monicMomentPolynomial (ν t) (n + 1)).IsRoot x := by
  have h := eventually_interlaces_of_coeff_tendsto
    (p := shiftedJacobiMonic n α β) (q := shiftedJacobiMonic (n + 1) α β)
    ⟨natDegree_shiftedJacobiMonic n hα hβ, monic_shiftedJacobiMonic n hα hβ⟩
    ⟨natDegree_shiftedJacobiMonic (n + 1) hα hβ,
      monic_shiftedJacobiMonic (n + 1) hα hβ⟩
    (shiftedJacobiMonic_strictInterl_succ n hα hβ)
    (shiftedJacobiMonic_no_common_root_succ n hα hβ)
    (P := fun t => monicMomentPolynomial (μ t) n)
    (Q := fun t => monicMomentPolynomial (ν t) (n + 1))
    (Filter.Eventually.of_forall fun t =>
      (isMonicOfDegree_monicMomentPolynomial (μ t) n).natDegree_eq.le)
    (Filter.Eventually.of_forall fun t =>
      (isMonicOfDegree_monicMomentPolynomial (ν t) (n + 1)).natDegree_eq.le)
    (fun k _ => tendsto_coeff_monicMomentPolynomial_shiftedJacobi hα hβ hμ k)
    (fun k _ => tendsto_coeff_monicMomentPolynomial_shiftedJacobi hα hβ hν k)
  exact h.mono fun _ ht => ht.2.2

/-- The same cross-family moment limits give simple real-rootedness of every
nontrivial real pencil combination, with one common eventual threshold. -/
theorem eventually_isSimpleRealRooted_jacobi_moment_pencil
    {ι : Type*} {l : Filter ι} {μ ν : ι → ℕ → ℝ} {α β : ℝ} {n : ℕ}
    (hα : -1 < α) (hβ : -1 < β)
    (hμ : ∀ k < 2 * n, Tendsto (fun t => μ t k) l (𝓝 (shiftedJacobiMoment α β k)))
    (hν : ∀ k < 2 * (n + 1),
      Tendsto (fun t => ν t k) l (𝓝 (shiftedJacobiMoment α β k))) :
    ∀ᶠ t in l, ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      IsSimpleRealRooted (C a * monicMomentPolynomial (μ t) n +
        C b * monicMomentPolynomial (ν t) (n + 1)) := by
  filter_upwards [eventually_interlaces_jacobi_moment_polynomials hα hβ hμ hν]
    with t ht
  have hp := isMonicOfDegree_monicMomentPolynomial (μ t) n
  have hq := isMonicOfDegree_monicMomentPolynomial (ν t) (n + 1)
  exact ht.1.toStrictInterl.isSimpleRealRooted_C_mul_add_C_mul
    (hasPosLeadingCoeff_of_monic hp.monic) (hasPosLeadingCoeff_of_monic hq.monic)
    (by rw [hp.natDegree_eq, hq.natDegree_eq]) ht.2

end RealRooted
