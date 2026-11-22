/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.Analysis.Polynomial.OrderedRootRates
import RealRooted.Bezoutian.RootEvaluation
import RealRooted.Jacobi

/-!
# Quantitative ordered-root convergence at a Jacobi reference

The actual shifted Jacobi family supplies the distinct ordered real reference
roots throughout the integrable parameter range. Any polynomial family with
convergent coefficients and a vanishing coefficient error bound inherits the
same root error rate.
-/

public section

open Filter Topology Polynomial

namespace RealRooted

/-- Every monic shifted Jacobi polynomial has an increasing factorization into
its actual real roots. The degree-zero factorization is the empty product. -/
theorem exists_shiftedJacobiMonic_ordered_factorization (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    ∃ r : Fin n → ℝ, StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n α β).IsRoot (r i)) ∧
      shiftedJacobiMonic n α β = ∏ i : Fin n, (Polynomial.X - C (r i)) := by
  have hp : IsMonicOfDegree (shiftedJacobiMonic n α β) n :=
    ⟨natDegree_shiftedJacobiMonic n hα hβ, monic_shiftedJacobiMonic n hα hβ⟩
  obtain ⟨r, hr, hroots⟩ := Polynomial.exists_strictMono_roots
    (shiftedJacobiMonic_splits n hα hβ) hp.natDegree_eq
    (shiftedJacobiMonic_roots_nodup n hα hβ)
  refine ⟨r, hr, hroots, ?_⟩
  simpa only [hp.leadingCoeff_eq, map_one, one_mul] using
    Polynomial.splits_eq_C_mul_prod hp.monic.ne_zero hp.natDegree_eq r hroots hr.injective

/-- A coefficient error rate at an actual shifted Jacobi reference transfers
to one convergent family of ordered simple real roots. -/
theorem exists_ordered_roots_tendsto_shiftedJacobi
    {ι : Type*} {l : Filter ι} {Q : ι → ℝ[X]} {n : ℕ} {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (hdegree : ∀ᶠ t in l, (Q t).natDegree ≤ n)
    (hcoeff : ∀ k ≤ n,
      Tendsto (fun t ↦ (Q t).coeff k) l (𝓝 ((shiftedJacobiMonic n α β).coeff k)))
    {δ : ι → ℝ} (hδ : ∀ᶠ t in l, 0 ≤ δ t)
    (hbound : ∀ᶠ t in l, ∀ k ≤ n,
      |(Q t).coeff k - (shiftedJacobiMonic n α β).coeff k| ≤ δ t)
    (hδlim : Tendsto δ l (𝓝 0)) :
    ∃ (r : Fin n → ℝ) (s : ι → Fin n → ℝ) (C : ℝ), 0 < C ∧ StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n α β).IsRoot (r i)) ∧
      (∀ᶠ t in l, (Q t).degree = n ∧ (Q t).Splits ∧ (Q t).roots.Nodup ∧
        StrictMono (s t) ∧ (∀ i, (Q t).IsRoot (s t i)) ∧
        ∀ i, |s t i - r i| ≤ C * δ t) ∧
      ∀ i, Tendsto (fun t ↦ s t i) l (𝓝 (r i)) := by
  obtain ⟨r, hr, href, hfactor⟩ :=
    exists_shiftedJacobiMonic_ordered_factorization n hα hβ
  have hp : IsMonicOfDegree (shiftedJacobiMonic n α β) n :=
    ⟨natDegree_shiftedJacobiMonic n hα hβ, monic_shiftedJacobiMonic n hα hβ⟩
  obtain ⟨s, C, hC, hevent, hslim⟩ :=
    _root_.Polynomial.exists_ordered_roots_tendsto_of_coeff_bound hp
      (shiftedJacobiMonic_splits n hα hβ) (shiftedJacobiMonic_roots_nodup n hα hβ)
      r hr hfactor hdegree hcoeff hδ hbound hδlim
  exact ⟨r, s, C, hC, hr, href, hevent, hslim⟩

end RealRooted
