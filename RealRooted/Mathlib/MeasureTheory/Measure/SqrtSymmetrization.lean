/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Analysis.Real.Sqrt
import TauCeti.MeasureTheory.Measure.Real

/-!
# The symmetric square-root law

A measure on the nonnegative half-line lifts to a reflection-invariant measure
by taking the equally weighted positive and negative square roots. Squaring
recovers the original measure, including its atom at zero. No finiteness or
moment hypothesis is needed for these measure identities.

See Sokal, arXiv:1903.12455v2, elementary fact 1 preceding the Wall theorem proof.
-/

public section

namespace MeasureTheory.Measure

/-- The equally weighted positive and negative square-root pushforwards. -/
@[expose] noncomputable def sqrtSymmetrization (mu : Measure ℝ) : Measure ℝ :=
  (2 : NNReal)⁻¹ • (mu.map Real.sqrt + mu.map (fun x : ℝ => -Real.sqrt x))

/-- The square-root symmetrization is reflection invariant. -/
theorem map_neg_sqrtSymmetrization (mu : Measure ℝ) :
    mu.sqrtSymmetrization.map (fun x : ℝ => -x) = mu.sqrtSymmetrization := by
  rw [sqrtSymmetrization, Measure.map_smul _ (by fun_prop),
    Measure.map_add _ _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, neg_neg]
  rw [add_comm]

/-- The reflection-invariance instance for the symmetric square-root law. -/
instance sqrtSymmetrization_isNegInvariant (mu : Measure ℝ) :
    mu.sqrtSymmetrization.IsNegInvariant :=
  ⟨map_neg_sqrtSymmetrization mu⟩

/-- Squaring the symmetric square-root law recovers a nonnegative measure. -/
theorem map_sq_sqrtSymmetrization {mu : Measure ℝ} (hmu : ∀ᵐ x ∂mu, 0 ≤ x) :
    mu.sqrtSymmetrization.map (fun x : ℝ => x ^ 2) = mu := by
  have hneg : (mu.map (fun x : ℝ => -Real.sqrt x)).map (fun x : ℝ => x ^ 2) = mu := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    exact (Measure.map_congr (hmu.mono fun x hx => by
      simp only [Function.comp_def, neg_sq, Real.sq_sqrt hx, id_eq])).trans Measure.map_id
  rw [sqrtSymmetrization, Measure.map_smul _ (by fun_prop),
    Measure.map_add _ _ (by fun_prop), map_sq_map_sqrt mu hmu, hneg,
    ← two_smul NNReal mu, smul_smul]
  norm_num

/-- Among reflection-invariant measures, this is the unique lift under squaring. -/
theorem eq_sqrtSymmetrization_of_map_sq_eq {mu nu : Measure ℝ}
    (hmu : ∀ᵐ x ∂mu, 0 ≤ x) (hnu : nu.map (fun x : ℝ => -x) = nu)
    (hsq : nu.map (fun x : ℝ => x ^ 2) = mu) : nu = mu.sqrtSymmetrization := by
  apply eq_of_map_sq_eq_of_map_neg_eq_self nu mu.sqrtSymmetrization hnu
    (map_neg_sqrtSymmetrization mu)
  rw [hsq, map_sq_sqrtSymmetrization hmu]

end MeasureTheory.Measure
