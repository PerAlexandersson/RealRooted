/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.MeasureTheory.Measure.SqrtSymmetrization
import RealRooted.Mathlib.MeasureTheory.Measure.SqrtMoments

/-!
# Stieltjes moments and aerated Hamburger moments

A sequence has a nonnegative representing measure exactly when inserting zero
between successive entries gives moments of a real measure. The forward
measure can be chosen reflection invariant. Neither the converse nor the
equivalence assumes determinacy, finite support, or a nonzero zeroth moment.

See Sokal, arXiv:1903.12455v2, elementary fact 1.
-/

public section

namespace MeasureTheory

/-- Insert a zero between successive entries of a real moment sequence. -/
@[expose] def aeratedMoment (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then m (n / 2) else 0

/-- Even entries of an aerated moment sequence recover the original sequence. -/
@[simp] theorem aeratedMoment_even (m : ℕ → ℝ) (n : ℕ) :
    aeratedMoment m (2 * n) = m n := by
  simp [aeratedMoment, Nat.mul_comm]

/-- Odd entries of an aerated moment sequence vanish. -/
@[simp] theorem aeratedMoment_odd (m : ℕ → ℝ) (n : ℕ) :
    aeratedMoment m (2 * n + 1) = 0 := by
  simp [aeratedMoment, Nat.add_mod, Nat.mul_comm]

/-- The symmetric square-root law represents the literal aerated moment sequence. -/
theorem Measure.integral_pow_sqrtSymmetrization {mu : Measure ℝ}
    (hmu : ∀ᵐ x ∂mu, 0 ≤ x) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂mu.sqrtSymmetrization) =
      aeratedMoment (fun k => ∫ x : ℝ, x ^ k ∂mu) n := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst n
    rw [aeratedMoment_even, Measure.integral_pow_even_sqrtSymmetrization hmu]
  · subst n
    rw [aeratedMoment_odd, Measure.integral_pow_odd_sqrtSymmetrization]

/-- A nonnegative representing measure exists exactly when its aerated
sequence has a real representing measure, with every natural power integrable. -/
theorem exists_nonnegative_moments_iff_aerated (m : ℕ → ℝ) :
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, 0 ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = m n) ↔
    ∃ nu : Measure ℝ, ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) nu ∧
      (∫ x : ℝ, x ^ n ∂nu) = aeratedMoment m n := by
  constructor
  · rintro ⟨mu, hmu, hmom⟩
    have heq : (fun n => ∫ x : ℝ, x ^ n ∂mu) = m := funext fun n => (hmom n).2
    refine ⟨mu.sqrtSymmetrization, fun n =>
      ⟨Measure.integrable_pow_sqrtSymmetrization hmu (fun k => (hmom k).1) n, ?_⟩⟩
    rw [Measure.integral_pow_sqrtSymmetrization hmu, heq]
  · rintro ⟨nu, hmom⟩
    refine ⟨nu.map (fun x : ℝ => x ^ 2), ?_, fun n => ⟨?_, ?_⟩⟩
    · apply (ae_map_iff (by fun_prop) measurableSet_Ici).mpr
      exact Filter.Eventually.of_forall sq_nonneg
    · apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
      simpa only [Function.comp_def, ← pow_mul] using (hmom (2 * n)).1
    · rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
      simpa only [pow_mul, aeratedMoment_even] using (hmom (2 * n)).2

end MeasureTheory
