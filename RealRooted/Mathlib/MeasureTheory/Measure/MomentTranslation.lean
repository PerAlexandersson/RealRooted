/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.MomentTranslation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Function.PolynomialMemLp

/-!
# Translation of representing moment measures

Pushforward by addition realizes the binomial transform of a moment sequence.
Every real translation is allowed. Support bounds translate with the same
parameter; preservation of nonnegative support needs a nonnegative shift.
The zero measure is included and no mass normalization is imposed.

See Sokal and Walrad, arXiv:2404.12131v1, equation (7) and the opening of the
proof of Theorem 2.
-/

public section

open Polynomial

namespace MeasureTheory

/-- All polynomial moments remain integrable after any real translation. -/
theorem integrable_pow_map_add {mu : Measure ℝ}
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu) (c : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (mu.map fun x => x + c) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  apply (TauCeti.integrable_eval_of_forall_integrable_pow hmom ((X + C c) ^ n)).congr
  filter_upwards [] with x
  simp only [Function.comp_def, eval_pow, eval_add, eval_X, eval_C]

/-- The power moments of a translated measure are the binomial transform. -/
theorem integral_pow_map_add {mu : Measure ℝ}
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu) (c : ℝ) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂(mu.map fun x => x + c)) =
      momentTranslate c (fun k => ∫ x : ℝ, x ^ k ∂mu) n := by
  rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop),
    momentTranslate_eq_sum]
  simp_rw [add_pow]
  rw [integral_finsetSum _ fun k _ =>
    ((hmom k).mul_const (c ^ (n - k))).mul_const (n.choose k : ℝ)]
  simp only [integral_mul_const]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A lower support bound moves by the same amount as the measure. -/
theorem ae_add_le_map_add_iff (mu : Measure ℝ) (a c : ℝ) :
    (∀ᵐ x ∂(mu.map fun y => y + c), a + c ≤ x) ↔ ∀ᵐ x ∂mu, a ≤ x := by
  rw [ae_map_iff (by fun_prop) measurableSet_Ici]
  simp

/-- Both endpoints of a compact support interval translate by the same amount. -/
theorem ae_mem_Icc_map_add_iff (mu : Measure ℝ) (a b c : ℝ) :
    (∀ᵐ x ∂(mu.map fun y => y + c), x ∈ Set.Icc (a + c) (b + c)) ↔
      ∀ᵐ x ∂mu, x ∈ Set.Icc a b := by
  simp only [Set.mem_Icc]
  rw [ae_map_iff (by fun_prop) measurableSet_Icc]
  simp

/-- A nonnegative translation preserves nonnegative support. -/
theorem ae_nonneg_map_add {mu : Measure ℝ} {c : ℝ}
    (hmu : ∀ᵐ x ∂mu, 0 ≤ x) (hc : 0 ≤ c) :
    ∀ᵐ x ∂(mu.map fun y => y + c), 0 ≤ x := by
  rw [ae_map_iff (by fun_prop) measurableSet_Ici]
  filter_upwards [hmu] with x hx
  exact add_nonneg hx hc

/-- Subtracting a lower support endpoint reduces its moment problem to the
nonnegative half-line. This equivalence includes zero measures. -/
theorem exists_measure_moments_Ici_iff (m : ℕ → ℝ) (c : ℝ) :
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = m n) ↔
    (∃ mu : Measure ℝ, (∀ᵐ x ∂mu, 0 ≤ x) ∧
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = momentTranslate (-c) m n) := by
  constructor
  · rintro ⟨mu, hsupp, hmom⟩
    have hi : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu := fun n => (hmom n).1
    have heq : (fun n => ∫ x : ℝ, x ^ n ∂mu) = m := funext fun n => (hmom n).2
    refine ⟨mu.map (fun x => x + -c), ?_, fun n => ⟨integrable_pow_map_add hi (-c) n, ?_⟩⟩
    · simpa only [add_neg_cancel] using (ae_add_le_map_add_iff mu c (-c)).mpr hsupp
    · rw [integral_pow_map_add hi, heq]
  · rintro ⟨mu, hsupp, hmom⟩
    have hi : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu := fun n => (hmom n).1
    have heq : (fun n => ∫ x : ℝ, x ^ n ∂mu) = momentTranslate (-c) m :=
      funext fun n => (hmom n).2
    refine ⟨mu.map (fun x => x + c), ?_, fun n => ⟨integrable_pow_map_add hi c n, ?_⟩⟩
    · simpa only [zero_add] using (ae_add_le_map_add_iff mu 0 c).mpr hsupp
    · rw [integral_pow_map_add hi, heq, momentTranslate_neg_cancel_right]

end MeasureTheory
