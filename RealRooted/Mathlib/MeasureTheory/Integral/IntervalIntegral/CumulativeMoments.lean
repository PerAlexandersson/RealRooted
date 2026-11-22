/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moments controlled by a finite cumulative-sum discrepancy

A finite weighted sum on `[0, 1]` whose cumulative sums differ from `t` by at
most `δ` has monomial moments within `2δ` of the uniform moments. The zeroth
moment has error at most `δ`. The weights may be signed and repeated nodes are
allowed, including both endpoints. No probability normalization is assumed.
-/

public section

open MeasureTheory Set

private theorem intervalIntegrable_ite_le_zero {f : ℝ → ℝ} {a b r : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t ↦ if r ≤ t then f t else 0) volume a b := by
  change IntervalIntegrable ((Ici r).indicator f) volume a b
  exact ⟨hf.1.indicator measurableSet_Ici, hf.2.indicator measurableSet_Ici⟩

private theorem integral_ite_le_zero {f : ℝ → ℝ} {a b r : ℝ}
    (hr : r ∈ Set.Icc a b) (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, if r ≤ t then f t else 0) = ∫ t in r..b, f t := by
  have hi := intervalIntegrable_ite_le_zero (r := r) hf
  have hparts := (IntervalIntegrable.trans_iff
    (a := a) (b := r) (c := b) (by
      simpa only [uIcc_of_le (hr.1.trans hr.2)] using hr)).mp hi
  have hlo : (∫ t in a..r, if r ≤ t then f t else 0) = 0 := by
    calc
      _ = ∫ _t in a..r, (0 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le hr.1 fun t ht ↦ by
          rw [ite_eq_right (not_le.mpr ht.2)]
      _ = 0 := by simp
  have hhi : (∫ t in r..b, if r ≤ t then f t else 0) = ∫ t in r..b, f t :=
    intervalIntegral.integral_congr_Ioo_of_le hr.2 fun t ht ↦ by
      rw [ite_eq_left ht.1.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals hparts.1 hparts.2, hlo, hhi, zero_add]

namespace Finset

variable {ι : Type*}

private theorem intervalIntegrable_cumulative (s : Finset ι) (r w : ι → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ ∑ i ∈ s, if r i ≤ t then w i else 0) volume a b := by
  have hi (i : ι) :
      IntervalIntegrable (fun t ↦ if r i ≤ t then w i else 0) volume a b :=
    intervalIntegrable_ite_le_zero intervalIntegrable_const
  convert IntervalIntegrable.sum s (fun i _ ↦ hi i) using 1
  ext t
  simp only [Finset.sum_apply]

/-- Integrating a finite weighted cumulative sum against a continuous function exchanges the
finite sum with the tail integrals. Signed weights and repeated nodes are allowed. -/
theorem integral_cumulative_mul (s : Finset ι) (r w : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc (0 : ℝ) 1) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, (∑ i ∈ s, if r i ≤ t then w i else 0) * g t) =
      ∑ i ∈ s, w i * ∫ t in r i..1, g t := by
  classical
  have heq : (fun t ↦ (∑ i ∈ s, if r i ≤ t then w i else 0) * g t) =
      (fun t ↦ ∑ i ∈ s, if r i ≤ t then w i * g t else 0) := by
    funext t
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [heq, intervalIntegral.integral_finsetSum (fun i _ ↦
    intervalIntegrable_ite_le_zero ((hg.intervalIntegrable 0 1).const_mul (w i)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_ite_le_zero (hr i hi) ((hg.intervalIntegrable 0 1).const_mul (w i)),
    intervalIntegral.integral_const_mul]

/-- The cumulative discrepancy at the right endpoint bounds the total-mass error.
No positivity of the weights or prior mass normalization is required. -/
theorem abs_sum_sub_one_le_of_cumulative_bound (s : Finset ι) (r w : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(∑ i ∈ s, if r i ≤ t then w i else 0) - t| ≤ δ) :
    |(∑ i ∈ s, w i) - 1| ≤ δ := by
  have heq : (∑ i ∈ s, if r i ≤ (1 : ℝ) then w i else 0) = ∑ i ∈ s, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact ite_eq_left (hr i hi).2
  simpa only [heq] using hδ 1 ⟨zero_le_one, le_rfl⟩

private theorem integral_pow_deriv (n : ℕ) (a b : ℝ) :
    (∫ t in a..b, ((n : ℝ) + 1) * t ^ n) = b ^ (n + 1) - a ^ (n + 1) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hasDerivAt_pow (n + 1) t
  · exact (continuous_const.mul (continuous_id.pow n)).intervalIntegrable a b

private theorem abs_integral_cumulative_sub_mul_le (s : Finset ι) (r w : ι → ℝ)
    {δ : ℝ} (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(∑ i ∈ s, if r i ≤ t then w i else 0) - t| ≤ δ)
    {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g t)
    (hgi : (∫ t in (0 : ℝ)..1, g t) = 1) :
    |∫ t in (0 : ℝ)..1, ((∑ i ∈ s, if r i ≤ t then w i else 0) - t) * g t| ≤ δ := by
  have hint := ((intervalIntegrable_cumulative s r w 0 1).sub
    (continuous_id.intervalIntegrable 0 1)).mul_continuousOn hg.continuousOn
  calc
    _ ≤ ∫ t in (0 : ℝ)..1,
        |((∑ i ∈ s, if r i ≤ t then w i else 0) - t) * g t| :=
      intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, δ * g t := by
      apply intervalIntegral.integral_mono_on zero_le_one hint.abs
        ((hg.intervalIntegrable 0 1).const_mul δ)
      intro t ht
      rw [abs_mul, abs_of_nonneg (hg0 t ht)]
      exact mul_le_mul_of_nonneg_right (hδ t ht) (hg0 t ht)
    _ = δ := by rw [intervalIntegral.integral_const_mul, hgi, mul_one]

private theorem abs_sum_mul_pow_succ_sub_le (s : Finset ι) (r w : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(∑ i ∈ s, if r i ≤ t then w i else 0) - t| ≤ δ) (n : ℕ) :
    |(∑ i ∈ s, w i * r i ^ (n + 1)) - 1 / ((n : ℝ) + 2)| ≤ 2 * δ := by
  let F (t : ℝ) := ∑ i ∈ s, if r i ≤ t then w i else 0
  let g (t : ℝ) := ((n : ℝ) + 1) * t ^ n
  have hg : Continuous g := continuous_const.mul (continuous_id.pow n)
  have hgi (a b : ℝ) : (∫ t in a..b, g t) = b ^ (n + 1) - a ^ (n + 1) :=
    integral_pow_deriv n a b
  have hFG : (∫ t in (0 : ℝ)..1, F t * g t) =
      (∑ i ∈ s, w i) - ∑ i ∈ s, w i * r i ^ (n + 1) := by
    have h := integral_cumulative_mul s r w hr hg
    simp_rw [hgi, one_pow, mul_sub, mul_one, Finset.sum_sub_distrib] at h
    exact h
  have hxg : (∫ t in (0 : ℝ)..1, t * g t) = 1 - 1 / ((n : ℝ) + 2) := by
    calc
      _ = ((n : ℝ) + 1) * ∫ t in (0 : ℝ)..1, t ^ (n + 1) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only [g]
        rw [pow_succ]
        ring
      _ = 1 - 1 / ((n : ℝ) + 2) := by
        rw [integral_pow]
        simp only [one_pow, zero_pow (Nat.succ_ne_zero (n + 1)), sub_zero,
          Nat.cast_add, Nat.cast_one]
        have hn : (n : ℝ) + 2 ≠ 0 := by positivity
        rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
        field_simp [hn]
        ring
  have herr : (∫ t in (0 : ℝ)..1, (F t - t) * g t) =
      (∫ t in (0 : ℝ)..1, F t * g t) - ∫ t in (0 : ℝ)..1, t * g t := by
    simp_rw [sub_mul]
    apply intervalIntegral.integral_sub
    · exact (intervalIntegrable_cumulative s r w 0 1).mul_continuousOn hg.continuousOn
    · exact (continuous_id.mul hg).intervalIntegrable 0 1
  have hidentity : (∑ i ∈ s, w i * r i ^ (n + 1)) - 1 / ((n : ℝ) + 2) =
      ((∑ i ∈ s, w i) - 1) - ∫ t in (0 : ℝ)..1, (F t - t) * g t := by
    rw [herr, hFG, hxg]
    ring
  have herror : |∫ t in (0 : ℝ)..1, (F t - t) * g t| ≤ δ :=
    abs_integral_cumulative_sub_mul_le s r w hδ hg
      (fun t ht ↦ mul_nonneg (by positivity) (pow_nonneg ht.1 _))
      (by rw [hgi]; simp)
  rw [hidentity]
  exact (abs_sub _ _).trans (by
    have hmass := abs_sum_sub_one_le_of_cumulative_bound s r w hr hδ
    linarith)

/-- Uniform cumulative discrepancy controls every monomial moment on the unit interval.
The constant `2δ` is independent of the degree. The weights may be signed, nodes may repeat,
and no total-mass normalization is assumed. -/
theorem abs_sum_mul_pow_sub_le_of_cumulative_bound (s : Finset ι) (r w : ι → ℝ)
    (hr : ∀ i ∈ s, r i ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |(∑ i ∈ s, if r i ≤ t then w i else 0) - t| ≤ δ) (k : ℕ) :
    |(∑ i ∈ s, w i * r i ^ k) - 1 / ((k : ℝ) + 1)| ≤ 2 * δ := by
  cases k with
  | zero =>
    have hmass := abs_sum_sub_one_le_of_cumulative_bound s r w hr hδ
    have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hmass
    simpa only [pow_zero, mul_one, Nat.cast_zero, zero_add, div_one] using
      hmass.trans (by linarith : δ ≤ 2 * δ)
  | succ n =>
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring] using
      abs_sum_mul_pow_succ_sub_le s r w hr hδ n

end Finset
