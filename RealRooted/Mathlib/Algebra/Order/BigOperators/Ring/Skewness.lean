/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A sharp bound on skewness

This file proves the sharp third-moment bound for an equal-weight finite family of real
numbers.  The proof centers the family and sums a nonnegative cubic certificate.  Equality
is attained when one value occurs once and a second value occurs at all remaining indices.
-/

@[expose] public section

open scoped BigOperators

variable {ι : Type*}

namespace Finset

private lemma card_mul_sq_le_card_sub_one_mul_sum_sq {s : Finset ι} {f : ι → ℝ}
    (hs : 2 ≤ #s) (hf : ∑ i ∈ s, f i = 0) {i : ι} (hi : i ∈ s) :
    (#s : ℝ) * f i ^ 2 ≤ ((#s : ℝ) - 1) * ∑ j ∈ s, f j ^ 2 := by
  have hs' : (2 : ℝ) ≤ #s := by exact_mod_cast hs
  have h₁ : ((#s : ℝ) * f i) ^ 2 ≤
      ∑ j ∈ s, (((#s : ℝ) - 1) * f j + f i) ^ 2 := by
    have h := single_le_sum
      (f := fun j ↦ (((#s : ℝ) - 1) * f j + f i) ^ 2)
      (fun j _ ↦ sq_nonneg _) hi
    convert h using 2
    ring
  have h₂ : ∑ j ∈ s, (((#s : ℝ) - 1) * f j + f i) ^ 2 =
      ((#s : ℝ) - 1) ^ 2 * ∑ j ∈ s, f j ^ 2 +
        2 * ((#s : ℝ) - 1) * f i * ∑ j ∈ s, f j + (#s : ℝ) * f i ^ 2 := by
    simp only [add_sq, sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul]
    congr 1
    · congr 1
      · apply sum_congr rfl
        intro j _
        ring
      · apply sum_congr rfl
        intro j _
        ring
  rw [h₂, hf] at h₁
  nlinarith

private lemma sum_pow_three_le {s : Finset ι} {f : ι → ℝ} (hs : 2 ≤ #s)
    (hf : ∑ i ∈ s, f i = 0) (a : ℝ) (ha : 0 ≤ a)
    (h₂ : ∑ i ∈ s, f i ^ 2 = (#s : ℝ) * ((#s : ℝ) - 1) * a ^ 2) :
    ∑ i ∈ s, f i ^ 3 ≤
      (#s : ℝ) * ((#s : ℝ) - 1) * ((#s : ℝ) - 2) * a ^ 3 := by
  have hs' : (2 : ℝ) ≤ #s := by exact_mod_cast hs
  have hle : ∀ i ∈ s, f i ≤ ((#s : ℝ) - 1) * a := by
    intro i hi
    have h := card_mul_sq_le_card_sub_one_mul_sum_sq hs hf hi
    rw [h₂] at h
    have h' : f i ^ 2 ≤ (((#s : ℝ) - 1) * a) ^ 2 := by
      have : (#s : ℝ) * (f i ^ 2 - (((#s : ℝ) - 1) * a) ^ 2) ≤ 0 := by
        nlinarith
      nlinarith
    exact (abs_le_of_sq_le_sq' h' (by nlinarith)).2
  have hsum : 0 ≤ ∑ i ∈ s, (f i + a) ^ 2 * (((#s : ℝ) - 1) * a - f i) :=
    sum_nonneg fun i hi ↦ mul_nonneg (sq_nonneg _) (by linarith [hle i hi])
  have hexpand :
      ∑ i ∈ s, (f i + a) ^ 2 * (((#s : ℝ) - 1) * a - f i) =
        -∑ i ∈ s, f i ^ 3 + (((#s : ℝ) - 1) * a - 2 * a) *
          ∑ i ∈ s, f i ^ 2 +
        (2 * a * (((#s : ℝ) - 1) * a) - a ^ 2) * ∑ i ∈ s, f i +
        (#s : ℝ) * (a ^ 2 * (((#s : ℝ) - 1) * a)) := by
    rw [mul_sum, mul_sum, ← sum_neg_distrib]
    have hconst : (#s : ℝ) * (a ^ 2 * (((#s : ℝ) - 1) * a)) =
        ∑ _i ∈ s, a ^ 2 * (((#s : ℝ) - 1) * a) := by
      simp
    rw [hconst, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hexpand, hf, h₂] at hsum
  nlinarith

private lemma sq_sum_pow_three_le_of_sum_eq_zero_of_two_le {s : Finset ι}
    {f : ι → ℝ} (hs : 2 ≤ #s) (hf : ∑ i ∈ s, f i = 0) :
    (#s : ℝ) * ((#s : ℝ) - 1) * (∑ i ∈ s, f i ^ 3) ^ 2 ≤
      ((#s : ℝ) - 2) ^ 2 * (∑ i ∈ s, f i ^ 2) ^ 3 := by
  have hs' : (2 : ℝ) ≤ #s := by exact_mod_cast hs
  have hpos : 0 < (#s : ℝ) * ((#s : ℝ) - 1) := by nlinarith
  set S₂ := ∑ i ∈ s, f i ^ 2 with hS₂def
  have hS₂ : 0 ≤ S₂ := sum_nonneg fun i _ ↦ sq_nonneg _
  set a := Real.sqrt (S₂ / ((#s : ℝ) * ((#s : ℝ) - 1))) with hadef
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have haa : a ^ 2 = S₂ / ((#s : ℝ) * ((#s : ℝ) - 1)) :=
    Real.sq_sqrt (div_nonneg hS₂ hpos.le)
  have hscale : S₂ = (#s : ℝ) * ((#s : ℝ) - 1) * a ^ 2 := by
    rw [haa, mul_div_cancel₀ _ hpos.ne']
  have hu := sum_pow_three_le hs hf a ha hscale
  have hl := sum_pow_three_le (f := fun i ↦ -f i) hs (by simp [hf]) a ha (by
    simpa using hscale)
  have hneg : ∑ i ∈ s, (-f i) ^ 3 = -∑ i ∈ s, f i ^ 3 := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hneg] at hl
  have hsq : (∑ i ∈ s, f i ^ 3) ^ 2 ≤
      ((#s : ℝ) * ((#s : ℝ) - 1) * ((#s : ℝ) - 2) * a ^ 3) ^ 2 :=
    sq_le_sq' (by linarith) hu
  rw [hscale]
  have h := mul_le_mul_of_nonneg_left hsq hpos.le
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- The sharp centered third-moment inequality for an equal-weight finite family.
Equality is attained when one value occurs once and another occurs at all remaining indices. -/
theorem sq_sum_pow_three_le_of_sum_eq_zero {s : Finset ι} {f : ι → ℝ}
    (hf : ∑ i ∈ s, f i = 0) :
    (#s : ℝ) * ((#s : ℝ) - 1) * (∑ i ∈ s, f i ^ 3) ^ 2 ≤
      ((#s : ℝ) - 2) ^ 2 * (∑ i ∈ s, f i ^ 2) ^ 3 := by
  by_cases hs : 2 ≤ #s
  · exact sq_sum_pow_three_le_of_sum_eq_zero_of_two_le hs hf
  · have hs' : #s = 0 ∨ #s = 1 := by lia
    rcases hs' with hs' | hs'
    · rw [card_eq_zero.mp hs'] at hf ⊢
      simp
    · obtain ⟨i, rfl⟩ := card_eq_one.mp hs'
      simp_all

/-- The sharp division-free skewness inequality for an equal-weight finite family.
Equality is attained when one value occurs once and another occurs at all remaining indices. -/
theorem skewness_sq_le (s : Finset ι) (f : ι → ℝ) :
    ((#s : ℝ) - 1) *
        ((#s : ℝ) ^ 2 * ∑ i ∈ s, f i ^ 3 -
          3 * (#s : ℝ) * (∑ i ∈ s, f i) * (∑ i ∈ s, f i ^ 2) +
          2 * (∑ i ∈ s, f i) ^ 3) ^ 2 ≤
      ((#s : ℝ) - 2) ^ 2 *
        ((#s : ℝ) * ∑ i ∈ s, f i ^ 2 - (∑ i ∈ s, f i) ^ 2) ^ 3 := by
  by_cases hs : 2 ≤ #s
  · set n : ℝ := (#s : ℝ) with hn
    set A := ∑ i ∈ s, f i with hA
    set μ := A / n with hμ
    have hn' : (2 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hs
    have hn0 : n ≠ 0 := by positivity
    have hcenter : ∑ i ∈ s, (f i - μ) = 0 := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← hn, hμ, hA]
      field_simp
      ring
    have h₂ : n * ∑ i ∈ s, (f i - μ) ^ 2 =
        n * ∑ i ∈ s, f i ^ 2 - A ^ 2 := by
      calc
        n * ∑ i ∈ s, (f i - μ) ^ 2 =
            ∑ i ∈ s, (n * f i ^ 2 - 2 * n * μ * f i + n * μ ^ 2) := by
              rw [mul_sum]
              apply sum_congr rfl
              intro i _
              ring
        _ = n * ∑ i ∈ s, f i ^ 2 - 2 * n * μ * A + n ^ 2 * μ ^ 2 := by
          rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_const,
            nsmul_eq_mul, ← hn, hA]
          ring
        _ = n * ∑ i ∈ s, f i ^ 2 - A ^ 2 := by
          rw [hμ]
          field_simp
          ring
    have h₃ : n ^ 2 * ∑ i ∈ s, (f i - μ) ^ 3 =
        n ^ 2 * ∑ i ∈ s, f i ^ 3 -
          3 * n * A * (∑ i ∈ s, f i ^ 2) + 2 * A ^ 3 := by
      calc
        n ^ 2 * ∑ i ∈ s, (f i - μ) ^ 3 =
            ∑ i ∈ s, (n ^ 2 * f i ^ 3 - 3 * n ^ 2 * μ * f i ^ 2 +
              3 * n ^ 2 * μ ^ 2 * f i - n ^ 2 * μ ^ 3) := by
                rw [mul_sum]
                apply sum_congr rfl
                intro i _
                ring
        _ = n ^ 2 * ∑ i ∈ s, f i ^ 3 -
              3 * n ^ 2 * μ * (∑ i ∈ s, f i ^ 2) +
              3 * n ^ 2 * μ ^ 2 * A - n ^ 3 * μ ^ 3 := by
          rw [sum_sub_distrib, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
            ← mul_sum, sum_const, nsmul_eq_mul, ← hn, hA]
          ring
        _ = n ^ 2 * ∑ i ∈ s, f i ^ 3 -
              3 * n * A * (∑ i ∈ s, f i ^ 2) + 2 * A ^ 3 := by
          rw [hμ]
          field_simp
          ring
    have hb := sq_sum_pow_three_le_of_sum_eq_zero (s := s) (f := fun i ↦ f i - μ)
      hcenter
    have hn3 : 0 ≤ n ^ 3 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hb hn3
    rw [← h₂, ← h₃]
    nlinarith
  · have hs' : #s = 0 ∨ #s = 1 := by lia
    rcases hs' with hs' | hs'
    · rw [card_eq_zero.mp hs']
      norm_num
    · obtain ⟨i, rfl⟩ := card_eq_one.mp hs'
      simp

end Finset

namespace List

/-- List form of the sharp division-free skewness inequality.
Equality is attained when one entry occurs once and another fills the remaining positions. -/
theorem skewness_sq_le (l : List ℝ) :
    ((l.length : ℝ) - 1) *
        ((l.length : ℝ) ^ 2 * (l.map (· ^ 3)).sum -
          3 * (l.length : ℝ) * l.sum * (l.map (· ^ 2)).sum + 2 * l.sum ^ 3) ^ 2 ≤
      ((l.length : ℝ) - 2) ^ 2 *
        ((l.length : ℝ) * (l.map (· ^ 2)).sum - l.sum ^ 2) ^ 3 := by
  have hmap (g : ℝ → ℝ) : (l.map g).sum = ∑ i : Fin l.length, g (l.get i) := by
    exact (Fin.sum_univ_fun_getElem l g).symm
  have hpowers : ∀ k : ℕ, (l.map (· ^ k)).sum = ∑ i : Fin l.length, l.get i ^ k :=
    fun k ↦ hmap (· ^ k)
  have hsum : l.sum = ∑ i : Fin l.length, l.get i := by
    exact (Fin.sum_univ_getElem l).symm
  have h := Finset.skewness_sq_le Finset.univ (fun i : Fin l.length ↦ l.get i)
  simpa only [Finset.card_univ, Fintype.card_fin, hpowers, hsum] using h

end List
