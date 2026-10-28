/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Tactic.Ring
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs

/-!
# Nanjundiah's identity

This file proves a guarded form of Nanjundiah's binomial identity. The explicit
summation interval is important over natural numbers: outside it, truncated
subtractions can create spurious terms.
-/

public section

open Finset

namespace Nat

/-- Weighted Vandermonde convolution obtained by choosing `j` elements from
`A`, `n - j` from `B`, and then `r` marked elements among the first `j`. -/
theorem weighted_vandermonde
    (A B n r : ℕ) (hrn : r ≤ n) :
    (∑ j ∈ Finset.range (n + 1),
      Nat.choose A j * Nat.choose B (n - j) * Nat.choose j r) =
      Nat.choose A r * Nat.choose (A - r + B) (n - r) := by
  calc
    (∑ j ∈ Finset.range (n + 1),
        Nat.choose A j * Nat.choose B (n - j) * Nat.choose j r) =
        ∑ j ∈ Finset.Icc r n,
          Nat.choose A j * Nat.choose B (n - j) * Nat.choose j r := by
      symm
      apply Finset.sum_subset
      · grind
      · grind
    _ = Nat.choose A r *
        ∑ j ∈ Finset.Icc r n,
          Nat.choose (A - r) (j - r) * Nat.choose B (n - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hrj : r ≤ j := (Finset.mem_Icc.mp hj).1
      rw [mul_assoc, mul_comm (Nat.choose B (n - j)) (Nat.choose j r), ← mul_assoc,
        Nat.choose_mul hrj]
      ring
    _ = Nat.choose A r *
        ∑ s ∈ Finset.range (n - r + 1),
          Nat.choose (A - r) s * Nat.choose B (n - r - s) := by
      congr 1
      have hIcc : Finset.Icc r n = Finset.Ico r (n + 1) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        lia
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      rw [show n + 1 - r = n - r + 1 by lia]
      apply Finset.sum_congr rfl
      intro s hs
      congr 2
      · exact Nat.add_sub_cancel_left r s
      · lia
    _ = Nat.choose A r * Nat.choose (A - r + B) (n - r) := by
      have hv := Nat.add_choose_eq (A - r) B (n - r)
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
      simpa [Nat.succ_eq_add_one] using congrArg (Nat.choose A r * ·) hv.symm

private theorem nanjundiah_aux
    (A B m n x y : ℕ) (hAB : A + B = m + n)
    (hmx : m ≤ x) (hxy : x + A = m + y) :
    (∑ j ∈ Finset.range (n + 1),
      Nat.choose A j * Nat.choose B (n - j) * Nat.choose (x + j) (m + n)) =
      Nat.choose x m * Nat.choose y n := by
  calc
    (∑ j ∈ Finset.range (n + 1),
        Nat.choose A j * Nat.choose B (n - j) * Nat.choose (x + j) (m + n)) =
      ∑ j ∈ Finset.range (n + 1),
        Nat.choose A j * Nat.choose B (n - j) *
          (∑ r ∈ Finset.range (m + n + 1),
            Nat.choose j r * Nat.choose x (m + n - r)) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      have hv := Nat.add_choose_eq j x (m + n)
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
      simpa [add_comm, Nat.succ_eq_add_one] using hv
    _ = ∑ r ∈ Finset.range (m + n + 1),
        Nat.choose x (m + n - r) *
          (∑ j ∈ Finset.range (n + 1),
            Nat.choose A j * Nat.choose B (n - j) * Nat.choose j r) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ r ∈ Finset.range (n + 1),
        Nat.choose x (m + n - r) *
          (∑ j ∈ Finset.range (n + 1),
            Nat.choose A j * Nat.choose B (n - j) * Nat.choose j r) := by
      symm
      apply Finset.sum_subset
      · grind
      · intro r hrBig hrSmall
        have hzero : (∑ j ∈ Finset.range (n + 1),
            Nat.choose A j * Nat.choose B (n - j) * Nat.choose j r) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [Nat.choose_eq_zero_of_lt (by grind : j < r), mul_zero]
        rw [hzero, mul_zero]
    _ = ∑ r ∈ Finset.range (n + 1),
        Nat.choose x (m + n - r) *
          (Nat.choose A r * Nat.choose (A - r + B) (n - r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [weighted_vandermonde A B n r
        (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
    _ = Nat.choose x m *
        ∑ r ∈ Finset.range (n + 1),
          Nat.choose A r * Nat.choose (x - m) (n - r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hrn : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      by_cases hrA : r ≤ A
      · have hm : m ≤ m + n - r := by lia
        have hABr : A - r + B = m + n - r := by lia
        have hsub : m + n - r - m = n - r := by lia
        have hchoose : Nat.choose (m + n - r) (n - r) =
            Nat.choose (m + n - r) m := by
          rw [← hsub]
          exact Nat.choose_symm hm
        have hmul := Nat.choose_mul (n := x) (k := m + n - r) (s := m) hm
        rw [hsub] at hmul
        rw [hABr, hchoose]
        calc
          Nat.choose x (m + n - r) *
              (Nat.choose A r * Nat.choose (m + n - r) m) =
              Nat.choose A r *
                (Nat.choose x (m + n - r) * Nat.choose (m + n - r) m) := by ring
          _ = Nat.choose A r *
                (Nat.choose x m * Nat.choose (x - m) (n - r)) := by rw [hmul]
          _ = Nat.choose x m *
                (Nat.choose A r * Nat.choose (x - m) (n - r)) := by ring
      · have hrA' : A < r := Nat.lt_of_not_ge hrA
        rw [Nat.choose_eq_zero_of_lt hrA']
        simp
    _ = Nat.choose x m * Nat.choose y n := by
      congr 1
      have hv := Nat.add_choose_eq A (x - m) n
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
      rw [show (∑ r ∈ Finset.range (n + 1),
          Nat.choose A r * Nat.choose (x - m) (n - r)) =
          Nat.choose (A + (x - m)) n by
        simpa [Nat.succ_eq_add_one] using hv.symm]
      congr 1
      lia

/-! ### A weighted support reindexing -/

/-- Reindex a product of shifted binomial coefficients on its exact support. -/
theorem sum_range_shifted_choose_reindex
    {R : Type*} [CommSemiring R] (a b k l : ℕ)
    (hk : k ≤ a) (hl : l ≤ b) (F : ℕ → R) :
    (∑ j ∈ Finset.range (b + 1),
      (Nat.choose (b - l + k) j : R) *
        (Nat.choose (a - k + l) (b - j) : R) * F (b + k - j)) =
      ∑ i ∈ Finset.Icc (max k l) (min (a + l) (b + k)),
        (Nat.choose (a - k + l) (i - k) : R) *
          (Nat.choose (b - l + k) (i - l) : R) * F i := by
  apply Finset.sum_bij_ne_zero (fun j _ _ => b + k - j)
  · intro j hj hne
    have hjb : j ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hjB : j ≤ b - l + k := by
      by_contra h
      apply hne
      simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]
    have hbjA : b - j ≤ a - k + l := by
      by_contra h
      apply hne
      simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]
    simp only [Finset.mem_Icc, max_le_iff, le_min_iff]
    constructor <;> constructor <;> lia
  · grind
  · intro i hi hne
    simp only [Finset.mem_Icc, max_le_iff, le_min_iff] at hi
    let j := b + k - i
    have hjb : j ≤ b := by dsimp [j]; lia
    have hjB : j ≤ b - l + k := by dsimp [j]; lia
    have hmap : b + k - j = i := by dsimp [j]; lia
    have hterm :
        (Nat.choose (b - l + k) j : R) *
              (Nat.choose (a - k + l) (b - j) : R) * F (b + k - j) =
          (Nat.choose (a - k + l) (i - k) : R) *
            (Nat.choose (b - l + k) (i - l) : R) * F i := by
      rw [show i - k = b - j by dsimp [j]; lia,
        show i - l = b - l + k - j by dsimp [j]; lia, hmap, Nat.choose_symm hjB]
      ring
    refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjb), ?_, hmap⟩
    intro hz
    apply hne
    rw [← hterm]
    exact hz
  · intro j hj hne
    have hjb : j ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hjB : j ≤ b - l + k := by
      by_contra h
      apply hne
      simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]
    rw [show b + k - j - k = b - j by lia,
      show b + k - j - l = b - l + k - j by lia, Nat.choose_symm hjB]
    ring

private theorem reindex_shifted_choose_sum
    (a b k l t : ℕ) (hk : k ≤ a) (hl : l ≤ b) :
    (∑ j ∈ Finset.range (b + 1),
      Nat.choose (b - l + k) j * Nat.choose (a - k + l) (b - j) *
        Nat.choose (t + a - k + j) (a + b)) =
      ∑ i ∈ Finset.Icc (max k l) (min (a + l) (b + k)),
        Nat.choose (a - k + l) (i - k) *
          Nat.choose (b - l + k) (i - l) *
            Nat.choose (t + a + b - i) (a + b) := by
  let F : ℕ → ℕ := fun i => Nat.choose (t + a + b - i) (a + b)
  calc
    (∑ j ∈ Finset.range (b + 1),
        Nat.choose (b - l + k) j * Nat.choose (a - k + l) (b - j) *
          Nat.choose (t + a - k + j) (a + b)) =
        ∑ j ∈ Finset.range (b + 1),
          Nat.choose (b - l + k) j * Nat.choose (a - k + l) (b - j) *
            F (b + k - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjb : j ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have h3 : t + a + b - (b + k - j) = t + a - k + j := by lia
      simp only [F, h3]
    _ = ∑ i ∈ Finset.Icc (max k l) (min (a + l) (b + k)),
        Nat.choose (a - k + l) (i - k) *
          Nat.choose (b - l + k) (i - l) * F i :=
      sum_range_shifted_choose_reindex a b k l hk hl F
    _ = ∑ i ∈ Finset.Icc (max k l) (min (a + l) (b + k)),
        Nat.choose (a - k + l) (i - k) *
          Nat.choose (b - l + k) (i - l) *
            Nat.choose (t + a + b - i) (a + b) := by rfl

/-- A guarded form of Nanjundiah's binomial identity. -/
theorem shifted_choose_mul_eq_sum
    (a b k l t : ℕ) (hk : k ≤ a) (hl : l ≤ b) :
    Nat.choose (t + a - k) a * Nat.choose (t + b - l) b =
      ∑ i ∈ Finset.Icc (max k l) (min (a + l) (b + k)),
        Nat.choose (a - k + l) (i - k) *
          Nat.choose (b - l + k) (i - l) *
            Nat.choose (t + a + b - i) (a + b) := by
  by_cases hkt : k ≤ t
  · have haux := nanjundiah_aux (b - l + k) (a - k + l) a b
      (t + a - k) (t + b - l) (by lia) (by lia) (by lia)
    rw [reindex_shifted_choose_sum a b k l t hk hl] at haux
    exact haux.symm
  · have htk : t < k := Nat.lt_of_not_ge hkt
    have hleft : Nat.choose (t + a - k) a = 0 := by
      apply Nat.choose_eq_zero_of_lt
      lia
    rw [hleft, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hki : k ≤ i := le_trans (le_max_left k l) (Finset.mem_Icc.mp hi).1
    have hia : i ≤ a + l := le_trans (Finset.mem_Icc.mp hi).2 (min_le_left _ _)
    have hiab : i ≤ a + b := le_trans hia (Nat.add_le_add_left hl a)
    have htop : t + a + b - i < a + b := by lia
    rw [Nat.choose_eq_zero_of_lt htop]
    simp

end Nat
