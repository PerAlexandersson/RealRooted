/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.EulerRecurrence
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Polynomial.Coeff
import RealRooted.IntervalDifferential.EulerNorm
import Mathlib.Tactic

/-!
# Executable coefficient tables for an Euler recurrence

We compute factorial-scaled integer coefficient rows in arrays. The soundness theorem identifies
each stored entry with the corresponding polynomial coefficient. No coefficient
rows are stored as certificate data.
-/

@[expose] public section

open Finset Polynomial

namespace RealRooted.IntervalDifferential

/-- Compute one degree-truncated Euler row from the preceding rows. -/
def eulerTableStep (H : ℕ) (support : ℕ → Finset ℕ) (cell : ℕ → ℕ → ℤ) (n : ℕ)
    (previous : Array (Array ℤ)) : Array ℤ :=
  Array.ofFn fun h : Fin (H + 1) =>
    if n < h.val then 0 else if n = 0 then if h.val = 0 then 1 else 0 else
      ∑ i ∈ range n, (((n - 1).factorial / i.factorial : ℕ) : ℤ) *
        ∑ a ∈ (support (n - i)).filter (· ≤ h.val),
        if n - i < a ∨ i < h.val - a then 0 else
        if (previous.getD i #[]).getD (h.val - a) 0 = 0 then 0 else
          cell (n - i) a * (previous.getD i #[]).getD (h.val - a) 0

/-- Memoized factorial-scaled integer rows through the indicated number of rows. -/
def eulerCoefficientTable (H : ℕ) (support : ℕ → Finset ℕ) (cell : ℕ → ℕ → ℤ) : ℕ → Array (Array ℤ)
  | 0 => #[]
  | n + 1 => let previous := eulerCoefficientTable H support cell n
      previous.push (eulerTableStep H support cell n previous)

@[simp] theorem size_eulerCoefficientTable (H : ℕ) (support : ℕ → Finset ℕ)
    (cell : ℕ → ℕ → ℤ) (n : ℕ) :
    (eulerCoefficientTable H support cell n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [eulerCoefficientTable, ih]

private theorem getD_push {α : Type*} (xs : Array α) (x d : α) (i : ℕ) :
    (xs.push x).getD i d = if i = xs.size then x else xs.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs <;> rfl

private theorem getD_eulerTableStep (H : ℕ) (support : ℕ → Finset ℕ) (cell : ℕ → ℕ → ℤ) (n : ℕ)
    (previous : Array (Array ℤ)) {h : ℕ} (hh : h ≤ H) :
    (eulerTableStep H support cell n previous).getD h 0 =
      if n < h then 0 else if n = 0 then if h = 0 then 1 else 0 else
        ∑ i ∈ range n, (((n - 1).factorial / i.factorial : ℕ) : ℤ) *
          ∑ a ∈ (support (n - i)).filter (· ≤ h),
          if n - i < a ∨ i < h - a then 0 else
          if (previous.getD i #[]).getD (h - a) 0 = 0 then 0 else
            cell (n - i) a * (previous.getD i #[]).getD (h - a) 0 := by
  simp [eulerTableStep, Array.getD_eq_getD_getElem?,
    show h < H + 1 by lia]

/-- Every entry of the executable table is the genuine Euler coefficient. -/
theorem eulerCoefficientTable_correct (H : ℕ) (support : ℕ → Finset ℕ)
    (cell : ℕ → ℕ → ℤ) (K : ℕ → ℚ[X])
    (hcell : ∀ n h, (cell n h : ℚ) = (K n).coeff h)
    (hK : ∀ i, (K i).natDegree ≤ i)
    (hsupport : ∀ i a, a ∉ support i → cell i a = 0) {N i h : ℕ} (hi : i < N) (hh : h ≤ H) :
    ((((eulerCoefficientTable H support cell N).getD i #[]).getD h 0 : ℤ) : ℚ) =
      (i.factorial : ℚ) * (PowerSeries.eulerCoeff K i).coeff h := by
  induction N generalizing i h with
  | zero => lia
  | succ N ih =>
    rw [eulerCoefficientTable, getD_push, size_eulerCoefficientTable]
    by_cases hin : i = N
    · subst i
      rw [ite_eq_left rfl, getD_eulerTableStep H support cell N _ hh]
      by_cases hNh : N < h
      · rw [ite_eq_left hNh]
        rw [coeff_eq_zero_of_natDegree_lt
          ((natDegree_eulerCoeff_le K hK N).trans_lt hNh), mul_zero]
        rfl
      · rw [ite_eq_right hNh]
        by_cases hn : N = 0
        · subst N
          rw [ite_eq_left rfl, PowerSeries.eulerCoeff_zero, coeff_one]
          norm_num
        · rw [ite_eq_right hn]
          have he := congrArg (fun p : ℚ[X] => p.coeff h)
            (PowerSeries.eulerCoeff_equation K hn)
          rw [smul_eq_C_mul, coeff_C_mul, finsetSum_coeff] at he
          simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
          simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_ite, Int.cast_zero]
          have hs : (∑ j ∈ range N,
              (((N - 1).factorial / j.factorial : ℕ) : ℚ) *
                ∑ a ∈ (support (N - j)).filter (· ≤ h),
                  if N - j < a ∨ j < h - a then 0 else
                  if ((eulerCoefficientTable H support cell N).getD j #[]).getD (h - a) 0 = 0
                    then 0 else
                    (cell (N - j) a : ℚ) *
                      (((eulerCoefficientTable H support cell N).getD j #[]).getD (h - a) 0 : ℚ)) =
              ((N - 1).factorial : ℚ) *
                ∑ j ∈ range N, ∑ a ∈ range (h + 1),
                  (K (N - j)).coeff a * (PowerSeries.eulerCoeff K j).coeff (h - a) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro j hj
            have hjN := mem_range.mp hj
            have hf : (((N - 1).factorial / j.factorial : ℕ) : ℚ) * (j.factorial : ℚ) =
                ((N - 1).factorial : ℚ) := by
              exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial (by lia : j ≤ N - 1))
            have hs : (∑ a ∈ (support (N - j)).filter (· ≤ h),
                (K (N - j)).coeff a * (PowerSeries.eulerCoeff K j).coeff (h - a)) =
                ∑ a ∈ range (h + 1),
                  (K (N - j)).coeff a * (PowerSeries.eulerCoeff K j).coeff (h - a) := by
              apply sum_subset (by intro a ha; exact mem_range.mpr (by
                have := (mem_filter.mp ha).2; lia))
              intro a ha hnot
              have hna : a ∉ support (N - j) := by
                intro he
                exact hnot (mem_filter.mpr ⟨he, by have := mem_range.mp ha; lia⟩)
              rw [← hcell, hsupport _ _ hna, Int.cast_zero, zero_mul]
            rw [← hs, mul_sum, mul_sum]
            apply sum_congr rfl
            intro a _
            by_cases hb : N - j < a ∨ j < h - a
            · rw [ite_eq_left hb, mul_zero]
              rcases hb with hb | hb
              · rw [coeff_eq_zero_of_natDegree_lt ((hK _).trans_lt hb), zero_mul, mul_zero]
              · rw [coeff_eq_zero_of_natDegree_lt
                  ((natDegree_eulerCoeff_le K hK j).trans_lt hb), mul_zero, mul_zero]
            · rw [ite_eq_right hb]
              by_cases hz : ((eulerCoefficientTable H support cell N).getD j #[]).getD (h - a) 0 = 0
              · rw [ite_eq_left hz, mul_zero]
                have hez := ih (i := j) (h := h - a) hjN ((Nat.sub_le h a).trans hh)
                rw [hz, Int.cast_zero] at hez
                have hp : (PowerSeries.eulerCoeff K j).coeff (h - a) = 0 :=
                  (mul_eq_zero.mp hez.symm).resolve_left (by positivity)
                rw [hp, mul_zero, mul_zero]
              · rw [ite_eq_right hz, hcell, ih hjN ((Nat.sub_le _ _).trans hh)]
                linear_combination (K (N - j)).coeff a *
                  (PowerSeries.eulerCoeff K j).coeff (h - a) * hf
          rw [hs, ← he]
          have hf : (N.factorial : ℚ) = (N : ℚ) * ((N - 1).factorial : ℚ) := by
            exact_mod_cast (Nat.mul_factorial_pred hn).symm
          rw [hf]
          ring
    · rw [ite_eq_right hin]
      exact ih (by lia) hh

end RealRooted.IntervalDifferential
