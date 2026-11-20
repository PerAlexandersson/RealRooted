module

public import RealRooted.TuranHurwitz.RisingConvolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Alternating convolution of reciprocal rising factorials

Reversing the finite rising products reduces the reciprocal identity to
the formal-binomial convolution already used in part (i).
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- Reversing a finite rising product changes its starting value and contributes a sign. -/
theorem rising_reverse_mul (b : ℝ) {k j : ℕ} (hj : j ≤ k) :
    rising (1 - b - k) j * rising b (k - j) = (-1 : ℝ) ^ j * rising b k := by
  have hr : rising (1 - b - k) j =
      (-1 : ℝ) ^ j * rising (b + ((k - j : ℕ) : ℝ)) j := by
    calc
      _ = (ascPochhammer ℝ j).eval (-(b + k - 1)) := by
        congr 1
        ring
      _ = (-1 : ℝ) ^ j * (descPochhammer ℝ j).eval (b + k - 1) :=
        ascPochhammer_eval_neg_eq_descPochhammer ℝ _ _
      _ = _ := by
        rw [descPochhammer_eval_eq_ascPochhammer]
        rw [Nat.cast_sub hj]
        congr 2
        ring
  rw [hr, mul_assoc, mul_comm _ (rising b (k - j)), ← rising_add]
  rw [Nat.sub_add_cancel hj]

/-- The exact reciprocal rising-factorial convolution, valid at every even index. -/
theorem alternating_inverse_rising_convolution {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1),
      (-1 : ℝ) ^ j /
        ((j.factorial : ℝ) * ((2 * n - j).factorial : ℝ) *
          rising b j * rising b (2 * n - j))) =
      (-1 : ℝ) ^ n / ((n.factorial : ℝ) * rising b n * rising b (2 * n)) := by
  let d := 1 - b - (2 * n : ℕ)
  have hterms (j : ℕ) (hj : j ≤ 2 * n) :
      rising b (2 * n) ^ 2 *
          ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((2 * n - j).factorial : ℝ) *
            rising b j * rising b (2 * n - j))) =
        (-1 : ℝ) ^ j * (rising d j / (j.factorial : ℝ)) *
          (rising d (2 * n - j) / ((2 * n - j).factorial : ℝ)) := by
    have h₁ := rising_reverse_mul b hj
    have h₂ := rising_reverse_mul b (Nat.sub_le (2 * n) j)
    rw [Nat.sub_sub_self hj] at h₂
    have hsign : (-1 : ℝ) ^ j * (-1 : ℝ) ^ (2 * n - j) = 1 := by
      rw [← pow_add, Nat.add_sub_of_le hj]
      simp [pow_mul]
    have hprod : rising d j * rising d (2 * n - j) *
        (rising b j * rising b (2 * n - j)) = rising b (2 * n) ^ 2 := by
      calc
        _ = (rising d j * rising b (2 * n - j)) *
            (rising d (2 * n - j) * rising b j) := by ring
        _ = ((-1 : ℝ) ^ j * rising b (2 * n)) *
            ((-1 : ℝ) ^ (2 * n - j) * rising b (2 * n)) := by rw [h₁, h₂]
        _ = _ := by nlinarith [hsign]
    have hfj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hfk : ((2 * n - j).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * n - j)
    field_simp [(rising_pos hb j).ne', (rising_pos hb (2 * n - j)).ne']
    linear_combination -hprod
  have hsum : rising b (2 * n) ^ 2 *
      (∑ j ∈ Finset.range (2 * n + 1),
        (-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((2 * n - j).factorial : ℝ) *
          rising b j * rising b (2 * n - j))) = rising d n / (n.factorial : ℝ) := by
    rw [Finset.mul_sum, ← alternating_rising_convolution d n]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterms j (by simpa using Finset.mem_range.mp hj)
  have hn := rising_reverse_mul b (by lia : n ≤ 2 * n)
  have hsub : 2 * n - n = n := by lia
  rw [hsub] at hn
  have hfn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hbn := (rising_pos hb n).ne'
  have hb2n := (rising_pos hb (2 * n)).ne'
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero hfn hbn) hb2n)).mpr
  apply (mul_left_cancel₀ hb2n)
  have h := congrArg (fun r : ℝ => r * (n.factorial : ℝ)) hsum
  rw [div_mul_cancel₀ _ hfn] at h
  dsimp [d] at h
  linear_combination rising b n * h + hn

end RealRooted.TuranHurwitz
