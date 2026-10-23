/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.CombinatorialExamples.ZigzagEulerian.Identification

/-!
# Weak alternating words and the finite centered evaluation

Appendix A.1--A.2 of the zig-zag Eulerian proof relates weak
alternating words to the centered zig-zag polynomial.  This module keeps the
word count independent of the permutation sum and proves the finite factor
evaluation used in that identification.
-/

open Polynomial Finset RealRooted.IntervalDifferential

noncomputable section

namespace RealRooted.ZigzagEulerian

/-- A weak up-down word on `n` positions with letters in `[k]`. -/
def IsWeakUpDown {n k : ℕ} (w : Fin n → Fin k) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val →
    if Even i.val then w i ≤ w j else w j ≤ w i

/-- The number `Ω_n(k)` of weak up-down words on the alphabet `[k]`.
The empty word is counted once even when `k = 0`. -/
def weakUpDownWordCount (n k : ℕ) : ℕ := by
  classical
  exact ((univ : Finset (Fin n → Fin k)).filter IsWeakUpDown).card

/-- There is exactly one empty word on every alphabet. -/
@[simp] theorem weakUpDownWordCount_zero (k : ℕ) :
    weakUpDownWordCount 0 k = 1 := by
  classical
  have h : ∀ w : Fin 0 → Fin k, IsWeakUpDown w := by
    intro w i
    exact Fin.elim0 i
  simp [weakUpDownWordCount, h]

/-- A nonempty word cannot use an empty alphabet. -/
@[simp] theorem weakUpDownWordCount_zero_alphabet (n : ℕ) (hn : 0 < n) :
    weakUpDownWordCount n 0 = 0 := by
  classical
  unfold weakUpDownWordCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro w _
  exact Fin.elim0 (w ⟨0, hn⟩)

/-- The finite weighted binomial expression from Appendix A.2, formula (A.4).
Its equality with `weakUpDownWordCount` is the fence-standardization step. -/
def zigzagBinomialWordCount (n k : ℕ) : ℕ := by
  classical
  exact ∑ π ∈ (univ : Finset (Equiv.Perm (Fin n))).filter IsUpDown,
    Nat.choose (k + n - 1 - swapCount π) n

private theorem factor_eval_odd (a b k : ℕ) (hk : a + b + 2 ≤ k) :
    ((X ^ 2 - 1) * zigzagBasis a b).eval ((2 * k + 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
        (Nat.choose (k + b + 1) (a + b + 2) : ℝ) := by
  induction a with
  | zero =>
    induction b with
    | zero =>
      have hc : Nat.choose (k + 1) 2 * 2 = (k + 1) * k := by
        simpa using Nat.choose_succ_right_eq (k + 1) 1
      have hcReal : (Nat.choose (k + 1) 2 : ℝ) * 2 = (k + 1 : ℝ) * k := by
        exact_mod_cast hc
      simp only [zero_add, zigzagBasis_zero_zero, mul_one, eval_sub,
        eval_pow, eval_X, eval_one]
      norm_num only [Nat.factorial]
      push_cast
      nlinarith [hcReal]
    | succ b ih =>
      have hk' : 0 + b + 2 ≤ k := by lia
      have h := ih hk'
      have hchoose := Nat.add_one_mul_choose_eq (k + b + 1) (b + 2)
      have hchooseReal :
          ((k + b + 2 : ℕ) : ℝ) *
              (Nat.choose (k + b + 1) (b + 2) : ℝ) =
            (Nat.choose (k + b + 2) (b + 3) : ℝ) * (b + 3 : ℝ) := by
        exact_mod_cast hchoose
      have hfactor :
          ((X ^ 2 - 1) * zigzagBasis 0 (b + 1)).eval ((2 * k + 1 : ℕ) : ℝ) =
            (2 * ((k + b + 2 : ℕ) : ℝ)) *
              ((X ^ 2 - 1) * zigzagBasis 0 b).eval ((2 * k + 1 : ℕ) : ℝ) := by
        rw [zigzagBasis_succ_right]
        simp only [eval_mul, eval_add, eval_X, eval_C]
        push_cast
        ring
      rw [hfactor, h]
      have hindex : 0 + (b + 1) + 2 = (0 + b + 2) + 1 := by lia
      calc
        2 * ((k + b + 2 : ℕ) : ℝ) *
            (2 ^ (0 + b + 2) * ((0 + b + 2).factorial : ℝ) *
              (Nat.choose (k + b + 1) (0 + b + 2) : ℝ)) =
          2 ^ (0 + b + 2) * ((0 + b + 2).factorial : ℝ) *
            (2 * (((k + b + 2 : ℕ) : ℝ) *
              (Nat.choose (k + b + 1) (b + 2) : ℝ))) := by simp only [zero_add]; ring
        _ = 2 ^ (0 + b + 2) * ((0 + b + 2).factorial : ℝ) *
            (2 * ((Nat.choose (k + b + 2) (b + 3) : ℝ) * (b + 3 : ℝ))) := by
              rw [hchooseReal]
        _ = 2 ^ (0 + (b + 1) + 2) *
            ((0 + (b + 1) + 2).factorial : ℝ) *
              (Nat.choose (k + (b + 1) + 1) (0 + (b + 1) + 2) : ℝ) := by
                conv_rhs => rw [hindex, pow_succ, Nat.factorial_succ]
                push_cast
                ring
  | succ a ih =>
    have hk' : a + b + 2 ≤ k := by lia
    have h := ih hk'
    have hchoose := Nat.choose_succ_right_eq (k + b + 1) (a + b + 2)
    have hsub : k + b + 1 - (a + b + 2) = k - a - 1 := by lia
    rw [hsub] at hchoose
    have hchooseReal :
        (Nat.choose (k + b + 1) (a + b + 3) : ℝ) * (a + b + 3 : ℝ) =
          (Nat.choose (k + b + 1) (a + b + 2) : ℝ) *
            ((k - a - 1 : ℕ) : ℝ) := by
      exact_mod_cast hchoose
    have hcast : ((k - a - 1 : ℕ) : ℝ) = (k : ℝ) - a - 1 := by
      rw [Nat.cast_sub (by lia : 1 ≤ k - a), Nat.cast_sub (by lia : a ≤ k)]
      push_cast
      ring
    have hfactor :
        ((X ^ 2 - 1) * zigzagBasis (a + 1) b).eval ((2 * k + 1 : ℕ) : ℝ) =
          (2 * ((k - a - 1 : ℕ) : ℝ)) *
            ((X ^ 2 - 1) * zigzagBasis a b).eval ((2 * k + 1 : ℕ) : ℝ) := by
      rw [zigzagBasis_succ_left]
      simp only [eval_mul, eval_sub, eval_X, eval_C]
      rw [hcast]
      push_cast
      ring
    rw [hfactor, h]
    have hindex : (a + 1) + b + 2 = (a + b + 2) + 1 := by lia
    calc
      2 * ((k - a - 1 : ℕ) : ℝ) *
          (2 ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
            (Nat.choose (k + b + 1) (a + b + 2) : ℝ)) =
        2 ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
          (2 * ((Nat.choose (k + b + 1) (a + b + 2) : ℝ) *
            ((k - a - 1 : ℕ) : ℝ))) := by ring
      _ = 2 ^ (a + b + 2) * ((a + b + 2).factorial : ℝ) *
          (2 * ((Nat.choose (k + b + 1) (a + b + 3) : ℝ) *
            (a + b + 3 : ℝ))) := by rw [← hchooseReal]
      _ = 2 ^ ((a + 1) + b + 2) *
          (((a + 1) + b + 2).factorial : ℝ) *
            (Nat.choose (k + b + 1) ((a + 1) + b + 2) : ℝ) := by
              conv_rhs => rw [hindex, pow_succ, Nat.factorial_succ]
              push_cast
              ring

/-- Appendix A.2's factor evaluation, summed over the actual up-down class.
This does not use the centered trigonometric generating series. -/
theorem zigzagCenteredQuotient_eval_odd (n k : ℕ)
    (hn : 2 ≤ n) (hk : n ≤ k) :
    (((X ^ 2 - 1) * zigzagCenteredQuotient n).eval ((2 * k + 1 : ℕ) : ℝ)) =
      (2 : ℝ) ^ n * (n.factorial : ℝ) *
        (zigzagBinomialWordCount n k : ℝ) := by
  classical
  rw [zigzagCenteredQuotient, eval_mul, eval_finsetSum, mul_sum]
  rw [zigzagBinomialWordCount, Nat.cast_sum]
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  have hd := swapCount_le_sub_two hn π
  have hindex : swapCount π + (n - 2 - swapCount π) + 2 = n := by lia
  have hb : k + (n - 2 - swapCount π) + 1 = k + n - 1 - swapCount π := by lia
  simpa only [eval_mul, hindex, hb] using
    factor_eval_odd (swapCount π) (n - 2 - swapCount π) k (by lia)

end RealRooted.ZigzagEulerian
