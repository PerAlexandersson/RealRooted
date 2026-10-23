/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.CombinatorialExamples.ZigzagEulerian.WordRecurrence

/-!
# The first-maximum recurrence as a definition

We define the weak alternating word numbers by the recurrence (A.1), independently
of words and permutations. The lexicographic recursion first decreases the length,
or keeps the length fixed and decreases the alphabet. Its equality with the actual
word count in particular proves that the division by two is exact.
-/

namespace RealRooted.ZigzagEulerian

/-- Weak alternating word numbers defined by the first-maximum recurrence (A.1).
The empty row is one and every positive row starts at zero. -/
def recursiveWordCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      (2 * recursiveWordCount (n + 1) k +
        ∑ p : Fin (n + 1), recursiveWordCount p.val k * recursiveWordCount (n - p.val) (k + 1) +
        (if n + 1 = 1 then 1 else 0) +
        (if 2 ≤ n + 1 then recursiveWordCount (n - 1) (k + 1) else 0)) / 2
termination_by n k => (n, k)
decreasing_by
  · simp_wf
  · simp_wf <;> exact p.isLt
  · simp_wf <;> lia
  · simp_wf <;> lia

/-- The recursively defined numbers count actual weak up-down words. -/
theorem recursiveWordCount_eq_weakUpDownWordCount (n k : ℕ) :
    recursiveWordCount n k = weakUpDownWordCount n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    cases n with
    | zero => simp [recursiveWordCount]
    | succ n =>
      induction k with
      | zero => simp [recursiveWordCount, weakUpDownWordCount_zero_alphabet, Nat.succ_pos]
      | succ k hk =>
        rw [recursiveWordCount, hk]
        have hsum :
            (∑ p : Fin (n + 1),
              recursiveWordCount p.val k * recursiveWordCount (n - p.val) (k + 1)) =
            ∑ p ∈ Finset.range (n + 1),
              weakUpDownWordCount p k * weakUpDownWordCount (n - p) (k + 1) := by
          calc
            _ = ∑ p : Fin (n + 1),
                weakUpDownWordCount p.val k * weakUpDownWordCount (n - p.val) (k + 1) := by
              apply Finset.sum_congr rfl
              intro p _
              rw [ih p.val p.isLt k, ih (n - p.val) (by lia) (k + 1)]
            _ = _ := Fin.sum_univ_eq_sum_range _ _
        rw [hsum, ih (n - 1) (by lia) (k + 1)]
        have hrec := weakUpDownWordCount_recurrence (n + 1) k
        simp only [Nat.add_sub_cancel] at hrec
        rw [← hrec]
        exact Nat.mul_div_cancel_left _ (by decide)

/-- The division in the defining recurrence is exact. -/
theorem recursiveWordCount_recurrence (n k : ℕ) :
    2 * recursiveWordCount n (k + 1) =
      2 * recursiveWordCount n k +
        ∑ p ∈ Finset.range n,
          recursiveWordCount p k * recursiveWordCount (n - 1 - p) (k + 1) +
        (if n = 1 then 1 else 0) +
        (if 2 ≤ n then recursiveWordCount (n - 2) (k + 1) else 0) := by
  simpa only [recursiveWordCount_eq_weakUpDownWordCount] using
    weakUpDownWordCount_recurrence n k

end RealRooted.ZigzagEulerian
