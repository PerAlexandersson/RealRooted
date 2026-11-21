/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.Identification
import RealRooted.IntervalDifferential.CenteredBasis

/-!
# Weak alternating words and the finite centered evaluation

Appendix A.1--A.2 of the zig-zag Eulerian proof relates weak
alternating words to the centered zig-zag polynomial.  This module keeps the
word count independent of the permutation sum and proves the finite factor
evaluation used in that identification.
-/

@[expose] public section

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
    zigzagBasis_eval_odd (swapCount π) (n - 2 - swapCount π) k (by lia)

end RealRooted.ZigzagEulerian
