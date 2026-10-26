/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Upper-index Vandermonde convolution

`∑_{i + j = n} C(i, r) C(j, m) = C(n + 1, r + m + 1)`: choose an `(r + m + 1)`-subset of
`{0, …, n}` and split it at its `(r + 1)`-st smallest element `i`.  The case `m = 0` is the
hockey-stick identity `Nat.sum_Icc_choose`.  The proof (induction on `n` with Pascal's rule) was
found by Aristotle (Harmonic).
-/

@[expose] public section

open Finset

namespace Nat

private theorem sum_range_choose_mul_choose_aux (r : ℕ) :
    ∀ k m : ℕ, ∑ i ∈ range k, i.choose r * (k - 1 - i).choose m = k.choose (m + 1 + r) := by
  intro k
  induction k with
  | zero => intro m; simp [Nat.choose_eq_zero_of_lt (show 0 < m + 1 + r by lia)]
  | succ k ih =>
    intro m
    cases m with
    | zero =>
      rw [sum_range_succ]
      have h := ih 0
      simp only [Nat.choose_zero_right, mul_one] at h ⊢
      rw [h, show 0 + 1 + r = r + 1 by lia, Nat.choose_succ_succ', add_comm]
    | succ m =>
      rw [sum_range_succ, show k + 1 - 1 - k = 0 by lia, Nat.choose_zero_succ, mul_zero,
        add_zero]
      have hs : ∀ i ∈ range k, i.choose r * (k + 1 - 1 - i).choose (m + 1)
          = i.choose r * (k - 1 - i).choose (m + 1) + i.choose r * (k - 1 - i).choose m := by
        intro i hi
        rw [mem_range] at hi
        rw [show k + 1 - 1 - i = (k - 1 - i) + 1 by lia, Nat.choose_succ_succ', mul_add,
          add_comm]
      rw [sum_congr rfl hs, sum_add_distrib, ih (m + 1), ih m,
        show m + 1 + 1 + r = (m + 1 + r) + 1 by lia, Nat.choose_succ_succ', add_comm]

/-- Upper-index Vandermonde convolution, range form:
`∑_{i ≤ n} C(i, r) C(n - i, m) = C(n + 1, r + m + 1)`. -/
theorem sum_range_succ_choose_mul_choose (n r m : ℕ) :
    ∑ i ∈ range (n + 1), i.choose r * (n - i).choose m = (n + 1).choose (r + m + 1) := by
  rw [show r + m + 1 = m + 1 + r by lia]
  simpa using sum_range_choose_mul_choose_aux r (n + 1) m

/-- Upper-index Vandermonde convolution:
`∑_{i + j = n} C(i, r) C(j, m) = C(n + 1, r + m + 1)`. -/
theorem sum_antidiagonal_choose_mul_choose (n r m : ℕ) :
    ∑ ij ∈ antidiagonal n, ij.1.choose r * ij.2.choose m = (n + 1).choose (r + m + 1) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_range_succ_choose_mul_choose n r m

end Nat
