/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring.RingNF

/-!
# Factorial products with multiples removed

The product of the positive integers through `N` not divisible by `r` is
`N! / (r^(N/r) (N/r)!)`. The division-free identity also covers `r = 0`.
-/

public section

open Finset

namespace Nat

/-- Separating the multiples of a stride from a factorial gives a product
identity without division. The stride may be zero. -/
theorem prod_Ioc_not_dvd_mul_pow_mul_factorial (r N : ℕ) :
    (∏ a ∈ (Ioc 0 N).filter (fun a => ¬r ∣ a), a) * r ^ (N / r) * (N / r).factorial =
      N.factorial := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hprod : (∏ a ∈ (Ioc 0 (n + 1)).filter (fun a => ¬r ∣ a), a) =
        (∏ a ∈ (Ioc 0 n).filter (fun a => ¬r ∣ a), a) *
          (if r ∣ n + 1 then 1 else n + 1) := by
      simp only [prod_filter]
      rw [prod_Ioc_succ_top (Nat.zero_le _)]
      simp only [ite_not]
    rw [hprod]
    by_cases hd : r ∣ n + 1
    · simp only [hd, ↓reduceIte, mul_one, succ_div_of_dvd hd, pow_succ, factorial_succ]
      have hm : (n / r + 1) * r = n + 1 := by
        rw [← succ_div_of_dvd hd, Nat.div_mul_cancel hd]
      calc
        _ = ((∏ a ∈ (Ioc 0 n).filter (fun a => ¬r ∣ a), a) *
            r ^ (n / r) * (n / r).factorial) * ((n / r + 1) * r) := by ring
        _ = n.factorial * (n + 1) := by rw [ih, hm]
        _ = _ := by ring
    · simp only [hd, ↓reduceIte, succ_div_of_not_dvd hd, factorial_succ]
      calc
        _ = ((∏ a ∈ (Ioc 0 n).filter (fun a => ¬r ∣ a), a) *
            r ^ (n / r) * (n / r).factorial) * (n + 1) := by ring
        _ = n.factorial * (n + 1) := by rw [ih]
        _ = _ := by ring

end Nat
