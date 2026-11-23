/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Binomial

/-!
# Reciprocal rising-factorial convolution

The finite Chu--Vandermonde identity gives a Gamma-free convolution of
reciprocal rising factorials. The numerator is a finite polynomial even when
the corresponding Gamma ratio has a removable singularity.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R]

/-- The reciprocal rising-factorial convolution, with no Gamma poles. -/
theorem sum_choose_mul_inv_ascPochhammer {a b : R} (n : ℕ)
    (ha : (ascPochhammer R n).eval a ≠ 0)
    (hb : (ascPochhammer R n).eval b ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : R) *
      ((ascPochhammer R k).eval a)⁻¹ *
      ((ascPochhammer R (n - k)).eval b)⁻¹) =
    (ascPochhammer R n).eval (a + b + n - 1) /
      ((ascPochhammer R n).eval a * (ascPochhammer R n).eval b) := by
  apply (eq_div_iff (mul_ne_zero ha hb)).mpr
  rw [Finset.sum_mul]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (n.choose k : R) * ((ascPochhammer R k).eval a)⁻¹ *
          ((ascPochhammer R (n - k)).eval b)⁻¹ *
          ((ascPochhammer R n).eval a * (ascPochhammer R n).eval b) =
        (n.choose k : R) *
          ((descPochhammer ℤ k).smeval (b + n - 1) *
            (descPochhammer ℤ (n - k)).smeval (a + n - 1)) := by
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have haeq := congrArg (eval a) (ascPochhammer_mul R k (n - k))
    have hbeq := congrArg (eval b) (ascPochhammer_mul R (n - k) k)
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast,
      Nat.add_sub_of_le hkn, Nat.sub_add_cancel hkn] at haeq hbeq
    have hak : (ascPochhammer R k).eval a ≠ 0 := by
      intro h
      rw [h, zero_mul] at haeq
      exact ha haeq.symm
    have hbk : (ascPochhammer R (n - k)).eval b ≠ 0 := by
      intro h
      rw [h, zero_mul] at hbeq
      exact hb hbeq.symm
    rw [descPochhammer_smeval_eq_ascPochhammer,
      descPochhammer_smeval_eq_ascPochhammer,
      ascPochhammer_smeval_eq_eval, ascPochhammer_smeval_eq_eval]
    rw [show b + n - 1 - k + 1 = b + ((n - k : ℕ) : R) by rw [Nat.cast_sub hkn]; ring,
      show a + n - 1 - ((n - k : ℕ) : R) + 1 = a + k by rw [Nat.cast_sub hkn]; ring]
    rw [← haeq, ← hbeq]
    field_simp
  rw [Finset.sum_congr rfl hterm,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l =>
      (n.choose k : R) *
        ((descPochhammer ℤ k).smeval (b + n - 1) *
          (descPochhammer ℤ l).smeval (a + n - 1)),
    ← Ring.descPochhammer_smeval_add n (Commute.all _ _),
    descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval]
  congr 1
  ring

end Polynomial
