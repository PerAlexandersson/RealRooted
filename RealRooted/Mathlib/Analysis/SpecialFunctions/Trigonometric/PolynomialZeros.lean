/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots

/-!
# Zeros of real trigonometric polynomials

A real trigonometric polynomial `∑_{k ≤ n} (a k cos (k t) + b k sin (k t))` that does not vanish
identically has at most `2 n` zeros in `[0, 2π)`.  Writing `w = exp (t i)`, the function
`w ^ n` times the trigonometric polynomial is the value at `w` of a complex polynomial of degree at
most `2 n`, and distinct points of `[0, 2π)` give distinct points `w` on the unit circle.
-/

public section

noncomputable section

open Polynomial Complex

namespace Real

/-- The complex polynomial of degree at most `2 n` whose value at `exp (t i)` is `exp (n t i)`
times the trigonometric polynomial with cosine coefficients `a` and sine coefficients `b`. -/
def trigPolynomialLift (n : ℕ) (a b : ℕ → ℝ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    (C (((a k : ℂ) - b k * I) / 2) * X ^ (n + k) +
      C (((a k : ℂ) + b k * I) / 2) * X ^ (n - k))

/-- The lift has degree at most `2 n`. -/
theorem natDegree_trigPolynomialLift_le (n : ℕ) (a b : ℕ → ℝ) :
    (trigPolynomialLift n a b).natDegree ≤ 2 * n := by
  unfold trigPolynomialLift
  refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
  have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_X_pow_le _ _).trans (by lia)
  · exact (natDegree_C_mul_X_pow_le _ _).trans (by lia)

/-- One summand of the lift evaluates to `exp (n t i)` times the matching trigonometric term. -/
private theorem eval_trigPolynomialLift_term {n k : ℕ} (hk : k ≤ n) (a b t : ℝ) :
    (((a : ℂ) - b * I) / 2) * Complex.exp (t * I) ^ (n + k) +
        (((a : ℂ) + b * I) / 2) * Complex.exp (t * I) ^ (n - k) =
      Complex.exp (t * I) ^ n * ((a * Real.cos (k * t) + b * Real.sin (k * t) : ℝ) : ℂ) := by
  have hw : Complex.exp (t * I) ≠ 0 := Complex.exp_ne_zero _
  have hsplit :
      Complex.exp (t * I) ^ (n - k) * Complex.exp (t * I) ^ k = Complex.exp (t * I) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hpos : Complex.exp (t * I) ^ k = (Real.cos (k * t) : ℂ) + Real.sin (k * t) * I := by
    rw [← Complex.exp_nat_mul, ← mul_assoc, ← ofReal_natCast, ← ofReal_mul, Complex.exp_mul_I,
      ← ofReal_cos, ← ofReal_sin]
  have hneg : Complex.exp (t * I) ^ (n - k) =
      Complex.exp (t * I) ^ n * ((Real.cos (k * t) : ℂ) - Real.sin (k * t) * I) := by
    have hnorm : ((Real.cos (k * t) : ℂ) + Real.sin (k * t) * I) *
        ((Real.cos (k * t) : ℂ) - Real.sin (k * t) * I) = 1 := by
      have h : (Real.cos (k * t) : ℂ) ^ 2 + (Real.sin (k * t) : ℂ) ^ 2 = 1 := by
        exact_mod_cast Real.cos_sq_add_sin_sq (k * t)
      linear_combination h - (Real.sin (k * t) : ℂ) ^ 2 * I_sq
    calc Complex.exp (t * I) ^ (n - k)
        = Complex.exp (t * I) ^ (n - k) * (Complex.exp (t * I) ^ k *
            ((Real.cos (k * t) : ℂ) - Real.sin (k * t) * I)) := by
          rw [hpos, hnorm, mul_one]
      _ = Complex.exp (t * I) ^ n * ((Real.cos (k * t) : ℂ) - Real.sin (k * t) * I) := by
          rw [← mul_assoc, hsplit]
  rw [pow_add, hpos, hneg, ofReal_add, ofReal_mul, ofReal_mul]
  linear_combination (-(Complex.exp (t * I) ^ n * b * (Real.sin (k * t) : ℂ))) * I_sq

/-- At `exp (t i)` the lift is `exp (n t i)` times the trigonometric polynomial. -/
theorem eval_trigPolynomialLift (n : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    (trigPolynomialLift n a b).eval (Complex.exp (t * I)) =
      Complex.exp (t * I) ^ n *
        ((∑ k ∈ Finset.range (n + 1), (a k * Real.cos (k * t) + b k * Real.sin (k * t)) : ℝ) :
          ℂ) := by
  simp only [trigPolynomialLift, eval_finsetSum, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  exact eval_trigPolynomialLift_term (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) _ _ _

/-- The map `t ↦ exp (t i)` is injective on `[0, 2π)`. -/
theorem injOn_exp_mul_I_Ico : Set.InjOn (fun t : ℝ ↦ Complex.exp (t * I)) (Set.Ico 0 (2 * π)) := by
  intro t ht u hu h
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hre : t = u + m * (2 * π) := by
    have := congrArg Complex.im hm
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hm0 : m = 0 := by
    have hlt : |(m : ℝ) * (2 * π)| < 2 * π := by
      rw [abs_lt]
      constructor <;> nlinarith [ht.1, ht.2, hu.1, hu.2, Real.pi_pos]
    have hmabs : |(m : ℝ)| < 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hlt
      nlinarith [Real.pi_pos]
    rw [← Int.cast_abs] at hmabs
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast hmabs)
  simpa [hm0] using hre

/-- A real trigonometric polynomial of degree at most `n` that does not vanish identically has at
most `2 n` zeros in `[0, 2π)`. -/
theorem card_zeros_trigPolynomial_le {n : ℕ} {a b : ℕ → ℝ} {s : Finset ℝ}
    (hs : ∀ t ∈ s, t ∈ Set.Ico 0 (2 * π))
    (hzero : ∀ t ∈ s,
      ∑ k ∈ Finset.range (n + 1), (a k * Real.cos (k * t) + b k * Real.sin (k * t)) = 0)
    (hne : ∃ t : ℝ,
      ∑ k ∈ Finset.range (n + 1), (a k * Real.cos (k * t) + b k * Real.sin (k * t)) ≠ 0) :
    s.card ≤ 2 * n := by
  set q := trigPolynomialLift n a b
  have hq : q ≠ 0 := by
    obtain ⟨t, ht⟩ := hne
    intro h0
    have h := eval_trigPolynomialLift n a b t
    rw [show trigPolynomialLift n a b = 0 from h0, eval_zero] at h
    have hw : Complex.exp (t * I) ^ n ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
    have h' := (mul_eq_zero.mp h.symm).resolve_left hw
    exact ht (by exact_mod_cast h')
  have hmaps : ∀ t ∈ s, Complex.exp (t * I) ∈ q.roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, mem_roots hq, IsRoot.def, eval_trigPolynomialLift, hzero t ht]
    simp
  calc s.card = (s.image fun t : ℝ ↦ Complex.exp (t * I)).card :=
        (Finset.card_image_of_injOn (injOn_exp_mul_I_Ico.mono fun t ht ↦ hs t ht)).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card fun w hw ↦ by
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
        exact hmaps t ht
    _ ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := card_roots' q
    _ ≤ 2 * n := natDegree_trigPolynomialLift_le n a b

end Real
