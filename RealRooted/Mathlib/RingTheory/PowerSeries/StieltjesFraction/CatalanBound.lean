/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Coefficients
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Geometric bounds for Stieltjes coefficients

Nonnegative numerators bounded by `L` give degree-`n` coefficients at most
`catalan n * L^n`, hence at most `(4*L)^n`. These are formal coefficient bounds,
independent of the existence of a representing measure.

See Sokal, arXiv:1903.12455v2, elementary continued-fraction fact 3.
-/

public section

open scoped BigOperators

namespace PowerSeries

/-- Nonnegative Stieltjes coefficients increase with every numerator. -/
theorem coeff_stieltjesTail_mono {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k)
    (hab : ∀ k, a k ≤ b k) (n s : ℕ) :
    coeff n (stieltjesTail a s) ≤ coeff n (stieltjesTail b s) := by
  have hb : ∀ k, 0 ≤ b k := fun k => (ha k).trans (hab k)
  induction n using Nat.strong_induction_on generalizing s with
  | ind n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [coeff_stieltjesTail_succ, coeff_stieltjesTail_succ]
          apply mul_le_mul (hab s)
          · apply Finset.sum_le_sum
            intro ij hij
            have hij' := Finset.mem_antidiagonal.mp hij
            exact mul_le_mul (ih ij.1 (by lia) s) (ih ij.2 (by lia) (s + 1))
              (coeff_stieltjesTail_nonneg ha _ _) (coeff_stieltjesTail_nonneg hb _ _)
          · exact Finset.sum_nonneg fun ij _ =>
              mul_nonneg (coeff_stieltjesTail_nonneg ha _ _) (coeff_stieltjesTail_nonneg ha _ _)
          · exact hb s

/-- Uniformly bounded nonnegative numerators give a weighted Catalan bound. -/
theorem coeff_stieltjesTail_le_catalan {a : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (ha : ∀ k, 0 ≤ a k) (haL : ∀ k, a k ≤ L) (n s : ℕ) :
    coeff n (stieltjesTail a s) ≤ (catalan n : ℝ) * L ^ n := by
  induction n using Nat.strong_induction_on generalizing s with
  | ind n ih =>
      cases n with
      | zero => simp
      | succ n =>
          have hsum : ∑ ij ∈ Finset.antidiagonal n,
                ((catalan ij.1 : ℝ) * L ^ ij.1) * ((catalan ij.2 : ℝ) * L ^ ij.2) =
              L ^ n * (catalan (n + 1) : ℝ) := by
            calc
              _ = ∑ ij ∈ Finset.antidiagonal n,
                  L ^ n * ((catalan ij.1 : ℝ) * (catalan ij.2 : ℝ)) := by
                apply Finset.sum_congr rfl
                intro ij hij
                have hij' := Finset.mem_antidiagonal.mp hij
                rw [← hij', pow_add]
                ring
              _ = _ := by
                rw [← Finset.mul_sum]
                congr 1
                exact_mod_cast (catalan_succ' n).symm
          calc
            coeff (n + 1) (stieltjesTail a s) = a s *
                ∑ ij ∈ Finset.antidiagonal n,
                  coeff ij.1 (stieltjesTail a s) *
                    coeff ij.2 (stieltjesTail a (s + 1)) := coeff_stieltjesTail_succ a s n
            _ ≤ L * ∑ ij ∈ Finset.antidiagonal n,
                ((catalan ij.1 : ℝ) * L ^ ij.1) * ((catalan ij.2 : ℝ) * L ^ ij.2) := by
              apply mul_le_mul (haL s)
              · apply Finset.sum_le_sum
                intro ij hij
                have hij' := Finset.mem_antidiagonal.mp hij
                exact mul_le_mul (ih ij.1 (by lia) s) (ih ij.2 (by lia) (s + 1))
                  (coeff_stieltjesTail_nonneg ha _ _)
                  (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hL _))
              · exact Finset.sum_nonneg fun ij _ =>
                  mul_nonneg (coeff_stieltjesTail_nonneg ha _ _) (coeff_stieltjesTail_nonneg ha _ _)
              · exact hL
            _ = (catalan (n + 1) : ℝ) * L ^ (n + 1) := by
              rw [hsum, pow_succ]
              ring

/-- Uniformly bounded nonnegative Stieltjes data give a geometric coefficient bound. -/
theorem coeff_stieltjesTail_le_pow {a : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (ha : ∀ k, 0 ≤ a k) (haL : ∀ k, a k ≤ L) (n s : ℕ) :
    coeff n (stieltjesTail a s) ≤ (4 * L) ^ n := by
  have hcat : catalan n ≤ 4 ^ n := by
    rw [catalan_eq_centralBinom_div]
    exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow n)
  calc
    coeff n (stieltjesTail a s) ≤ (catalan n : ℝ) * L ^ n :=
      coeff_stieltjesTail_le_catalan hL ha haL n s
    _ ≤ (4 : ℝ) ^ n * L ^ n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcat) (pow_nonneg hL n)
    _ = _ := (mul_pow 4 L n).symm

end PowerSeries
