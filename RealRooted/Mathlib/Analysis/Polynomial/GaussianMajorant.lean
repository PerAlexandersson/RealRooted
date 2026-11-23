/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RealRooted.Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianTail

/-!
# Uniform Gaussian majorants for polynomial evaluations

The Gaussian parameter is bounded below by a positive constant, while the
polynomial argument and exponential prefactor range over bounded intervals.
A finite sum of polynomially weighted Gaussians dominates the whole family.
-/

public section

open Real

namespace Polynomial

private theorem abs_eval_le_coeff_majorant (p : ℝ[X]) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    |p.eval x| ≤ ∑ k ∈ p.support, |p.coeff k| * y ^ k := by
  rw [eval_eq_sum, sum_def]
  calc
    _ ≤ ∑ k ∈ p.support, |p.coeff k * x ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ p.support, |p.coeff k| * x ^ k := by
      simp only [abs_mul, abs_pow, abs_of_nonneg hx]
    _ ≤ _ := Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy k) (abs_nonneg _)

/-- A coefficientwise majorant for a polynomial multiplied by a Gaussian weight. -/
theorem norm_nat_pow_mul_eval_mul_exp_le (p : ℝ[X]) (r n : ℕ) {a b c d e : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c) (hcb : c ≤ b) (hed : e ≤ d) :
    ‖(n : ℝ) ^ r * p.eval (c * n ^ 2) * exp (e - c * n ^ 2)‖ ≤
      ∑ k ∈ p.support, (|p.coeff k| * |b| ^ k * exp d) *
        ((n : ℝ) ^ (2 * k + r) * exp (-a * n ^ 2)) := by
  have hc : 0 ≤ c := ha.trans hac
  have hpoly := abs_eval_le_coeff_majorant p
    (mul_nonneg hc (sq_nonneg (n : ℝ)))
    (mul_le_mul_of_nonneg_right (hcb.trans (le_abs_self b)) (sq_nonneg (n : ℝ)))
  have hexp : exp (e - c * (n : ℝ) ^ 2) ≤ exp d * exp (-a * n ^ 2) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hac) (sq_nonneg (n : ℝ))]
  calc
    _ = (n : ℝ) ^ r * |p.eval (c * n ^ 2)| * exp (e - c * n ^ 2) := by
      rw [norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ r),
        abs_of_pos (exp_pos _)]
    _ ≤ ((n : ℝ) ^ r * ∑ k ∈ p.support, |p.coeff k| * (|b| * n ^ 2) ^ k) *
        (exp d * exp (-a * n ^ 2)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity)) hexp
        (exp_nonneg _) (by positivity)
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_pow, ← pow_mul, pow_add]
      ring

/-- A compact family of polynomial Gaussian terms admits one summable lattice majorant. -/
theorem exists_summable_bound_nat_pow_eval_exp (p : ℝ[X]) (r : ℕ) {a : ℝ}
    (ha : 0 < a) (b d : ℝ) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ (n : ℕ) (c e : ℝ), a ≤ c → c ≤ b → e ≤ d →
      ‖(n : ℝ) ^ r * p.eval (c * n ^ 2) * exp (e - c * n ^ 2)‖ ≤ M n := by
  let M (n : ℕ) := ∑ k ∈ p.support, (|p.coeff k| * |b| ^ k * exp d) *
    ((n : ℝ) ^ (2 * k + r) * exp (-a * n ^ 2))
  refine ⟨M, ?_, fun n c e hac hcb hed => ?_⟩
  · exact summable_sum fun k _ => (summable_nat_pow_mul_exp_neg_sq (2 * k + r) ha).mul_left _
  · exact norm_nat_pow_mul_eval_mul_exp_le p r n ha.le hac hcb hed

end Polynomial
