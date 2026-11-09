/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Wronskian.PolarLaguerre
import RealRooted.Mathlib.Analysis.Calculus.LocalExtr.Polynomial

/-!
# The two Laguerre forms of a split polynomial

For a real polynomial `f` the first Laguerre form is `f' ^ 2 - f * f''`
(`RealRooted.laguerreForm`), and the second one is
`(3 * f'' ^ 2 - 4 * f' * f''' + f * f⁽⁴⁾) / 12` (`RealRooted.secondLaguerreForm`).
If `f = a * ∏ (X - rⱼ)`, then `f (t + i y) * f (t - i y) = a ^ 2 * ∏ ((t - rⱼ) ^ 2 + y ^ 2)`,
and the coefficients of `y ^ 2` and `y ^ 4` on the left are the two forms evaluated at `t`.
All coefficients on the right are nonnegative, so both forms are nonnegative when `f` splits.
We prove this without complex numbers, from the identities
`L₁ ((X - a) * g) = g ^ 2 + (X - a) ^ 2 * L₁ g` and
`L₂ ((X - a) * g) = L₁ g + (X - a) ^ 2 * L₂ g`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The second Laguerre form `(3 * f'' ^ 2 - 4 * f' * f''' + f * f⁽⁴⁾) / 12` of a real
polynomial: the coefficient of `y ^ 4` in `f (t + i y) * f (t - i y)`. -/
def secondLaguerreForm (f : ℝ[X]) : ℝ[X] :=
  C (1 / 12) * (3 * derivative (derivative f) ^ 2 -
    4 * derivative f * derivative (derivative (derivative f)) +
    f * derivative (derivative (derivative (derivative f))))

@[simp] theorem eval_secondLaguerreForm (f : ℝ[X]) (t : ℝ) :
    (secondLaguerreForm f).eval t =
      (3 * (derivative (derivative f)).eval t ^ 2 -
        4 * (derivative f).eval t * (derivative (derivative (derivative f))).eval t +
        f.eval t * (derivative (derivative (derivative (derivative f)))).eval t) / 12 := by
  simp [secondLaguerreForm]
  ring

/-- Adjoining a linear factor `X - a` turns the first Laguerre form into
`g ^ 2 + (X - a) ^ 2 * L₁ g`. -/
theorem laguerreForm_X_sub_C_mul (a : ℝ) (g : ℝ[X]) :
    laguerreForm ((X - C a) * g) = g ^ 2 + (X - C a) ^ 2 * laguerreForm g := by
  simp only [laguerreForm, map_add, map_sub, derivative_mul, derivative_X, derivative_C,
    map_zero, derivative_one]
  ring

/-- Adjoining a linear factor `X - a` turns the second Laguerre form into
`L₁ g + (X - a) ^ 2 * L₂ g`. -/
theorem secondLaguerreForm_X_sub_C_mul (a : ℝ) (g : ℝ[X]) :
    secondLaguerreForm ((X - C a) * g) =
      laguerreForm g + (X - C a) ^ 2 * secondLaguerreForm g := by
  simp only [secondLaguerreForm, laguerreForm, map_add, map_sub, derivative_mul, derivative_X,
    derivative_C, map_zero, derivative_one]
  have h12 : (C (1 / 12 : ℝ)) * 12 = 1 := by
    rw [← C_ofNat, ← C_mul]; simp
  linear_combination (derivative g ^ 2 - g * derivative (derivative g)) * h12

private theorem forms_eval_nonneg_prod (c : ℝ) (s : Multiset ℝ) (t : ℝ) :
    0 ≤ (laguerreForm (C c * (s.map fun r => X - C r).prod)).eval t ∧
      0 ≤ (secondLaguerreForm (C c * (s.map fun r => X - C r).prod)).eval t := by
  induction s using Multiset.induction_on with
  | empty => simp [laguerreForm]
  | cons a s ih =>
    have hrw : (C c * ((a ::ₘ s).map fun r => X - C r).prod : ℝ[X]) =
        (X - C a) * (C c * (s.map fun r => X - C r).prod) := by
      rw [Multiset.map_cons, Multiset.prod_cons]
      ring
    rw [hrw, laguerreForm_X_sub_C_mul, secondLaguerreForm_X_sub_C_mul]
    obtain ⟨h₁, h₂⟩ := ih
    simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    exact ⟨add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) h₁),
      add_nonneg h₁ (mul_nonneg (sq_nonneg _) h₂)⟩

/-- Both Laguerre forms of a split polynomial are nonnegative on `ℝ`. -/
theorem laguerreForm_eval_nonneg_and_secondLaguerreForm_eval_nonneg {f : ℝ[X]}
    (hf : f.Splits) (t : ℝ) :
    0 ≤ (laguerreForm f).eval t ∧ 0 ≤ (secondLaguerreForm f).eval t := by
  have h := forms_eval_nonneg_prod f.leadingCoeff f.roots t
  rwa [← hf.eq_prod_roots] at h

/-- The second Laguerre form of a split polynomial is nonnegative on `ℝ`. -/
theorem secondLaguerreForm_eval_nonneg {f : ℝ[X]} (hf : f.Splits) (t : ℝ) :
    0 ≤ (secondLaguerreForm f).eval t :=
  (laguerreForm_eval_nonneg_and_secondLaguerreForm_eval_nonneg hf t).2

/-- **Forward direction.** If a real polynomial splits, then its derivative splits and both
Laguerre forms are nonnegative on `ℝ`. -/
theorem splits_derivative_and_forms_nonneg_of_splits {f : ℝ[X]} (hf : f.Splits) :
    (derivative f).Splits ∧ ∀ t : ℝ,
      0 ≤ (laguerreForm f).eval t ∧ 0 ≤ (secondLaguerreForm f).eval t :=
  ⟨hf.derivative, fun t => laguerreForm_eval_nonneg_and_secondLaguerreForm_eval_nonneg hf t⟩

end RealRooted
