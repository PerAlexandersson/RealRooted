module

public import RealRooted.SimpleRoots
public import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Strict discriminants of simple real-rooted quadratics
-/

public section

open Polynomial

namespace RealRooted

/-- A genuine quadratic with simple real roots has positive discriminant,
with either sign of its leading coefficient. -/
theorem IsSimpleRealRooted.discrim_pos {a b c : ℝ}
    (h : IsSimpleRealRooted (C a * X ^ 2 + C b * X + C c)) (ha : a ≠ 0) :
    0 < discrim a b c := by
  obtain ⟨x, hx⟩ := h.2.1.exists_eval_eq_zero (by
    rw [degree_quadratic ha]
    norm_num)
  have hr : (C a * X ^ 2 + C b * X + C c).IsRoot x := hx
  have hx' : a * (x * x) + b * x + c = 0 := by
    simpa only [eval_add, eval_mul, eval_C, eval_pow, eval_X, pow_two] using hx
  have hd : 2 * a * x + b ≠ 0 := by
    intro heq
    apply h.2.2.eval_derivative_ne_zero hr
    norm_num [derivative_add, derivative_mul, derivative_X_pow]
    nlinarith [heq]
  rw [discrim_eq_sq_of_quadratic_eq_zero hx']
  exact sq_pos_of_ne_zero hd

end RealRooted
