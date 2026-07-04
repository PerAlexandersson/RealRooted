import Mathlib

/-!
# Real roots of quadratics with nonnegative discriminant

This file records the elementary fact that a real quadratic with nonnegative
discriminant has a real root.
-/

namespace RealRooted

/-- A real quadratic `a x^2 + b x + c` with `a ≠ 0` and nonnegative
discriminant has a real root. -/
lemma exists_root_of_disc_nonneg {a b c : ℝ} (ha : a ≠ 0)
    (h : 0 ≤ b ^ 2 - 4 * a * c) :
    ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
  set s := Real.sqrt (b ^ 2 - 4 * a * c) with hsdef
  have hs : s ^ 2 = b ^ 2 - 4 * a * c := Real.sq_sqrt h
  refine ⟨(-b + s) / (2 * a), ?_⟩
  have h2a : (2 * a) ≠ 0 := mul_ne_zero two_ne_zero ha
  field_simp
  linear_combination hs

end RealRooted
