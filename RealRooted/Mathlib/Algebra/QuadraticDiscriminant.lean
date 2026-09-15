import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Ordered quadratic inequalities

This file supplements `Mathlib.Algebra.QuadraticDiscriminant` with an
elementary consequence of global nonnegativity.
-/

open Filter

/-- The quadratic coefficient is nonnegative when the quadratic is
nonnegative on the whole ordered field. -/
theorem quadratic_leadingCoeff_nonneg
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (h : ∀ x : K, 0 ≤ a * (x * x) + b * x + c) :
    0 ≤ a := by
  by_contra ha
  have ha' : a < 0 := lt_of_not_ge ha
  have ht : Tendsto (fun x => (a * x + b) * x + c) atTop atBot :=
    tendsto_atBot_add_const_right _ c <|
      (tendsto_atBot_add_const_right _ b
        (tendsto_id.const_mul_atTop_of_neg ha')).atBot_mul_atTop₀ tendsto_id
  rcases (ht.eventually (eventually_lt_atBot 0)).exists with ⟨x, hx⟩
  apply (h x).not_gt
  calc
    a * (x * x) + b * x + c = (a * x + b) * x + c := by
      simp only [add_mul, mul_assoc]
    _ < 0 := hx

/-- A quadratic with positive leading coefficient and nonpositive
discriminant is nonnegative on the whole ordered field. -/
theorem quadratic_nonneg_of_pos_of_discrim_nonpos
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (ha : 0 < a) (hdisc : discrim a b c ≤ 0) (x : K) :
    0 ≤ a * (x * x) + b * x + c := by
  rw [discrim] at hdisc
  have hsquare := sq_nonneg (2 * a * x + b)
  nlinarith

/-- A quadratic with positive leading coefficient and negative discriminant
is positive on the whole ordered field. -/
theorem quadratic_pos_of_pos_of_discrim_neg
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (ha : 0 < a) (hdisc : discrim a b c < 0) (x : K) :
    0 < a * (x * x) + b * x + c := by
  rw [discrim] at hdisc
  have hsquare := sq_nonneg (2 * a * x + b)
  nlinarith
