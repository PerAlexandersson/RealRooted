import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Ring

/-!
# Ordered quadratic inequalities

This file supplements `Mathlib.Algebra.QuadraticDiscriminant` with elementary
ordered-ring consequences of global nonnegativity and nonpositive
discriminant.
-/

open Filter

/-- Updating the leading and linear coefficients of a quadratic changes its
discriminant by an explicit correction while the constant coefficient stays
fixed. -/
theorem discrim_add_leading_linear
    {R : Type*} [CommRing R] (a b c da db : R) :
    discrim (a + da) (b + db) c =
      discrim a b c + (2 * b * db + db ^ 2 - 4 * da * c) := by
  simp only [discrim]
  ring

/-- Nonpositivity after updating the leading and linear coefficients is
equivalent to fitting the exact correction inside the old discriminant
margin. -/
theorem discrim_add_leading_linear_nonpos_iff
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c da db : R) :
    discrim (a + da) (b + db) c ≤ 0 ↔
      2 * b * db + db ^ 2 - 4 * da * c ≤ -discrim a b c := by
  rw [discrim_add_leading_linear]
  constructor <;> intro h <;> linarith

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

/-- A quadratic with nonnegative leading and constant coefficients and
nonpositive discriminant is nonnegative on the whole ordered field. -/
theorem quadratic_nonneg_of_nonneg_of_discrim_nonpos
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hdisc : discrim a b c ≤ 0) (x : K) :
    0 ≤ a * (x * x) + b * x + c := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    rw [discrim] at hdisc
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    simp [hb, hc]
  · exact quadratic_nonneg_of_pos_of_discrim_nonpos ha hdisc x

/-- If a quadratic has zero leading coefficient and nonpositive
discriminant, then its linear coefficient vanishes. -/
theorem quadratic_linear_eq_zero_of_leading_eq_zero_of_discrim_nonpos
    {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (ha : a = 0) (hdisc : discrim a b c ≤ 0) :
    b = 0 := by
  rw [discrim, ha] at hdisc
  nlinarith [sq_nonneg b]

/-- For a quadratic with nonnegative leading coefficient and nonpositive
discriminant, either the leading coefficient vanishes or the constant
coefficient is nonnegative. -/
theorem
    quadratic_leading_eq_zero_or_constant_nonneg_of_leading_nonneg_of_discrim_nonpos
    {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (ha : 0 ≤ a) (hdisc : discrim a b c ≤ 0) :
    a = 0 ∨ 0 ≤ c := by
  rcases ha.eq_or_lt with ha | ha
  · exact Or.inl ha.symm
  · right
    by_contra hc
    have hc' : c < 0 := lt_of_not_ge hc
    rw [discrim] at hdisc
    have hproduct : 4 * a * c < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by norm_num) ha) hc'
    linarith [sq_nonneg b]

/-- A quadratic with positive leading coefficient and negative discriminant
is positive on the whole ordered field. -/
theorem quadratic_pos_of_pos_of_discrim_neg
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : K} (ha : 0 < a) (hdisc : discrim a b c < 0) (x : K) :
    0 < a * (x * x) + b * x + c := by
  rw [discrim] at hdisc
  have hsquare := sq_nonneg (2 * a * x + b)
  nlinarith
