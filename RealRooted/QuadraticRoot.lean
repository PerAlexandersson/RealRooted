module

public import Mathlib

/-!
# Real roots of quadratics with nonnegative discriminant

This file records the elementary fact that a real quadratic with nonnegative
discriminant has a real root.
-/

public section

open Polynomial

namespace RealRooted

/-- A real quadratic `a x^2 + b x + c` with `a ≠ 0` and nonnegative
discriminant has a real root. -/
lemma exists_root_of_disc_nonneg {a b c : ℝ} (ha : a ≠ 0)
    (h : 0 ≤ b ^ 2 - 4 * a * c) :
    ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
  refine ⟨(-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a), ?_⟩
  have hs := Real.sq_sqrt h
  grind

/-- Completing the square for a quadratic in discriminant form. -/
lemma four_mul_quadratic_eq (a b c x : ℝ) :
    4 * a * (a * x ^ 2 + b * x + c) = (2 * a * x + b) ^ 2 - discrim a b c := by
  rw [discrim]
  ring

/-- For a genuine quadratic, a real root exists iff the discriminant is
nonnegative. -/
lemma exists_root_iff_discrim_nonneg {a b c : ℝ} (ha : a ≠ 0) :
    (∃ x : ℝ, a * x ^ 2 + b * x + c = 0) ↔ 0 ≤ discrim a b c := by
  constructor
  · rintro ⟨x, hx⟩
    have hsq := four_mul_quadratic_eq a b c x
    rw [hx, mul_zero] at hsq
    nlinarith [sq_nonneg (2 * a * x + b)]
  · exact exists_root_of_disc_nonneg ha

/-- A real quadratic polynomial with nonzero leading coefficient and
nonnegative discriminant splits over `ℝ`. -/
lemma quadraticPoly_splits_of_discrim_nonneg {a b c : ℝ} (ha : a ≠ 0)
    (hdisc : 0 ≤ discrim a b c) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits := by
  obtain ⟨x, hx⟩ := (exists_root_iff_discrim_nonneg ha).mpr hdisc
  exact Polynomial.Splits.of_natDegree_eq_two (natDegree_quadratic ha) (by simpa using hx)

/-- Roots of a real quadratic with positive leading coefficient and
nonnegative discriminant, ordered increasingly. -/
lemma roots_quadratic_posLead {a b c : ℝ} (ha : 0 < a)
    (hd : 0 ≤ b ^ 2 - 4 * a * c) :
    (C a * X ^ 2 + C b * X + C c).roots =
      {(-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a),
        (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)} := by
  have hs₂ : Real.sqrt (b ^ 2 - 4 * a * c) ^ 2 = b ^ 2 - 4 * a * c :=
    Real.sq_sqrt hd
  apply (Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero'
    (a := a) (b := b) (c := c) (ha := ne_of_gt ha)).2
  constructor
  · field_simp
    ring
  · field_simp
    linarith [hs₂]

/-- A real polynomial written in quadratic form splits when its discriminant
is nonnegative; if the quadratic coefficient is zero, this is the linear case.
-/
lemma quadraticPoly_splits_of_discrim_nonneg_or_linear {a b c : ℝ}
    (hdisc : 0 ≤ discrim a b c) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits := by
  by_cases ha : a = 0
  · simpa [ha] using
      Polynomial.Splits.of_natDegree_le_one (by compute_degree : (C b * X + C c).natDegree ≤ 1)
  · exact quadraticPoly_splits_of_discrim_nonneg ha hdisc

/-- A real quadratic polynomial with nonzero leading coefficient and negative
discriminant does not split over `ℝ`. -/
lemma quadraticPoly_not_splits_of_discrim_neg {a b c : ℝ} (ha : a ≠ 0)
    (hdisc : discrim a b c < 0) :
    ¬ ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits := by
  intro hs
  obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero <|
    Polynomial.degree_ne_of_natDegree_ne (by rw [natDegree_quadratic ha]; norm_num)
  exact (not_le_of_gt hdisc) <| (exists_root_iff_discrim_nonneg ha).mp
    ⟨x, by simpa using hx⟩

/-- Splitting criterion for a real quadratic polynomial. -/
private lemma quadraticPoly_splits_iff_discrim_nonneg {a b c : ℝ} (ha : a ≠ 0) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ 0 ≤ discrim a b c := by
  refine ⟨fun hsplit => ?_, quadraticPoly_splits_of_discrim_nonneg ha⟩
  by_contra hneg
  exact quadraticPoly_not_splits_of_discrim_neg ha (lt_of_not_ge hneg) hsplit

/-- Splitting criterion for a normalized monic real quadratic, phrased with
the explicit discriminant `b ^ 2 - 4 * c`. -/
lemma monicQuadraticPoly_splits_iff_discrim_nonneg {b c : ℝ} :
    ((X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ 0 ≤ b ^ 2 - 4 * c := by
  simpa [discrim] using
    (quadraticPoly_splits_iff_discrim_nonneg (a := (1 : ℝ)) (b := b) (c := c) one_ne_zero)

/-- Non-splitting criterion for a normalized monic real quadratic. -/
lemma monicQuadraticPoly_not_splits_iff_discrim_neg {b c : ℝ} :
    ¬ ((X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ b ^ 2 - 4 * c < 0 := by
  rw [monicQuadraticPoly_splits_iff_discrim_nonneg, not_le]

/-- Splitting criterion for a quadratic with positive leading coefficient. -/
lemma quadraticPoly_splits_iff_le {a b c : ℝ} (ha : 0 < a) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits ↔ 4 * a * c ≤ b ^ 2 := by
  rw [quadraticPoly_splits_iff_discrim_nonneg ha.ne']
  rw [discrim]
  grind

/-- One-directional splitting criterion for a quadratic with positive leading
coefficient. -/
lemma quadraticPoly_splits_of_le {a b c : ℝ} (ha : 0 < a)
    (h : 4 * a * c ≤ b ^ 2) :
    ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits :=
  (quadraticPoly_splits_iff_le ha).mpr h

/-- A splitting real quadratic has nonnegative discriminant, expressed in
coefficient form. -/
theorem quadratic_disc_coeff_le_of_splits_natDegree_two
    {p : ℝ[X]} (hdeg : p.natDegree = 2) (hs : p.Splits) :
    4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 := by
  have ha : p.coeff 2 ≠ 0 := by
    rw [← hdeg, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact Polynomial.ne_zero_of_natDegree_gt (n := 0) (by rw [hdeg]; norm_num)
  rw [Polynomial.eq_quadratic_of_degree_le_two
    (Polynomial.degree_le_of_natDegree_le hdeg.le)] at hs
  have := (quadraticPoly_splits_iff_discrim_nonneg ha).mp hs
  unfold discrim at this
  nlinarith

/-- A splitting real polynomial of degree at most two has nonnegative
quadratic discriminant, expressed in coefficient form. -/
theorem quadratic_disc_coeff_le_of_splits_natDegree_le_two
    {p : ℝ[X]} (hdeg : p.natDegree ≤ 2) (hs : p.Splits) :
    4 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 := by
  by_cases h2 : p.natDegree = 2
  · exact quadratic_disc_coeff_le_of_splits_natDegree_two h2 hs
  · have hc2 : p.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
    rw [hc2]
    linarith [sq_nonneg (p.coeff 1)]

/-- A degree-two real polynomial with nonnegative discriminant splits. -/
theorem splits_of_natDegree_eq_two_of_discrim_nonneg {p : ℝ[X]} (h : p.natDegree = 2)
    (hd : 0 ≤ discrim (p.coeff 2) (p.coeff 1) (p.coeff 0)) : p.Splits := by
  have ha : p.coeff 2 ≠ 0 := by
    rw [← h, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact Polynomial.ne_zero_of_natDegree_gt (n := 0) (by rw [h]; norm_num)
  rw [Polynomial.eq_quadratic_of_degree_le_two
    (Polynomial.degree_le_of_natDegree_le h.le)]
  exact quadraticPoly_splits_of_discrim_nonneg ha hd

/-- The quadratic `C a + C b * X + C c * X ^ 2` splits when `0 ≤ b ^ 2 - 4 * c * a`. -/
theorem splits_C_add_C_mul_X_add_C_mul_X_sq {a b c : ℝ} (h : 0 ≤ b ^ 2 - 4 * c * a) :
    (C a + C b * X + C c * X ^ 2 : ℝ[X]).Splits := by
  simpa [add_comm, add_left_comm, add_assoc] using
    quadraticPoly_splits_of_discrim_nonneg_or_linear
      (a := c) (b := b) (c := a) (by simpa [discrim] using h)

/-- A palindromic quartic `a + b X + c X² + b X³ + a X⁴` with `a > 0` splits when the quadratic
`a y² + b y + (c - 2a)` in `y = X + 1/X` has both roots at most `-2`, that is, when `4a ≤ b`,
`2b ≤ c + 2a` and `4a(c - 2a) ≤ b²`. -/
theorem splits_palindromic_quartic {a b c : ℝ} (ha : 0 < a) (hb : 4 * a ≤ b)
    (hc : 2 * b ≤ c + 2 * a) (hd : 0 ≤ b ^ 2 - 4 * a * (c - 2 * a)) :
    (C a + C b * X + C c * X ^ 2 + C b * X ^ 3 + C a * X ^ 4 : ℝ[X]).Splits := by
  set s := Real.sqrt (b ^ 2 - 4 * a * (c - 2 * a))
  have hs2 : s ^ 2 = b ^ 2 - 4 * a * (c - 2 * a) := Real.sq_sqrt hd
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsle : s ≤ b - 4 * a := by nlinarith
  set y₁ := (-b + s) / (2 * a)
  set y₂ := (-b - s) / (2 * a)
  have hsum : b = a * -(y₁ + y₂) := by
    simp only [y₁, y₂]
    field_simp [ha.ne']
    ring
  have hprod : c = a * (2 + y₁ * y₂) := by
    simp only [y₁, y₂]
    field_simp [ha.ne']
    nlinarith
  have hy₁ : y₁ ≤ -2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hy₂ : y₂ ≤ -2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hfac : (C a + C b * X + C c * X ^ 2 + C b * X ^ 3 + C a * X ^ 4 : ℝ[X]) =
      C a * ((C 1 + C (-y₁) * X + C 1 * X ^ 2) * (C 1 + C (-y₂) * X + C 1 * X ^ 2)) := by
    rw [hsum, hprod]
    simp only [map_mul, map_neg, map_add, map_ofNat, map_one]
    ring
  rw [hfac]
  refine (Splits.mul ?_ ?_).C_mul a <;>
    exact splits_C_add_C_mul_X_add_C_mul_X_sq (by nlinarith)

end RealRooted
