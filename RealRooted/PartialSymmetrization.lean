import RealRooted.Multiaffine

/-!
# Partial symmetrization

This file develops the bivariate coefficient identities used in the
Borcea--Brändén proof that transposition averages preserve stability.
-/

namespace RealRooted

open MvPolynomial

/-- The first real quadratic form from Borcea--Brändén, Part II, Lemma 1.4. -/
def bivariateV1 (a b c d : ℂ) (x : ℝ) : ℝ :=
  (a * star c).im + (a * star d + b * star c).im * x +
    (b * star d).im * x ^ 2

/-- The second real quadratic form from Borcea--Brändén, Part II, Lemma 1.4. -/
def bivariateV2 (a b c d : ℂ) (x : ℝ) : ℝ :=
  bivariateV1 a c b d x

/-- The four-coefficient bivariate multiaffine polynomial used in Part II,
Lemma 1.4. -/
noncomputable def bivariateMultiaffinePolynomial (a b c d : ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  C a + C b * X 0 + C c * X 1 + C d * X 0 * X 1

/-- Evaluation of the four-coefficient bivariate multiaffine polynomial. -/
theorem eval_bivariateMultiaffinePolynomial
    (a b c d : ℂ) (z : Fin 2 → ℂ) :
    MvPolynomial.eval z (bivariateMultiaffinePolynomial a b c d) =
      a + b * z 0 + c * z 1 + d * z 0 * z 1 := by
  simp [bivariateMultiaffinePolynomial]

/-- The real-boundary quotient identity for `bivariateV1` from
Borcea--Brändén, Part II, Lemma 1.4. -/
theorem im_bivariateQuotient_eq_bivariateV1_div_normSq
    (a b c d : ℂ) (x : ℝ) :
    ((a + b * (x : ℂ)) / (c + d * (x : ℂ))).im =
      bivariateV1 a b c d x /
        Complex.normSq (c + d * (x : ℂ)) := by
  simp [Complex.div_im, Complex.normSq, bivariateV1]
  ring

/-- The symmetric real-boundary quotient identity for `bivariateV2` from
Borcea--Brändén, Part II, Lemma 1.4. -/
theorem im_bivariateQuotient_eq_bivariateV2_div_normSq
    (a b c d : ℂ) (x : ℝ) :
    ((a + c * (x : ℂ)) / (b + d * (x : ℂ))).im =
      bivariateV2 a b c d x /
        Complex.normSq (b + d * (x : ℂ)) := by
  exact im_bivariateQuotient_eq_bivariateV1_div_normSq a c b d x

/-- A positive imaginary part of `c / d` keeps `c + d * z` nonzero on the
closed upper half-plane. This is the denominator observation in Part II,
Lemma 1.4. -/
theorem add_mul_ne_zero_of_im_div_pos
    (c d z : ℂ) (h : 0 < (c / d).im) (hz : 0 ≤ z.im) :
    c + d * z ≠ 0 := by
  intro hzero
  have hd : d ≠ 0 := by
    intro hd
    simp [hd] at h
  have hratio : c / d = -z := by
    apply (div_eq_iff hd).2
    linear_combination hzero
  rw [hratio] at h
  simp at h
  linarith

/-- The real-boundary specialization of
`add_mul_ne_zero_of_im_div_pos`. -/
theorem add_mul_real_ne_zero_of_im_div_pos
    (c d : ℂ) (x : ℝ) (h : 0 < (c / d).im) :
    c + d * (x : ℂ) ≠ 0 := by
  exact add_mul_ne_zero_of_im_div_pos c d x h (by simp)

/-- Solving a bivariate multiaffine expression for its second variable, as in
the proof of Borcea--Brändén, Part II, Lemma 1.4. -/
theorem bivariate_eq_factor_quotient
    (a b c d z w : ℂ) (hden : c + d * z ≠ 0) :
    a + b * z + c * w + d * z * w =
      (c + d * z) * (w + (a + b * z) / (c + d * z)) := by
  calc
    a + b * z + c * w + d * z * w =
        (c + d * z) * w + (a + b * z) := by ring
    _ = (c + d * z) * w +
        (c + d * z) * ((a + b * z) / (c + d * z)) := by
      rw [mul_div_cancel₀ (a + b * z) hden]
    _ = (c + d * z) * (w + (a + b * z) / (c + d * z)) := by ring

/-- With a nonzero denominator, the bivariate expression has the unique
second-variable zero used in equation (1.2) of Part II. -/
theorem bivariate_eq_zero_iff
    (a b c d z w : ℂ) (hden : c + d * z ≠ 0) :
    a + b * z + c * w + d * z * w = 0 ↔
      w = -((a + b * z) / (c + d * z)) := by
  rw [bivariate_eq_factor_quotient a b c d z w hden]
  simp only [mul_eq_zero, hden, false_or]
  constructor <;> intro h <;> linear_combination h

/-- Positive imaginary part of the solved quotient excludes a zero with the
second variable in the upper half-plane. -/
theorem bivariate_ne_zero_of_quotient_im_pos
    (a b c d z w : ℂ) (hden : c + d * z ≠ 0)
    (hq : 0 < ((a + b * z) / (c + d * z)).im) (hw : 0 < w.im) :
    a + b * z + c * w + d * z * w ≠ 0 := by
  intro hzero
  have hroot := (bivariate_eq_zero_iff a b c d z w hden).mp hzero
  rw [hroot] at hw
  simp at hw
  linarith

/-- The source's quotient-positivity condition implies bivariate nonvanishing
on the upper half-plane. This is the algebraic direction preceding (1.2). -/
theorem bivariate_ne_zero_of_im_div_pos_of_quotient_im_pos
    (a b c d z w : ℂ) (hcd : 0 < (c / d).im) (hz : 0 ≤ z.im)
    (hq : 0 < ((a + b * z) / (c + d * z)).im) (hw : 0 < w.im) :
    a + b * z + c * w + d * z * w ≠ 0 := by
  exact bivariate_ne_zero_of_quotient_im_pos a b c d z w
    (add_mul_ne_zero_of_im_div_pos c d z hcd hz) hq hw

/-- The quotient-positivity condition in (1.2) implies upper-half-plane
stability of the corresponding bivariate multiaffine polynomial. -/
theorem mvUpperHalfPlaneStable_bivariate_of_quotient_im_pos
    (a b c d : ℂ) (hcd : 0 < (c / d).im)
    (hq : ∀ z : ℂ, 0 < z.im →
      0 < ((a + b * z) / (c + d * z)).im) :
    MvUpperHalfPlaneStable (bivariateMultiaffinePolynomial a b c d) := by
  intro z hz
  rw [eval_bivariateMultiaffinePolynomial]
  exact bivariate_ne_zero_of_im_div_pos_of_quotient_im_pos
    a b c d (z 0) (z 1) hcd (le_of_lt (hz 0)) (hq (z 0) (hz 0)) (hz 1)

/-- Stability forces the solved quotient into the closed upper half-plane.
Upgrading this weak inequality to strict positivity is the separate
open-mapping step in the proof of Part II, Lemma 1.4. -/
theorem quotient_im_nonneg_of_mvUpperHalfPlaneStable_bivariate
    (a b c d : ℂ)
    (hP : MvUpperHalfPlaneStable (bivariateMultiaffinePolynomial a b c d))
    (hcd : 0 < (c / d).im) (z : ℂ) (hz : 0 < z.im) :
    0 ≤ ((a + b * z) / (c + d * z)).im := by
  by_contra hq
  let w := -((a + b * z) / (c + d * z))
  have hw : 0 < w.im := by
    dsimp [w]
    simp
    linarith
  have hstable := hP ![z, w] (by
    intro i
    fin_cases i <;> simp_all)
  rw [eval_bivariateMultiaffinePolynomial] at hstable
  exact hstable ((bivariate_eq_zero_iff a b c d z w
    (add_mul_ne_zero_of_im_div_pos c d z hcd (le_of_lt hz))).2 rfl)

/-- On the real boundary, positivity of the first quotient imaginary part is
equivalent to positivity of `bivariateV1` when its denominator stays off zero. -/
theorem im_bivariateQuotient_pos_iff_bivariateV1_pos
    (a b c d : ℂ) (x : ℝ) (h : 0 < (c / d).im) :
    0 < ((a + b * (x : ℂ)) / (c + d * (x : ℂ))).im ↔
      0 < bivariateV1 a b c d x := by
  have hden := add_mul_real_ne_zero_of_im_div_pos c d x h
  have hnorm : 0 < Complex.normSq (c + d * (x : ℂ)) :=
    Complex.normSq_pos.mpr hden
  rw [im_bivariateQuotient_eq_bivariateV1_div_normSq]
  exact div_pos_iff_of_pos_right hnorm

/-- The symmetric real-boundary positivity equivalence for `bivariateV2`. -/
theorem im_bivariateQuotient_pos_iff_bivariateV2_pos
    (a b c d : ℂ) (x : ℝ) (h : 0 < (b / d).im) :
    0 < ((a + c * (x : ℂ)) / (b + d * (x : ℂ))).im ↔
      0 < bivariateV2 a b c d x := by
  exact im_bivariateQuotient_pos_iff_bivariateV1_pos a c b d x h

/-- Under partial transposition averaging, V1 is the corresponding convex
combination of the original V1 and V2. -/
theorem bivariateV1_partialSymmetrization
    (a b c d : ℂ) (t x : ℝ) :
    bivariateV1 a
        ((t : ℂ) * b + (1 - t : ℝ) * c)
        ((t : ℂ) * c + (1 - t : ℝ) * b) d x =
      t * bivariateV1 a b c d x +
        (1 - t) * bivariateV2 a b c d x := by
  simp [bivariateV1, bivariateV2, Complex.mul_im]
  ring

/-- Under partial transposition averaging, V2 is the corresponding convex
combination of the original V2 and V1. -/
theorem bivariateV2_partialSymmetrization
    (a b c d : ℂ) (t x : ℝ) :
    bivariateV2 a
        ((t : ℂ) * b + (1 - t : ℝ) * c)
        ((t : ℂ) * c + (1 - t : ℝ) * b) d x =
      t * bivariateV2 a b c d x +
        (1 - t) * bivariateV1 a b c d x := by
  exact bivariateV1_partialSymmetrization a c b d t x

end RealRooted
