import RealRooted.Multiaffine

/-!
# Partial symmetrization

This file develops the bivariate coefficient identities used in the
Borcea--Brändén proof that transposition averages preserve stability.
-/

namespace RealRooted

/-- The first real quadratic form from Borcea--Brändén, Part II, Lemma 1.4. -/
def bivariateV1 (a b c d : ℂ) (x : ℝ) : ℝ :=
  (a * star c).im + (a * star d + b * star c).im * x +
    (b * star d).im * x ^ 2

/-- The second real quadratic form from Borcea--Brändén, Part II, Lemma 1.4. -/
def bivariateV2 (a b c d : ℂ) (x : ℝ) : ℝ :=
  (a * star b).im + (a * star d + c * star b).im * x +
    (c * star d).im * x ^ 2

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
  simp [Complex.div_im, Complex.normSq, bivariateV2]
  ring

/-- A positive imaginary part of `c / d` keeps `c + d * x` nonzero on the
real boundary. This is the denominator observation in Part II, Lemma 1.4. -/
theorem add_mul_real_ne_zero_of_im_div_pos
    (c d : ℂ) (x : ℝ) (h : 0 < (c / d).im) :
    c + d * (x : ℂ) ≠ 0 := by
  intro hzero
  have hd : d ≠ 0 := by
    intro hd
    simp [hd] at h
  have hratio : c / d = -(x : ℂ) := by
    apply (div_eq_iff hd).2
    linear_combination hzero
  rw [hratio] at h
  simp at h

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
  have hden := add_mul_real_ne_zero_of_im_div_pos b d x h
  have hnorm : 0 < Complex.normSq (b + d * (x : ℂ)) :=
    Complex.normSq_pos.mpr hden
  rw [im_bivariateQuotient_eq_bivariateV2_div_normSq]
  exact div_pos_iff_of_pos_right hnorm

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
  simp [bivariateV1, bivariateV2, Complex.mul_im]
  ring

end RealRooted
