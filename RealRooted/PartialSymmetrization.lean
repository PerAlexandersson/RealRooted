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
