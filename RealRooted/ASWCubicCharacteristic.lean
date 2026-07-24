import RealRooted.ASWCubicRecurrence
import RealRooted.CubicDiscriminant

/-!
# Characteristic polynomials for cubic ASW minor recurrences

This file records the characteristic polynomials of the two cubic Toeplitz
minor recurrences. It proves their discriminant scaling and the root
transformation from the shift-one recurrence to the shift-two recurrence.

The shift-two roots are the pairwise products of the shift-one roots divided
by the positive constant coefficient. This normalization is needed for both
the elementary symmetric functions and the later modulus comparison.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Characteristic polynomial of the shift-one cubic minor recurrence. -/
def aswCubicShiftOneCharPoly {R : Type*} [CommRing R] (a b c d : R) : R[X] :=
  X ^ 3 - C b * X ^ 2 + C (a * c) * X - C (a ^ 2 * d)

/-- Characteristic polynomial of the shift-two cubic minor recurrence. -/
def aswCubicShiftTwoCharPoly {R : Type*} [CommRing R] (a b c d : R) : R[X] :=
  X ^ 3 - C c * X ^ 2 + C (b * d) * X - C (a * d ^ 2)

/-- The shift-one characteristic discriminant is the original coefficient
discriminant multiplied by the square of the constant coefficient. -/
theorem cubicDiscr_aswCubicShiftOneCharPoly (a b c d : ℝ) :
    cubicDiscr (aswCubicShiftOneCharPoly a b c d) =
      a ^ 2 * cubicDiscr (C d * X ^ 3 + C c * X ^ 2 + C b * X + C a) := by
  rw [show aswCubicShiftOneCharPoly a b c d =
      C 1 * X ^ 3 + C (-b) * X ^ 2 + C (a * c) * X + C (-(a ^ 2 * d)) by
    simp only [aswCubicShiftOneCharPoly, C_1, C_neg]
    ring]
  rw [cubicDiscr_of_coeffs, cubicDiscr_of_coeffs]
  ring

/-- The shift-two characteristic discriminant is the original coefficient
discriminant multiplied by the square of the leading coefficient. -/
theorem cubicDiscr_aswCubicShiftTwoCharPoly (a b c d : ℝ) :
    cubicDiscr (aswCubicShiftTwoCharPoly a b c d) =
      d ^ 2 * cubicDiscr (C d * X ^ 3 + C c * X ^ 2 + C b * X + C a) := by
  rw [show aswCubicShiftTwoCharPoly a b c d =
      C 1 * X ^ 3 + C (-c) * X ^ 2 + C (b * d) * X + C (-(a * d ^ 2)) by
    simp only [aswCubicShiftTwoCharPoly, C_1, C_neg]
    ring]
  rw [cubicDiscr_of_coeffs, cubicDiscr_of_coeffs]
  ring

/-- Pairwise products of the shift-one roots, scaled by the nonzero constant
coefficient, have the elementary symmetric functions of the shift-two roots. -/
theorem aswCubicShiftTwo_roots_from_shiftOne
    (a b c d r z w : ℂ)
    (hsum : r + z + w = b)
    (hpairs : r * z + z * w + w * r = a * c)
    (hprod : r * z * w = a ^ 2 * d)
    (ha : a ≠ 0) :
    r * z / a + r * w / a + z * w / a = c ∧
      (r * z / a) * (r * w / a) +
          (r * w / a) * (z * w / a) +
            (z * w / a) * (r * z / a) = b * d ∧
      (r * z / a) * (r * w / a) * (z * w / a) = a * d ^ 2 := by
  constructor
  · field_simp [ha]
    linear_combination hpairs
  constructor
  · field_simp [ha]
    calc
      r * z * w * (r + w + z) = (r * z * w) * (r + z + w) := by ring
      _ = (a ^ 2 * d) * b := by rw [hprod, hsum]
      _ = a ^ 2 * b * d := by ring
  · field_simp [ha]
    calc
      r ^ 2 * z ^ 2 * w ^ 2 = (r * z * w) ^ 2 := by ring
      _ = (a ^ 2 * d) ^ 2 := by rw [hprod]
      _ = a ^ 4 * d ^ 2 := by ring

/-- The scaled pairwise products of a shift-one root triple factor the
shift-two characteristic polynomial. -/
theorem aswCubicShiftTwoCharPoly_eq_prod_from_shiftOne
    (a b c d r z w : ℂ)
    (hsum : r + z + w = b)
    (hpairs : r * z + z * w + w * r = a * c)
    (hprod : r * z * w = a ^ 2 * d)
    (ha : a ≠ 0) :
    aswCubicShiftTwoCharPoly a b c d =
      (X - C (r * z / a)) * (X - C (r * w / a)) * (X - C (z * w / a)) := by
  obtain ⟨hsum', hpairs', hprod'⟩ :=
    aswCubicShiftTwo_roots_from_shiftOne a b c d r z w hsum hpairs hprod ha
  unfold aswCubicShiftTwoCharPoly
  rw [← hsum', ← hpairs', ← hprod']
  simp only [C_add, C_mul]
  ring

end RealRooted

