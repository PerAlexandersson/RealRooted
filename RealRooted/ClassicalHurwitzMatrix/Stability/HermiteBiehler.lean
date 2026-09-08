import RealRooted.ClassicalHurwitzMatrix.Stability.Rotation
import RealRooted.HermiteBiehler.Converse

/-!
# Hermite--Biehler consequences of strict Hurwitz stability

This module transports the rotated odd/even polynomial into the existing
Hermite--Biehler converse. Leading-coefficient sign choices stay explicit: the
two useful normalizations are the original rotated pair and the pair obtained
by multiplying its Hermite--Biehler polynomial by `i`.
-/

open Polynomial

noncomputable section

namespace RealRooted

namespace IsUpperHalfPlaneStable

/-- Multiplication by a nonzero constant preserves upper-half-plane stability. -/
theorem C_mul {p : ℂ[X]} (hp : IsUpperHalfPlaneStable p)
    {c : ℂ} (hc : c ≠ 0) :
    IsUpperHalfPlaneStable (C c * p) := by
  intro z hz
  simp only [eval_mul, eval_C]
  exact mul_ne_zero hc (hp z hz)

end IsUpperHalfPlaneStable

/-- Multiplication by `i` swaps the two Hermite--Biehler parts and negates the
new real part. -/
theorem C_I_mul_hermiteBiehlerPolynomial (f g : ℝ[X]) :
    C Complex.I * hermiteBiehlerPolynomial f g =
      hermiteBiehlerPolynomial (-g) f := by
  simp only [hermiteBiehlerPolynomial, complexify, Polynomial.map_neg]
  rw [mul_add, ← mul_assoc, ← C_mul, Complex.I_mul_I]
  simp [add_comm]

/-- With positive leading coefficients in the direct normalization, strict
Hurwitz stability forces the rotated odd part to be in proper position with
respect to the rotated even part. -/
theorem IsStrictlyHurwitzStable.prec_rotatedParts_of_posLeading
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (heven : HasPosLeadingCoeff (hurwitzRotatedEvenPart even))
    (hodd : HasPosLeadingCoeff (hurwitzRotatedOddPart odd))
    (hdegree : 1 ≤ (hurwitzRotatedEvenPart even).natDegree) :
    Prec (hurwitzRotatedOddPart odd) (hurwitzRotatedEvenPart even) :=
  prec_of_stable_general heven hodd
    h.upperHalfPlaneStable_rotatedParts hdegree

/-- With positive leading coefficients after multiplication by `i`, strict
Hurwitz stability forces the rotated even part to be in proper position with
respect to the negated rotated odd part. -/
theorem IsStrictlyHurwitzStable.prec_rotatedParts_swapped_of_posLeading
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff (-hurwitzRotatedOddPart odd))
    (heven : HasPosLeadingCoeff (hurwitzRotatedEvenPart even))
    (hdegree : 1 ≤ (-hurwitzRotatedOddPart odd).natDegree) :
    Prec (hurwitzRotatedEvenPart even) (-hurwitzRotatedOddPart odd) := by
  apply prec_of_stable_general hodd heven _ hdegree
  rw [← C_I_mul_hermiteBiehlerPolynomial]
  exact h.upperHalfPlaneStable_rotatedParts.C_mul (by simp)

end RealRooted
