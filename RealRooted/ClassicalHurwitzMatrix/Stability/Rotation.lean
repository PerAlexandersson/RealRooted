import RealRooted.ClassicalHurwitzMatrix.Stability

/-!
# Rotation between strict left- and upper-half-plane stability

The substitution `X ↦ -iX` sends the closed upper half-plane to the closed
right half-plane. This file records the exact root transport needed before the
Hermite--Biehler analysis of a strict Routh step.
-/

open Polynomial

namespace RealRooted

/-- A complex polynomial has no root in the closed upper half-plane. -/
def IsClosedUpperHalfPlaneStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, 0 ≤ z.im → p.eval z ≠ 0

namespace IsClosedUpperHalfPlaneStable

theorem ne_zero {p : ℂ[X]} (hp : IsClosedUpperHalfPlaneStable p) : p ≠ 0 := by
  intro hp0
  exact hp 0 (by simp) (by simp [hp0])

theorem upperHalfPlaneStable {p : ℂ[X]}
    (hp : IsClosedUpperHalfPlaneStable p) : IsUpperHalfPlaneStable p :=
  fun z hz ↦ hp z hz.le

end IsClosedUpperHalfPlaneStable

/-- Rotate the variable so that strict left-half-plane root location becomes
closed-upper-half-plane exclusion. -/
noncomputable def rotateLeftHalfPlaneToUpper (p : ℝ[X]) : ℂ[X] :=
  (complexify p).comp (C (-Complex.I) * X)

@[simp]
theorem eval_rotateLeftHalfPlaneToUpper (p : ℝ[X]) (z : ℂ) :
    (rotateLeftHalfPlaneToUpper p).eval z =
      (complexify p).eval (-Complex.I * z) := by
  simp [rotateLeftHalfPlaneToUpper, Polynomial.eval_comp]

theorem isRoot_rotateLeftHalfPlaneToUpper_iff (p : ℝ[X]) (z : ℂ) :
    (rotateLeftHalfPlaneToUpper p).IsRoot z ↔
      (complexify p).IsRoot (-Complex.I * z) := by
  simp only [Polynomial.IsRoot, eval_rotateLeftHalfPlaneToUpper]

theorem isRoot_rotateLeftHalfPlaneToUpper_I_mul_iff (p : ℝ[X]) (z : ℂ) :
    (rotateLeftHalfPlaneToUpper p).IsRoot (Complex.I * z) ↔
      (complexify p).IsRoot z := by
  rw [isRoot_rotateLeftHalfPlaneToUpper_iff]
  have hrotate : -Complex.I * (Complex.I * z) = z := by
    rw [neg_mul, ← mul_assoc, Complex.I_mul_I]
    simp
  rw [hrotate]

/-- Evaluation of the rotated odd/even polynomial at the negative square of
the new variable. This fixes the signs used by the Hermite--Biehler bridge. -/
theorem eval_rotateLeftHalfPlaneToUpper_oddEvenPolynomial
    (odd even : ℝ[X]) (z : ℂ) :
    (rotateLeftHalfPlaneToUpper (oddEvenPolynomial odd even)).eval z =
      (complexify even).eval (-(z ^ 2)) -
        Complex.I * z * (complexify odd).eval (-(z ^ 2)) := by
  rw [eval_rotateLeftHalfPlaneToUpper,
    eval_complexify_oddEvenPolynomial]
  have hsquare : (-Complex.I * z) ^ 2 = -(z ^ 2) := by
    simp [mul_pow, Complex.I_sq]
  rw [hsquare]
  ring

/-- Strict left-half-plane stability is exactly closed-upper-half-plane
exclusion after the substitution `X ↦ -iX`. -/
theorem isClosedUpperHalfPlaneStable_rotateLeftHalfPlaneToUpper_iff
    (p : ℝ[X]) :
    IsClosedUpperHalfPlaneStable (rotateLeftHalfPlaneToUpper p) ↔
      IsStrictlyHurwitzStable p := by
  constructor
  · intro hp z hz
    by_contra hzneg
    have hzre : 0 ≤ z.re := le_of_not_gt hzneg
    have hwim : 0 ≤ (Complex.I * z).im := by
      simpa [Complex.mul_im] using hzre
    have hne := hp (Complex.I * z) hwim
    apply hne
    rw [eval_rotateLeftHalfPlaneToUpper]
    have hrotate : -Complex.I * (Complex.I * z) = z := by
      rw [neg_mul, ← mul_assoc, Complex.I_mul_I]
      simp
    rw [hrotate, hz]
  · intro hp z hzim hroot
    rw [eval_rotateLeftHalfPlaneToUpper] at hroot
    have hlt := hp (-Complex.I * z) hroot
    have hre : (-Complex.I * z).re = z.im := by
      simp [Complex.mul_re]
    rw [hre] at hlt
    exact (not_lt_of_ge hzim) hlt

end RealRooted
