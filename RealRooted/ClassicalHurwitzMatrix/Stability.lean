import RealRooted.ClassicalHurwitzMatrix

/-!
# Strict Hurwitz stability

This file separates the strict root-location hypothesis in the classical
Routh--Hurwitz theorem from `IsHurwitzStable`, the project's combinatorial
closed-half-plane predicate with nonnegative coefficients.
-/

open Polynomial

namespace RealRooted

/-- A complex polynomial is strictly left-half-plane stable when every root
has strictly negative real part. -/
def IsOpenLeftHalfPlaneStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → z.re < 0

namespace IsOpenLeftHalfPlaneStable

theorem ne_zero {p : ℂ[X]} (hp : IsOpenLeftHalfPlaneStable p) : p ≠ 0 := by
  intro hp0
  have := hp 0 (by simp [hp0])
  norm_num at this

/-- Strict left-half-plane stability implies the closed-half-plane exclusion
used by `IsRightHalfPlaneStable`. -/
theorem rightHalfPlaneStable {p : ℂ[X]}
    (hp : IsOpenLeftHalfPlaneStable p) : IsRightHalfPlaneStable p := by
  intro z hz hroot
  have := hp z hroot
  exact (not_lt_of_ge hz.le) this

theorem mul {p q : ℂ[X]} (hp : IsOpenLeftHalfPlaneStable p)
    (hq : IsOpenLeftHalfPlaneStable q) :
    IsOpenLeftHalfPlaneStable (p * q) := by
  intro z hroot
  rw [eval_mul, mul_eq_zero] at hroot
  exact hroot.elim (hp z) (hq z)

theorem of_mul_left {p q : ℂ[X]} (hpq : IsOpenLeftHalfPlaneStable (p * q)) :
    IsOpenLeftHalfPlaneStable p := by
  intro z hroot
  apply hpq z
  simp [hroot]

theorem of_mul_right {p q : ℂ[X]} (hpq : IsOpenLeftHalfPlaneStable (p * q)) :
    IsOpenLeftHalfPlaneStable q := by
  intro z hroot
  apply hpq z
  simp [hroot]

theorem mul_iff {p q : ℂ[X]} :
    IsOpenLeftHalfPlaneStable (p * q) ↔
      IsOpenLeftHalfPlaneStable p ∧ IsOpenLeftHalfPlaneStable q :=
  ⟨fun h => ⟨h.of_mul_left, h.of_mul_right⟩, fun h => h.1.mul h.2⟩

@[simp]
theorem C (c : ℂ) : IsOpenLeftHalfPlaneStable (C c) ↔ c ≠ 0 := by
  constructor
  · intro h hc
    subst c
    exact h.ne_zero (by simp)
  · intro hc z hroot
    have : c = 0 := by simpa using hroot
    exact (hc this).elim

end IsOpenLeftHalfPlaneStable

/-- Strict Hurwitz stability for a real polynomial, without a coefficient-sign
normalization. -/
def IsStrictlyHurwitzStable (p : ℝ[X]) : Prop :=
  IsOpenLeftHalfPlaneStable (complexify p)

namespace IsStrictlyHurwitzStable

theorem ne_zero {p : ℝ[X]} (hp : IsStrictlyHurwitzStable p) : p ≠ 0 := by
  intro hp0
  exact IsOpenLeftHalfPlaneStable.ne_zero hp (by simp [hp0])

/-- A strictly Hurwitz-stable polynomial has nonzero constant coefficient. -/
theorem coeff_zero_ne {p : ℝ[X]} (hp : IsStrictlyHurwitzStable p) :
    p.coeff 0 ≠ 0 := by
  intro hcoeff
  have hroot : (complexify p).eval 0 = 0 := by
    simp [complexify, ← Polynomial.coeff_zero_eq_eval_zero, hcoeff]
  have := hp 0 hroot
  norm_num at this

/-- Under the combinatorial sign normalization, strict stability supplies the
positive constant coefficient assumed in Holtz's criterion. -/
theorem coeff_zero_pos {p : ℝ[X]} (hp : IsStrictlyHurwitzStable p)
    (hnn : HasNonnegCoeffs p) : 0 < p.coeff 0 :=
  lt_of_le_of_ne (hnn 0) hp.coeff_zero_ne.symm

theorem rightHalfPlaneStable {p : ℝ[X]} (hp : IsStrictlyHurwitzStable p) :
    IsRightHalfPlaneStable (complexify p) :=
  IsOpenLeftHalfPlaneStable.rightHalfPlaneStable hp

/-- Adding the project's nonnegative-coefficient normalization turns strict
root location into its existing quasi-stable interface. -/
theorem isHurwitzStable {p : ℝ[X]} (hp : IsStrictlyHurwitzStable p)
    (hnn : HasNonnegCoeffs p) : IsHurwitzStable p :=
  ⟨hnn, hp.rightHalfPlaneStable⟩

theorem mul {p q : ℝ[X]} (hp : IsStrictlyHurwitzStable p)
    (hq : IsStrictlyHurwitzStable q) : IsStrictlyHurwitzStable (p * q) := by
  simpa only [IsStrictlyHurwitzStable, complexify, Polynomial.map_mul] using
    IsOpenLeftHalfPlaneStable.mul hp hq

theorem mul_iff {p q : ℝ[X]} :
    IsStrictlyHurwitzStable (p * q) ↔
      IsStrictlyHurwitzStable p ∧ IsStrictlyHurwitzStable q := by
  simpa only [IsStrictlyHurwitzStable, complexify, Polynomial.map_mul] using
    (IsOpenLeftHalfPlaneStable.mul_iff :
      IsOpenLeftHalfPlaneStable (complexify p * complexify q) ↔ _)

@[simp]
theorem C (c : ℝ) : IsStrictlyHurwitzStable (C c) ↔ c ≠ 0 := by
  simp [IsStrictlyHurwitzStable, complexify]

theorem not_X : ¬ IsStrictlyHurwitzStable (X : ℝ[X]) := by
  intro h
  exact h.coeff_zero_ne (by simp)

/-- The monic linear base case fixes the sign direction for strict Hurwitz
stability. -/
theorem X_add_C (a : ℝ) :
    IsStrictlyHurwitzStable (X + Polynomial.C a) ↔ 0 < a := by
  constructor
  · intro h
    have hroot : (complexify (X + Polynomial.C a)).eval (-(a : ℂ)) = 0 := by
      simp [complexify]
    simpa using h (-(a : ℂ)) hroot
  · intro ha z hroot
    have hz : z + (a : ℂ) = 0 := by
      simpa [complexify] using hroot
    rw [eq_neg_of_add_eq_zero_left hz]
    simpa using ha

end IsStrictlyHurwitzStable

end RealRooted
