import Mathlib.RingTheory.Polynomial.Pochhammer
import RealRooted.Transforms.BrandenE.Basic

/-!
# Falling-factorial inverse of Brändén's E transform

Mathlib's descending Pochhammer polynomials provide the inverse basis to the
ordered Bell basis.  The unnormalized image identity is ring-generic; the
normalized inverse requires characteristic zero so that factorials are units.
-/

open Polynomial

noncomputable section

namespace RealRooted

universe u

variable {R : Type u}

/-- The `E` transform sends the descending Pochhammer polynomial to a scaled
monomial. -/
theorem brandenE_descPochhammer [CommRing R] :
    ∀ n : ℕ,
      brandenE (descPochhammer R n) = C (n.factorial : R) * X ^ n
  | 0 => by
      rw [show descPochhammer R 0 = 1 by simp,
        show (1 : R[X]) = X ^ 0 by simp, brandenE_X_pow]
      simp
  | n + 1 => by
      rw [descPochhammer_succ_right]
      rw [mul_comm (descPochhammer R n) (X - (n : R[X]))]
      rw [show X - (n : R[X]) = X + C (-(n : R)) by
        simp [sub_eq_add_neg]]
      rw [brandenE_mul_X_add_C, brandenE_descPochhammer]
      simp only [derivative_mul, derivative_C, zero_mul, zero_add]
      rw [Nat.factorial_succ]
      cases n with
      | zero => simp
      | succ n =>
          rw [Polynomial.derivative_X_pow_succ]
          push_cast
          simp only [map_add, map_one, map_mul, map_neg]
          ring

/-- Brändén's `E` transform is injective whenever factorials remain nonzero. -/
theorem brandenE_injective [CommRing R] [IsDomain R] [CharZero R] :
    Function.Injective (brandenE (R := R)) :=
  Polynomial.basisTransform_injective_of_natDegree_eq
    (orderedBellPolynomial_natDegree (R := R))
    (orderedBellPolynomial_ne_zero (R := R))

section Field

variable [Field R] [CharZero R]

/-- The normalized descending-Pochhammer basis inverse to the ordered Bell
basis. -/
def brandenEPreimageBasis (n : ℕ) : R[X] :=
  C ((n.factorial : R)⁻¹) * descPochhammer R n

theorem brandenE_preimageBasis (n : ℕ) :
    brandenE (brandenEPreimageBasis (R := R) n) = X ^ n := by
  rw [brandenEPreimageBasis, brandenE_C_mul,
    brandenE_descPochhammer, ← mul_assoc, ← C_mul]
  have hfac : (n.factorial : R) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp [hfac]

/-- The coefficientwise transform in the normalized descending-Pochhammer
basis. -/
def brandenEPreimage (p : R[X]) : R[X] :=
  Polynomial.basisTransform (brandenEPreimageBasis (R := R)) p

/-- `brandenEPreimage` is a right inverse of `brandenE`. -/
theorem brandenE_preimage (p : R[X]) :
    brandenE (brandenEPreimage p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      change brandenE (Polynomial.basisTransform brandenEPreimageBasis p) = p at hp
      change brandenE (Polynomial.basisTransform brandenEPreimageBasis q) = q at hq
      rw [brandenEPreimage, Polynomial.basisTransform_add, brandenE_add, hp, hq]
  | monomial n a =>
      rw [brandenEPreimage, Polynomial.basisTransform_monomial,
        brandenE_C_mul, brandenE_preimageBasis]
      simp [Polynomial.X_pow_eq_monomial]

theorem brandenEPreimage_rightInverse :
    Function.RightInverse (brandenEPreimage (R := R)) (brandenE (R := R)) :=
  brandenE_preimage

/-- The normalized preimage transform is also a left inverse. -/
theorem brandenEPreimage_brandenE (p : R[X]) :
    brandenEPreimage (brandenE p) = p :=
  (brandenE_injective (R := R)) (brandenE_preimage (brandenE p))

theorem brandenEPreimage_leftInverse :
    Function.LeftInverse (brandenEPreimage (R := R)) (brandenE (R := R)) :=
  brandenEPreimage_brandenE

/-- Brändén's `E` transform is a bijection in characteristic zero. -/
theorem brandenE_bijective : Function.Bijective (brandenE (R := R)) := by
  refine ⟨brandenE_injective, ?_⟩
  intro p
  exact ⟨brandenEPreimage p, brandenE_preimage p⟩

end Field

end RealRooted
