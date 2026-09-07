import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.Transforms.BrandenE.OrderedBell

/-!
# Brändén's E transform

The `E` transform is the coefficientwise basis transform sending `X ^ n` to
the `n`th ordered Bell polynomial.  This file contains its coefficient-generic
linear and first-order differential algebra.
-/

open Polynomial

noncomputable section

namespace RealRooted

universe u

variable {R : Type u}

section Semiring

variable [Semiring R]

/-- Brändén's `E` transform, expressed in the ordered Bell basis. -/
def brandenE (p : R[X]) : R[X] :=
  Polynomial.basisTransform (orderedBellPolynomial (R := R)) p

@[simp] theorem brandenE_zero : brandenE (0 : R[X]) = 0 :=
  Polynomial.basisTransform_zero _

theorem brandenE_add (p q : R[X]) :
    brandenE (p + q) = brandenE p + brandenE q :=
  Polynomial.basisTransform_add _ p q

theorem brandenE_smul (a : R) (p : R[X]) :
    brandenE (a • p) = C a * brandenE p :=
  Polynomial.basisTransform_smul _ a p

theorem brandenE_C_mul (a : R) (p : R[X]) :
    brandenE (C a * p) = C a * brandenE p := by
  rw [Polynomial.C_mul', brandenE_smul]

/-- Brändén's transform distributes over finite polynomial sums. -/
theorem brandenE_finset_sum {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    brandenE (∑ i ∈ s, f i) = ∑ i ∈ s, brandenE (f i) :=
  Polynomial.basisTransform_finset_sum _ s f

@[simp] theorem brandenE_X_pow (n : ℕ) :
    brandenE (X ^ n : R[X]) = orderedBellPolynomial n :=
  Polynomial.basisTransform_X_pow _ n

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- Multiplication by `X` before `brandenE` becomes the Euler differential
operator afterwards. -/
theorem brandenE_X_mul (p : R[X]) :
    brandenE (X * p) =
      X * brandenE p + X * (1 + X) * (brandenE p).derivative :=
  Polynomial.basisTransform_X_mul_of_succ_derivative
    (orderedBellPolynomial (R := R)) X (X * (1 + X))
    orderedBellPolynomial_succ p

/-- Affine-factor form of `brandenE_X_mul`. -/
theorem brandenE_mul_X_add_C (r : R) (p : R[X]) :
    brandenE ((X + C r) * p) =
      (X + C r) * brandenE p +
        X * (1 + X) * (brandenE p).derivative :=
  Polynomial.basisTransform_mul_X_add_C_of_succ_derivative
    (orderedBellPolynomial (R := R)) X (X * (1 + X))
    orderedBellPolynomial_succ r p

/-- Reciprocal affine-factor form of `brandenE_X_mul`. -/
theorem brandenE_one_add_C_mul_X (a : R) (p : R[X]) :
    brandenE ((1 + C a * X) * p) =
      (1 + C a * X) * brandenE p +
        C a * X * (1 + X) * (brandenE p).derivative := by
  rw [show (1 + C a * X) * p = p + C a * (X * p) by ring,
    brandenE_add, brandenE_C_mul, brandenE_X_mul]
  ring

end CommSemiring

end RealRooted
