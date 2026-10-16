module

public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# The reverse-Hermite basis transform

This module defines the reverse-Hermite polynomials with positive recurrence
and the coefficientwise transform that sends `X ^ n` to the `n`th basis
polynomial. These are distinct from Mathlib's probabilists' Hermite
polynomials, whose recurrence has a negative derivative term.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

universe u

variable {R : Type u}

section Semiring

variable [Semiring R]

/-- The reverse-Hermite basis with recurrence
`B_(n+2) = X * (B_(n+1) + (n+1) * B_n)`. -/
def reverseHermiteBasis : ℕ → R[X]
  | 0 => 1
  | 1 => X
  | n + 2 =>
      X * (reverseHermiteBasis (n + 1) +
        C ((n : R) + 1) * reverseHermiteBasis n)

@[simp] theorem reverseHermiteBasis_zero :
    reverseHermiteBasis (R := R) 0 = 1 := rfl

@[simp] theorem reverseHermiteBasis_one :
    reverseHermiteBasis (R := R) 1 = X := rfl

@[simp] theorem reverseHermiteBasis_succ_succ (n : ℕ) :
    reverseHermiteBasis (R := R) (n + 2) =
      X * (reverseHermiteBasis (n + 1) +
        C ((n : R) + 1) * reverseHermiteBasis n) := rfl

/-- The linear transform sending `X ^ n` to `reverseHermiteBasis n`. -/
def reverseHermiteTransform (p : R[X]) : R[X] :=
  basisTransform reverseHermiteBasis p

@[simp] theorem reverseHermiteTransform_zero :
    reverseHermiteTransform (0 : R[X]) = 0 := by
  simp [reverseHermiteTransform]

theorem reverseHermiteTransform_add (p q : R[X]) :
    reverseHermiteTransform (p + q) =
      reverseHermiteTransform p + reverseHermiteTransform q :=
  basisTransform_add reverseHermiteBasis p q

theorem reverseHermiteTransform_smul (a : R) (p : R[X]) :
    reverseHermiteTransform (a • p) =
      C a * reverseHermiteTransform p :=
  basisTransform_smul reverseHermiteBasis a p

theorem reverseHermiteTransform_C_mul (a : R) (p : R[X]) :
    reverseHermiteTransform (C a * p) =
      C a * reverseHermiteTransform p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
    reverseHermiteTransform, basisTransform_smul]
  change C a * basisTransform reverseHermiteBasis p =
    C a * basisTransform reverseHermiteBasis p
  rfl

@[simp] theorem reverseHermiteTransform_C (a : R) :
    reverseHermiteTransform (C a) = C a := by
  rw [reverseHermiteTransform, basisTransform_C]
  simp only [reverseHermiteBasis_zero, mul_one]

@[simp] theorem reverseHermiteTransform_X_pow (n : ℕ) :
    reverseHermiteTransform (X ^ n : R[X]) = reverseHermiteBasis n :=
  basisTransform_X_pow reverseHermiteBasis n

@[simp] theorem reverseHermiteTransform_monomial (n : ℕ) (a : R) :
    reverseHermiteTransform (monomial n a) =
      C a * reverseHermiteBasis n :=
  basisTransform_monomial reverseHermiteBasis n a

@[simp] theorem reverseHermiteTransform_one :
    reverseHermiteTransform (1 : R[X]) = 1 := by
  simpa using reverseHermiteTransform_C (R := R) 1

@[simp] theorem reverseHermiteTransform_X :
    reverseHermiteTransform (X : R[X]) = X := by
  rw [show (X : R[X]) = X ^ 1 by simp,
    reverseHermiteTransform_X_pow]
  simp only [reverseHermiteBasis_one, pow_one]

end Semiring

section Real

/-- The reverse-Hermite basis is monic and has its indexed degree. -/
theorem reverseHermiteBasis_monic_natDegree :
    ∀ n : ℕ, (reverseHermiteBasis (R := ℝ) n).Monic ∧
      (reverseHermiteBasis (R := ℝ) n).natDegree = n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
      rw [reverseHermiteBasis_succ_succ]
      have hdegree :
          (C ((n : ℝ) + 1) * reverseHermiteBasis (R := ℝ) n).natDegree <
            (reverseHermiteBasis (R := ℝ) (n + 1)).natDegree := by
        rw [natDegree_C_mul (by positivity), hn.2, hn1.2]
        lia
      have hinnerMonic :
          (reverseHermiteBasis (R := ℝ) (n + 1) +
            C ((n : ℝ) + 1) * reverseHermiteBasis n).Monic := by
        apply hn1.1.add_of_left
        rw [degree_eq_natDegree
            (mul_ne_zero (C_ne_zero.mpr (by positivity)) hn.1.ne_zero),
          degree_eq_natDegree hn1.1.ne_zero]
        exact_mod_cast hdegree
      have hinnerDegree :
          (reverseHermiteBasis (R := ℝ) (n + 1) +
            C ((n : ℝ) + 1) * reverseHermiteBasis n).natDegree = n + 1 := by
        rw [natDegree_add_eq_left_of_natDegree_lt hdegree, hn1.2]
      constructor
      · exact monic_X.mul hinnerMonic
      · rw [monic_X.natDegree_mul hinnerMonic, natDegree_X, hinnerDegree]
        lia

/-- The reverse-Hermite transform preserves the top nonzero coefficient. -/
theorem coeff_reverseHermiteTransform_natDegree {p : ℝ[X]} (hp : p ≠ 0) :
    (reverseHermiteTransform p).coeff p.natDegree = p.leadingCoeff := by
  rw [reverseHermiteTransform, coeff_basisTransform, Polynomial.sum_def]
  have hnmem : p.natDegree ∈ p.support := natDegree_mem_support_of_nonzero hp
  rw [Finset.sum_eq_single_of_mem p.natDegree hnmem]
  · rw [coeff_natDegree]
    have hcoeff :
        (reverseHermiteBasis (R := ℝ) p.natDegree).coeff p.natDegree = 1 := by
      have htop :=
        (reverseHermiteBasis_monic_natDegree p.natDegree).1.coeff_natDegree
      rw [(reverseHermiteBasis_monic_natDegree p.natDegree).2] at htop
      exact htop
    simp [hcoeff]
  · intro n hn hne
    have hnle : n ≤ p.natDegree :=
      le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)
    have hnlt : n < p.natDegree := lt_of_le_of_ne hnle hne
    have hzero :
        (reverseHermiteBasis (R := ℝ) n).coeff p.natDegree = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [(reverseHermiteBasis_monic_natDegree n).2]
      exact hnlt
    simp [hzero]

/-- The reverse-Hermite transform preserves the degree of a nonzero polynomial. -/
theorem natDegree_reverseHermiteTransform {p : ℝ[X]} (hp : p ≠ 0) :
    (reverseHermiteTransform p).natDegree = p.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact basisTransform_natDegree_le_of_natDegree_le
      (fun n => (reverseHermiteBasis_monic_natDegree n).2.le) p
  · rw [coeff_reverseHermiteTransform_natDegree hp]
    exact leadingCoeff_ne_zero.mpr hp

end Real

section CommSemiring

variable [CommSemiring R]

/-- Multiplication by `X` before the reverse-Hermite transform becomes the
corresponding first-order input-derivative step afterwards. -/
theorem reverseHermiteTransform_X_mul (p : R[X]) :
    reverseHermiteTransform (X * p) =
      X * (reverseHermiteTransform p +
        reverseHermiteTransform p.derivative) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [mul_add, reverseHermiteTransform_add,
        reverseHermiteTransform_add, derivative_add,
        reverseHermiteTransform_add, hp, hq]
      ring
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      rw [show X * (C a * X ^ n) = C a * X ^ (n + 1) by ring,
        reverseHermiteTransform_C_mul,
        reverseHermiteTransform_X_pow,
        reverseHermiteTransform_C_mul,
        reverseHermiteTransform_X_pow]
      cases n with
      | zero =>
          simp
      | succ n =>
          have hder :
              (C a * X ^ (n + 1)).derivative =
                C (a * ((n : R) + 1)) * X ^ n := by
            simp only [derivative_mul, derivative_C, zero_mul, zero_add,
              derivative_pow, derivative_X]
            push_cast
            simp only [map_add, map_one, map_mul]
            ring
          rw [hder, reverseHermiteTransform_C_mul,
            reverseHermiteTransform_X_pow]
          simp only [reverseHermiteBasis_succ_succ]
          simp only [map_add, map_one, map_mul]
          ring

/-- The affine-factor form of `reverseHermiteTransform_X_mul`. -/
theorem reverseHermiteTransform_mul_X_add_C (r : R) (p : R[X]) :
    reverseHermiteTransform ((X + C r) * p) =
      (X + C r) * reverseHermiteTransform p +
        X * reverseHermiteTransform p.derivative := by
  rw [add_mul, reverseHermiteTransform_add,
    reverseHermiteTransform_X_mul, reverseHermiteTransform_C_mul]
  ring

end CommSemiring

end RealRooted
