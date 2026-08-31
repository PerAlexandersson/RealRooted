import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# Polynomial basis transforms

The coefficientwise linear map sending `X ^ n` to a prescribed polynomial
`B n`, together with its elementary algebra and the injectivity criterion for
degree-triangular bases.
-/

open Finset

noncomputable section

namespace Polynomial

universe u

variable {R : Type u}

section Semiring

variable [Semiring R]

/-- The linear basis transform sending `X ^ n` to `B n`. -/
def basisTransform (B : ℕ → R[X]) (p : R[X]) : R[X] :=
  p.sum fun n a => C a * B n

theorem coeff_basisTransform (B : ℕ → R[X]) (p : R[X]) (j : ℕ) :
    (basisTransform B p).coeff j = p.sum fun n a => a * (B n).coeff j := by
  simp [basisTransform, Polynomial.coeff_sum, Polynomial.coeff_C_mul]

@[simp] theorem basisTransform_zero (B : ℕ → R[X]) :
    basisTransform B 0 = 0 := by
  simp [basisTransform]

@[simp] theorem basisTransform_monomial (B : ℕ → R[X]) (n : ℕ) (a : R) :
    basisTransform B (monomial n a) = C a * B n := by
  rw [basisTransform, Polynomial.sum_monomial_index]
  simp

@[simp] theorem basisTransform_C (B : ℕ → R[X]) (a : R) :
    basisTransform B (C a) = C a * B 0 := by
  simpa using basisTransform_monomial B 0 a

@[simp] theorem basisTransform_X_pow (B : ℕ → R[X]) (n : ℕ) :
    basisTransform B (X ^ n) = B n := by
  rw [show (X ^ n : R[X]) = monomial n 1 by simp [Polynomial.X_pow_eq_monomial]]
  simp

theorem basisTransform_add (B : ℕ → R[X]) (p q : R[X]) :
    basisTransform B (p + q) = basisTransform B p + basisTransform B q := by
  rw [basisTransform, basisTransform, basisTransform]
  exact Polynomial.sum_add_index p q (fun n a => C a * B n) (by simp) (by simp [add_mul])

theorem basisTransform_smul (B : ℕ → R[X]) (a : R) (p : R[X]) :
    basisTransform B (a • p) = C a * basisTransform B p := by
  rw [basisTransform, basisTransform]
  rw [Polynomial.sum_smul_index]
  · simp [Polynomial.sum_def, Finset.mul_sum, mul_assoc]
  · simp

end Semiring

section Differential

variable [CommSemiring R]

/-- A basis transform transports multiplication by `X` to a first-order
differential operator when its basis satisfies the corresponding successor
recurrence. -/
theorem basisTransform_X_mul_of_succ_derivative
    (B : ℕ → R[X]) (A D : R[X])
    (hsucc : ∀ n, B (n + 1) = A * B n + D * (B n).derivative)
    (p : R[X]) :
    basisTransform B (X * p) =
      A * basisTransform B p + D * (basisTransform B p).derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [mul_add, basisTransform_add, hp, hq, derivative_add]
      ring
  | monomial n a =>
      rw [Polynomial.X_mul_monomial, basisTransform_monomial, hsucc]
      simp [Polynomial.derivative_mul]
      ring

/-- The affine factor version of
`basisTransform_X_mul_of_succ_derivative`. -/
theorem basisTransform_mul_X_add_C_of_succ_derivative
    (B : ℕ → R[X]) (A D : R[X])
    (hsucc : ∀ n, B (n + 1) = A * B n + D * (B n).derivative)
    (r : R) (p : R[X]) :
    basisTransform B ((X + C r) * p) =
      (A + C r) * basisTransform B p + D * (basisTransform B p).derivative := by
  rw [add_mul, basisTransform_add,
    basisTransform_X_mul_of_succ_derivative B A D hsucc]
  rw [show C r * p = r • p by rw [Polynomial.smul_eq_C_mul],
    basisTransform_smul]
  ring

end Differential

section Domain

variable [CommRing R] [IsDomain R]

/-- A degree-triangular polynomial basis defines an injective basis transform. -/
theorem basisTransform_injective_of_natDegree_eq
    {B : ℕ → R[X]}
    (hdegree : ∀ n, (B n).natDegree = n)
    (hnonzero : ∀ n, B n ≠ 0) :
    Function.Injective (basisTransform B) := by
  have htransform_ne : ∀ {p : R[X]}, p ≠ 0 → basisTransform B p ≠ 0 := by
    intro p hp hzero
    let d := p.natDegree
    have hdmem : d ∈ p.support := natDegree_mem_support_of_nonzero hp
    have hcoeff := congrArg (fun q : R[X] => q.coeff d) hzero
    rw [coeff_basisTransform, Polynomial.sum_def] at hcoeff
    have hsum :
        ∑ k ∈ p.support, p.coeff k * (B k).coeff d =
          p.coeff d * (B d).coeff d := by
      apply Finset.sum_eq_single d
      · intro k hk hkd
        have hk_le : k ≤ d :=
          le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
        have hk_lt : k < d := lt_of_le_of_ne hk_le hkd
        have hvanish : (B k).coeff d = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          simp_all
        simp [hvanish]
      · simp_all
    rw [hsum] at hcoeff
    have hpcoeff : p.coeff d ≠ 0 := Polynomial.mem_support_iff.mp hdmem
    have hBcoeff : (B d).coeff d ≠ 0 := by
      have hlead : (B d).leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr (hnonzero d)
      rw [← coeff_natDegree, hdegree d] at hlead
      simpa using hlead
    simp_all
  intro p q hpq
  apply sub_eq_zero.mp
  by_contra hsub
  apply htransform_ne hsub
  rw [show p - q = p + (-1 : R) • q by simp [sub_eq_add_neg],
    basisTransform_add, basisTransform_smul, hpq]
  simp

end Domain

end Polynomial
