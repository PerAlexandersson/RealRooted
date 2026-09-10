import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization.Derivative
import RealRooted.BoundarySpecializationGeneral
import RealRooted.Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Coefficient extraction from finite-variable stable polynomials

This file combines finite-variable derivative stability with boundary
specialization to extract coefficients in one distinguished variable.
-/

namespace RealRooted

noncomputable section

private theorem specializeZero_none_eq_rename_optionEquivLeft_coeff_zero
    {σ : Type*} (P : MvPolynomial (Option σ) ℂ) :
    MvPolynomial.specializeZero none P =
      MvPolynomial.rename some ((MvPolynomial.optionEquivLeft ℂ σ P).coeff 0) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [MvPolynomial.specializeZero_add, hP, hQ]
  | mul_X P i hP =>
      cases i with
      | none =>
          have hX : MvPolynomial.specializeZero none
              (MvPolynomial.X none : MvPolynomial (Option σ) ℂ) = 0 := by
            simp [MvPolynomial.X, MvPolynomial.specializeZero_monomial]
          rw [MvPolynomial.specializeZero_mul, hP, hX]
          simp
      | some i =>
          have hX : MvPolynomial.specializeZero none
              (MvPolynomial.X (some i) : MvPolynomial (Option σ) ℂ) =
                MvPolynomial.X (some i) := by
            simp [MvPolynomial.X, MvPolynomial.specializeZero_monomial]
          rw [MvPolynomial.specializeZero_mul, hP, hX]
          simp

private theorem optionEquivLeft_iterate_pderiv_none
    {σ : Type*} (P : MvPolynomial (Option σ) ℂ) (k : ℕ) :
    MvPolynomial.optionEquivLeft ℂ σ ((MvPolynomial.pderiv none)^[k] P) =
      (Polynomial.derivative^[k]) (MvPolynomial.optionEquivLeft ℂ σ P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        MvPolynomial.optionEquivLeft_pderiv_none, ih]

/-- Iterating the distinguished partial derivative and then setting that
variable to zero extracts the corresponding coefficient, multiplied by a
factorial. -/
theorem _root_.MvPolynomial.specializeZero_none_iterate_pderiv_eq_factorial_coeff
    {σ : Type*} (P : MvPolynomial (Option σ) ℂ) (k : ℕ) :
    MvPolynomial.specializeZero none ((MvPolynomial.pderiv none)^[k] P) =
      MvPolynomial.C (k.factorial : ℂ) *
        MvPolynomial.rename some
          ((MvPolynomial.optionEquivLeft ℂ σ P).coeff k) := by
  rw [specializeZero_none_eq_rename_optionEquivLeft_coeff_zero,
    optionEquivLeft_iterate_pderiv_none, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

private theorem iterate_pderiv_none_zero_or_of_finite
    {σ : Type*} [Finite σ] {P : MvPolynomial (Option σ) ℂ}
    (hP : MvUpperHalfPlaneStable P) (k : ℕ) :
    MvUpperHalfPlaneStableOrZero ((MvPolynomial.pderiv none)^[k] P) := by
  induction k with
  | zero => exact hP.orZero
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with hzero | hstable
      · left
        simp [hzero]
      · exact hstable.pderiv_zero_or_of_finite none

/-- Every coefficient in one distinguished variable of a finite-variable
stable polynomial is either zero or stable in the remaining variables. -/
theorem MvUpperHalfPlaneStable.optionEquivLeft_coeff_zero_or_of_finite
    {σ : Type*} [Finite σ] {P : MvPolynomial (Option σ) ℂ}
    (hP : MvUpperHalfPlaneStable P) (k : ℕ) :
    MvUpperHalfPlaneStableOrZero
      ((MvPolynomial.optionEquivLeft ℂ σ P).coeff k) := by
  have hderiv := iterate_pderiv_none_zero_or_of_finite hP k
  have hspecial : MvUpperHalfPlaneStableOrZero
      (MvPolynomial.specializeZero none ((MvPolynomial.pderiv none)^[k] P)) := by
    rcases hderiv with hzero | hstable
    · left
      simp [hzero]
    · exact hstable.specializeZero_zero_or_general none
  rw [MvPolynomial.specializeZero_none_iterate_pderiv_eq_factorial_coeff] at hspecial
  rcases hspecial with hzero | hstable
  · left
    have hrename : MvPolynomial.rename some
        ((MvPolynomial.optionEquivLeft ℂ σ P).coeff k) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (MvPolynomial.C_ne_zero.mpr
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)))
    exact (MvPolynomial.rename_eq_zero_iff_of_injective _
      (Option.some_injective σ)).mp hrename
  · right
    intro z hz
    let w : Option σ → ℂ := fun o => o.elim Complex.I z
    have hw : ∀ o, 0 < (w o).im := by
      intro o
      cases o with
      | none => simp [w]
      | some i => exact hz i
    have hne := hstable w hw
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_rename] at hne
    have hcomp : w ∘ some = z := by
      funext i
      rfl
    rw [hcomp] at hne
    intro hzero
    rw [hzero, mul_zero] at hne
    exact hne rfl

end

end RealRooted
