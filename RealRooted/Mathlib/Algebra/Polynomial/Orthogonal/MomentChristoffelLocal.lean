/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentAlgebra
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentShift

/-!
# Christoffel identities with finite nondegeneracy hypotheses

Only the displayed finite Hankel determinants and denominator norm are
required. The numerator norm may vanish. These identities therefore include
the final step of a finite-support Stieltjes fraction.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- A finite Christoffel identity valid even when the shifted numerator norm
vanishes at the end of the support. -/
theorem X_mul_monicMomentPolynomial_shift_of_isUnit
    (μ : ℕ → K) (n : ℕ)
    (hd : IsUnit (momentHankelMatrix μ n).det)
    (hdnext : IsUnit (momentHankelMatrix μ (n + 1)).det)
    (hs : IsUnit (momentHankelMatrix (fun k => μ (k + 1)) n).det)
    (hnorm : momentNormSq μ n ≠ 0) :
    X * monicMomentPolynomial (fun k => μ (k + 1)) n =
      monicMomentPolynomial μ (n + 1) +
        C (momentNormSq (fun k => μ (k + 1)) n / momentNormSq μ n) *
          monicMomentPolynomial μ n := by
  have heq :
      X * monicMomentPolynomial (fun k => μ (k + 1)) n -
        C (momentNormSq (fun k => μ (k + 1)) n / momentNormSq μ n) *
          monicMomentPolynomial μ n = monicMomentPolynomial μ (n + 1) := by
    apply eq_monicMomentPolynomial μ hdnext
    · apply IsMonicOfDegree.sub
      · simpa only [Nat.one_add] using (isMonicOfDegree_X K).mul
          (isMonicOfDegree_monicMomentPolynomial (fun k => μ (k + 1)) n)
      · calc
          _ ≤ (monicMomentPolynomial μ n).natDegree := natDegree_C_mul_le _ _
          _ = n := (isMonicOfDegree_monicMomentPolynomial μ n).natDegree_eq
          _ < n + 1 := by lia
    · intro i
      rw [momentPairing_sub_right, momentPairing_C_mul_right, ← momentPairing_shift]
      by_cases hi : i.val < n
      · rw [momentPairing_X_pow_monicMomentPolynomial _ n hs ⟨i.val, hi⟩,
          momentPairing_X_pow_monicMomentPolynomial μ n hd ⟨i.val, hi⟩]
        simp
      · have hi' : i.val = n := by lia
        rw [hi', momentPairing_X_pow_monicMomentPolynomial_eq_norm _ n hs,
          momentPairing_X_pow_monicMomentPolynomial_eq_norm μ n hd,
          div_mul_cancel₀ _ hnorm, sub_self]
  exact sub_eq_iff_eq_add.mp heq

/-- The second finite Christoffel identity permits a vanishing next unshifted
norm. Thus the last odd Stieltjes numerator may be zero. -/
theorem monicMomentPolynomial_eq_shift_add_of_isUnit
    (μ : ℕ → K) (n : ℕ)
    (hdnext : IsUnit (momentHankelMatrix μ (n + 1)).det)
    (hs : IsUnit (momentHankelMatrix (fun k => μ (k + 1)) n).det)
    (hsnext : IsUnit (momentHankelMatrix (fun k => μ (k + 1)) (n + 1)).det)
    (hnorm : momentNormSq (fun k => μ (k + 1)) n ≠ 0) :
    monicMomentPolynomial μ (n + 1) =
      monicMomentPolynomial (fun k => μ (k + 1)) (n + 1) +
        C (momentNormSq μ (n + 1) / momentNormSq (fun k => μ (k + 1)) n) *
          monicMomentPolynomial (fun k => μ (k + 1)) n := by
  have heq : monicMomentPolynomial μ (n + 1) -
      C (momentNormSq μ (n + 1) / momentNormSq (fun k => μ (k + 1)) n) *
        monicMomentPolynomial (fun k => μ (k + 1)) n =
      monicMomentPolynomial (fun k => μ (k + 1)) (n + 1) := by
    apply eq_monicMomentPolynomial _ hsnext
    · apply (isMonicOfDegree_monicMomentPolynomial μ (n + 1)).sub
      calc
        _ ≤ (monicMomentPolynomial (fun k => μ (k + 1)) n).natDegree :=
          natDegree_C_mul_le _ _
        _ = n := (isMonicOfDegree_monicMomentPolynomial _ n).natDegree_eq
        _ < n + 1 := by lia
    · intro i
      rw [momentPairing_sub_right, momentPairing_C_mul_right, momentPairing_shift_X_pow]
      by_cases hi : i.val < n
      · rw [momentPairing_X_pow_monicMomentPolynomial μ (n + 1) hdnext
          ⟨i.val + 1, by lia⟩, momentPairing_X_pow_monicMomentPolynomial _ n hs ⟨i.val, hi⟩]
        simp
      · have hi' : i.val = n := by lia
        rw [hi', momentPairing_X_pow_monicMomentPolynomial_eq_norm μ (n + 1) hdnext,
          momentPairing_X_pow_monicMomentPolynomial_eq_norm _ n hs,
          div_mul_cancel₀ _ hnorm, sub_self]
  exact sub_eq_iff_eq_add.mp heq

end Polynomial
