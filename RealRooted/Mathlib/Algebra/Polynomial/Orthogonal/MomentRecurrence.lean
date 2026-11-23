/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentAlgebra

/-!
# Three-term recurrence from a positive moment functional

The monic polynomials obtained from the finite Hankel solve satisfy the
three-term recurrence. The subdiagonal coefficient is the quotient of
successive squared norms and is strictly positive. This is unconditional
infrastructure; a particular arithmetic moment sequence supplies the
positive-definiteness hypotheses separately.
-/

public section

namespace Polynomial

/-- The diagonal coefficient of the monic moment-polynomial recurrence. -/
@[expose] noncomputable def momentJacobiDiagonal (μ : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentPairing μ (X * monicMomentPolynomial μ n) (monicMomentPolynomial μ n) /
    momentNormSq μ n

/-- The outgoing Jacobi numerator is the ratio of consecutive squared norms. -/
@[expose] noncomputable def momentJacobiNumerator (μ : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentNormSq μ (n + 1) / momentNormSq μ n

/-- Strictly positive Hankel matrices give positive outgoing Jacobi numerators. -/
theorem momentJacobiNumerator_pos (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef) (n : ℕ) :
    0 < momentJacobiNumerator μ n :=
  div_pos (momentNormSq_pos μ (n + 1) (hpos (n + 2)))
    (momentNormSq_pos μ n (hpos (n + 1)))

/-- Positive Hankel forms have invertible determinants. -/
private theorem det_isUnit (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef) (n : ℕ) :
    IsUnit (momentHankelMatrix μ n).det :=
  isUnit_iff_ne_zero.mpr (hpos n).det_pos.ne'

/-- The first monic moment polynomial has the mean as its sole root. -/
theorem monicMomentPolynomial_one_eq (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef) :
    monicMomentPolynomial μ 1 = X - C (momentJacobiDiagonal μ 0) := by
  have hm : μ 0 ≠ 0 := by
    simpa only [momentNormSq_zero] using (momentNormSq_pos μ 0 (hpos 1)).ne'
  have hx : momentFunctional μ X = μ 1 := by
    simpa only [pow_one] using momentFunctional_X_pow μ 1
  have hc (c : ℝ) : momentFunctional μ (C c) = c * μ 0 := by
    simpa only [mul_one, momentFunctional_one] using momentFunctional_C_mul μ c 1
  have hd : momentJacobiDiagonal μ 0 = μ 1 / μ 0 := by
    simp only [momentJacobiDiagonal, monicMomentPolynomial_zero, momentNormSq_zero,
      momentPairing, mul_one, hx]
  symm
  apply eq_monicMomentPolynomial μ (det_isUnit μ hpos 1)
    (isMonicOfDegree_X_sub_one _)
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [Fin.val_zero, pow_zero, momentPairing, one_mul, momentFunctional_sub,
    hx, hc, hd, div_mul_cancel₀ _ hm, sub_self]

/-- Moving multiplication by X increases the monomial exponent. -/
private theorem pairing_X_pow_X_mul_eq (μ : ℕ → ℝ) (n i : ℕ) :
    momentPairing μ (X ^ i) (X * monicMomentPolynomial μ n) =
      momentPairing μ (X ^ (i + 1)) (monicMomentPolynomial μ n) := by
  rw [← momentPairing_X_mul_left, ← pow_succ']

/-- The recurrence candidate is orthogonal to all lower monomials. -/
private theorem recurrence_lower_orthogonal (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef) (n : ℕ) (i : Fin (n + 1)) :
    momentPairing μ (X ^ i.val)
      ((X - C (momentJacobiDiagonal μ (n + 1))) * monicMomentPolynomial μ (n + 1) -
        C (momentJacobiNumerator μ n) * monicMomentPolynomial μ n) = 0 := by
  have horth : momentPairing μ (X ^ i.val) (monicMomentPolynomial μ (n + 1)) = 0 :=
    momentPairing_X_pow_monicMomentPolynomial μ (n + 1) (det_isUnit μ hpos _) i
  rw [sub_mul, momentPairing_sub_right, momentPairing_sub_right,
    momentPairing_C_mul_right, momentPairing_C_mul_right, horth, mul_zero, sub_zero,
    pairing_X_pow_X_mul_eq]
  by_cases hi : i.val < n
  · rw [momentPairing_X_pow_monicMomentPolynomial μ (n + 1)
      (det_isUnit μ hpos _) ⟨i.val + 1, by lia⟩,
      momentPairing_X_pow_monicMomentPolynomial μ n (det_isUnit μ hpos _) ⟨i.val, hi⟩]
    simp
  · have hi' : i.val = n := by lia
    rw [hi', momentPairing_X_pow_monicMomentPolynomial_eq_norm μ (n + 1)
      (det_isUnit μ hpos _), momentPairing_X_pow_monicMomentPolynomial_eq_norm μ n
      (det_isUnit μ hpos _), momentJacobiNumerator,
      div_mul_cancel₀ _ (momentNormSq_pos μ n (hpos (n + 1))).ne', sub_self]

/-- The diagonal recurrence coefficient removes the self pairing. -/
private theorem recurrence_self_orthogonal (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef) (n : ℕ) :
    momentPairing μ (monicMomentPolynomial μ (n + 1))
      ((X - C (momentJacobiDiagonal μ (n + 1))) * monicMomentPolynomial μ (n + 1) -
        C (momentJacobiNumerator μ n) * monicMomentPolynomial μ n) = 0 := by
  have hdegree : (monicMomentPolynomial μ n).degree < (n + 1 : WithBot ℕ) :=
    lt_of_le_of_lt degree_le_natDegree (by
      rw [(isMonicOfDegree_monicMomentPolynomial μ n).natDegree_eq]
      exact_mod_cast Nat.lt_succ_self n)
  have horth := momentPairing_monicMomentPolynomial μ (n + 1)
    (det_isUnit μ hpos _) hdegree
  rw [momentPairing_comm] at horth
  rw [sub_mul, momentPairing_sub_right, momentPairing_sub_right,
    momentPairing_C_mul_right, momentPairing_C_mul_right, horth, mul_zero, sub_zero,
    momentPairing_comm μ (monicMomentPolynomial μ (n + 1))
      (X * monicMomentPolynomial μ (n + 1))]
  change _ - momentJacobiDiagonal μ (n + 1) * momentNormSq μ (n + 1) = 0
  rw [momentJacobiDiagonal,
    div_mul_cancel₀ _ (momentNormSq_pos μ (n + 1) (hpos (n + 2))).ne', sub_self]

/-- Positive Hankel forms force the monic three-term recurrence, with coefficients
defined by the moment pairing and successive squared norms. -/
theorem monicMomentPolynomial_add_two (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef) (n : ℕ) :
    monicMomentPolynomial μ (n + 2) =
      (X - C (momentJacobiDiagonal μ (n + 1))) * monicMomentPolynomial μ (n + 1) -
        C (momentJacobiNumerator μ n) * monicMomentPolynomial μ n := by
  let q := (X - C (momentJacobiDiagonal μ (n + 1))) * monicMomentPolynomial μ (n + 1) -
    C (momentJacobiNumerator μ n) * monicMomentPolynomial μ n
  have hmonic : IsMonicOfDegree q (n + 2) := by
    apply IsMonicOfDegree.sub
    · simpa only [Nat.one_add] using
        (isMonicOfDegree_X_sub_one (momentJacobiDiagonal μ (n + 1))).mul
          (isMonicOfDegree_monicMomentPolynomial μ (n + 1))
    · calc
        _ ≤ (monicMomentPolynomial μ n).natDegree := natDegree_C_mul_le _ _
        _ = n := (isMonicOfDegree_monicMomentPolynomial μ n).natDegree_eq
        _ < n + 2 := by lia
  have hlow (i : Fin (n + 1)) : momentPairing μ (X ^ i.val) q = 0 :=
    recurrence_lower_orthogonal μ hpos n i
  have htop : momentPairing μ (X ^ (n + 1)) q = 0 := by
    have hsmall := (isMonicOfDegree_monicMomentPolynomial μ
      (n + 1)).natDegree_sub_X_pow (by lia : n + 1 ≠ 0)
    have hdegree : (monicMomentPolynomial μ (n + 1) - X ^ (n + 1)).degree <
        (n + 1 : WithBot ℕ) :=
      lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hsmall)
    have h := momentPairing_eq_zero_of_X_pow μ hdegree hlow
    rw [momentPairing_sub_left, recurrence_self_orthogonal μ hpos n] at h
    exact neg_eq_zero.mp (by simpa only [zero_sub] using h)
  symm
  apply eq_monicMomentPolynomial μ (det_isUnit μ hpos _) hmonic
  intro i
  by_cases hi : i.val < n + 1
  · exact hlow ⟨i.val, hi⟩
  · have hi' : i.val = n + 1 := by lia
    simpa only [hi'] using htop

end Polynomial
