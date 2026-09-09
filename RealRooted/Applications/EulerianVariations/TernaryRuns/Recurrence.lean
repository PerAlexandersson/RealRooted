import RealRooted.Basic.Coefficients
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Ternary increasing-run recurrence

This file defines the polynomial family in the normalized differential-
recurrence form used for the ternary-word application in arXiv:2609.07325.
Its algebraic degree, leading-coefficient, coefficient-positivity, and support
properties do not depend on the combinatorial interpretation.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.EulerianVariations

/-- The polynomial family determined by the ternary increasing-run
differential recurrence. -/
def ternaryRunPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C (3 / ((n : ℝ) + 1)) * X + C (-3 / ((n : ℝ) + 1)) * X ^ 2) *
          (ternaryRunPolynomial n).derivative +
        (C (-(n : ℝ) / ((n : ℝ) + 1)) +
          C ((4 * (n : ℝ) + 3) / ((n : ℝ) + 1)) * X) *
            ternaryRunPolynomial n

/-- The normalized differential recurrence for the ternary-run family. -/
lemma ternaryRunPolynomial_succ (n : ℕ) :
    ternaryRunPolynomial (n + 1) =
      (C (3 / ((n : ℝ) + 1)) * X + C (-3 / ((n : ℝ) + 1)) * X ^ 2) *
          (ternaryRunPolynomial n).derivative +
        (C (-(n : ℝ) / ((n : ℝ) + 1)) +
          C ((4 * (n : ℝ) + 3) / ((n : ℝ) + 1)) * X) *
            ternaryRunPolynomial n :=
  rfl

@[simp] theorem ternaryRunPolynomial_zero :
    ternaryRunPolynomial 0 = 1 :=
  rfl

theorem ternaryRunPolynomial_one :
    ternaryRunPolynomial 1 = C 3 * X := by
  norm_num [ternaryRunPolynomial]

private theorem ternaryRunPolynomial_degree_and_leadingCoeff (n : ℕ) :
    (ternaryRunPolynomial n).natDegree = n ∧
      (ternaryRunPolynomial n).leadingCoeff =
        (Finset.range n).prod (fun k : ℕ =>
          (-3 / ((k : ℝ) + 1)) * (k : ℝ) +
            (4 * (k : ℝ) + 3) / ((k : ℝ) + 1)) := by
  have hrec : ∀ k, ternaryRunPolynomial (k + 1) =
      (C (3 / ((k : ℝ) + 1)) * X + C (-3 / ((k : ℝ) + 1)) * X ^ 2) *
          (ternaryRunPolynomial k).derivative +
        (C (-(k : ℝ) / ((k : ℝ) + 1)) +
          C ((4 * (k : ℝ) + 3) / ((k : ℝ) + 1)) * X) *
            ternaryRunPolynomial k + 0 := by
    intro k
    rw [ternaryRunPolynomial_succ]
    ring
  have hseed : ternaryRunPolynomial 0 ≠ 0 := by
    simp [ternaryRunPolynomial]
  have hrem : ∀ k, (0 : ℝ[X]).natDegree ≤
      (ternaryRunPolynomial 0).natDegree + k := by
    intro k
    simp
  have hfactor : ∀ k : ℕ,
      (-3 / ((k : ℝ) + 1)) * (k : ℝ) +
        (4 * (k : ℝ) + 3) / ((k : ℝ) + 1) ≠ 0 := by
    intro k
    apply ne_of_gt
    rw [show (-3 / ((k : ℝ) + 1)) * (k : ℝ) +
        (4 * (k : ℝ) + 3) / ((k : ℝ) + 1) =
          ((k : ℝ) + 3) / ((k : ℝ) + 1) by
            field_simp
            ring]
    positivity
  have hresult :=
    Polynomial.natDegree_and_leadingCoeff_quadratic_derivative_recurrence_of_ne_zero
      ternaryRunPolynomial (fun _ => 0)
        (fun k => 3 / ((k : ℝ) + 1))
        (fun k => -3 / ((k : ℝ) + 1))
        (fun k => -(k : ℝ) / ((k : ℝ) + 1))
        (fun k => (4 * (k : ℝ) + 3) / ((k : ℝ) + 1))
        hrec hseed hrem (by
          intro k
          simpa [ternaryRunPolynomial] using hfactor k) n
  simpa [ternaryRunPolynomial] using hresult

/-- The ternary-run recurrence polynomial at rank `n` has degree `n`. -/
theorem natDegree_ternaryRunPolynomial (n : ℕ) :
    (ternaryRunPolynomial n).natDegree = n :=
  (ternaryRunPolynomial_degree_and_leadingCoeff n).1

/-- The ternary-run recurrence polynomial has positive leading coefficient. -/
theorem ternaryRunPolynomial_pos_leadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (ternaryRunPolynomial n) := by
  rw [HasPosLeadingCoeff, (ternaryRunPolynomial_degree_and_leadingCoeff n).2]
  apply Finset.prod_pos
  intro k _
  rw [show (-3 / ((k : ℝ) + 1)) * (k : ℝ) +
      (4 * (k : ℝ) + 3) / ((k : ℝ) + 1) =
        ((k : ℝ) + 3) / ((k : ℝ) + 1) by
          field_simp
          ring]
  positivity

private lemma coeff_zero_ternaryRunPolynomial_succ (n : ℕ) :
    (ternaryRunPolynomial (n + 1)).coeff 0 =
      (-(n : ℝ) / ((n : ℝ) + 1)) * (ternaryRunPolynomial n).coeff 0 := by
  rw [ternaryRunPolynomial_succ]
  simp

private lemma coeff_succ_ternaryRunPolynomial_succ (n k : ℕ) :
    (ternaryRunPolynomial (n + 1)).coeff (k + 1) =
      ((3 * ((k : ℝ) + 1) - (n : ℝ)) / ((n : ℝ) + 1)) *
          (ternaryRunPolynomial n).coeff (k + 1) +
        ((4 * (n : ℝ) + 3 - 3 * (k : ℝ)) / ((n : ℝ) + 1)) *
          (ternaryRunPolynomial n).coeff k := by
  rw [ternaryRunPolynomial_succ,
    Polynomial.coeff_quadratic_derivative_add_linear_mul_succ]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem ternaryRunPolynomial_two :
    ternaryRunPolynomial 2 = C 3 * X + C 6 * X ^ 2 := by
  ext k
  cases k with
  | zero =>
      rw [coeff_zero_ternaryRunPolynomial_succ]
      norm_num [ternaryRunPolynomial_one]
  | succ k =>
      rw [coeff_succ_ternaryRunPolynomial_succ, ternaryRunPolynomial_one]
      by_cases hk0 : k = 0
      · subst k
        norm_num [Polynomial.coeff_X]
      by_cases hk1 : k = 1
      · subst k
        norm_num [Polynomial.coeff_X]
      have hk1' : 1 ≠ k := Ne.symm hk1
      simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow, hk0, hk1, hk1']

theorem ternaryRunPolynomial_three :
    ternaryRunPolynomial 3 = C 1 * X + C 16 * X ^ 2 + C 10 * X ^ 3 := by
  ext k
  cases k with
  | zero =>
      rw [coeff_zero_ternaryRunPolynomial_succ]
      norm_num [ternaryRunPolynomial_two]
  | succ k =>
      rw [coeff_succ_ternaryRunPolynomial_succ, ternaryRunPolynomial_two]
      by_cases hk0 : k = 0
      · subst k
        norm_num [Polynomial.coeff_X]
      by_cases hk1 : k = 1
      · subst k
        norm_num [Polynomial.coeff_X]
      by_cases hk2 : k = 2
      · subst k
        norm_num [Polynomial.coeff_X]
      have hk1' : 1 ≠ k := Ne.symm hk1
      simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_X_pow, hk0, hk1, hk1', hk2]

/-- Coefficients are nonnegative, and coefficients strictly below one third
of the rank vanish. -/
theorem ternaryRunPolynomial_coeff_nonneg_and_support (n k : ℕ) :
    0 ≤ (ternaryRunPolynomial n).coeff k ∧
      (3 * k < n → (ternaryRunPolynomial n).coeff k = 0) := by
  induction n generalizing k with
  | zero =>
      constructor
      · cases k with
        | zero => simp [ternaryRunPolynomial]
        | succ k =>
            change 0 ≤ (1 : ℝ[X]).coeff (k + 1)
            rw [Polynomial.coeff_one]
            simp
      · intro h
        lia
  | succ n ih =>
      cases k with
      | zero =>
          have hzero : (ternaryRunPolynomial (n + 1)).coeff 0 = 0 := by
            rw [coeff_zero_ternaryRunPolynomial_succ]
            by_cases hn : n = 0
            · simp [hn]
            · rw [(ih 0).2 (by lia)]
              ring
          exact ⟨by rw [hzero], fun _ => hzero⟩
      | succ k =>
          rw [coeff_succ_ternaryRunPolynomial_succ]
          have hcurr := ih (k + 1)
          have hprev := ih k
          constructor
          · apply add_nonneg
            · by_cases hbelow : 3 * (k + 1) < n
              · rw [hcurr.2 hbelow]
                simp
              · apply mul_nonneg
                · apply div_nonneg
                  · apply sub_nonneg.mpr
                    have hnat : n ≤ 3 * (k + 1) := by lia
                    exact_mod_cast hnat
                  · positivity
                · exact hcurr.1
            · by_cases habove : n < k
              · have hzero : (ternaryRunPolynomial n).coeff k = 0 := by
                  apply Polynomial.coeff_eq_zero_of_natDegree_lt
                  rw [natDegree_ternaryRunPolynomial]
                  exact habove
                rw [hzero]
                simp
              · apply mul_nonneg
                · apply div_nonneg
                  · apply sub_nonneg.mpr
                    have hnat : 3 * k ≤ 4 * n + 3 := by lia
                    exact_mod_cast hnat
                  · positivity
                · exact hprev.1
          · intro hbelow
            have hprevZero : (ternaryRunPolynomial n).coeff k = 0 :=
              hprev.2 (by lia)
            have hcurrTerm :
                ((3 * ((k : ℝ) + 1) - (n : ℝ)) / ((n : ℝ) + 1)) *
                  (ternaryRunPolynomial n).coeff (k + 1) = 0 := by
              by_cases hstrict : 3 * (k + 1) < n
              · rw [hcurr.2 hstrict]
                simp
              · have heq : 3 * (k + 1) = n := by lia
                have heqReal : 3 * ((k : ℝ) + 1) - (n : ℝ) = 0 := by
                  have hcast : 3 * ((k : ℝ) + 1) = (n : ℝ) := by
                    exact_mod_cast heq
                  linarith
                rw [heqReal]
                simp
            rw [hcurrTerm, hprevZero]
            ring

/-- Every ternary-run recurrence polynomial has nonnegative coefficients. -/
theorem ternaryRunPolynomial_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (ternaryRunPolynomial n) :=
  fun k => (ternaryRunPolynomial_coeff_nonneg_and_support n k).1

end RealRooted.Applications.EulerianVariations
