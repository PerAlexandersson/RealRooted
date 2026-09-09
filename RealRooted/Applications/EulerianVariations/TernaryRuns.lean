import RealRooted.Applications.EulerianVariations.TernaryRuns.Recurrence
import RealRooted.Linear
import RealRooted.MaWang.DerivativeStep
import RealRooted.PFPolynomial

/-!
# Ternary increasing runs

This file proves the real-rootedness result for the ternary increasing-run
polynomials in Theorem `thm:ternaryRuns`, under Section
`sec:furtherFamilies`, of
[arXiv:2609.07325](https://arxiv.org/abs/2609.07325).

The paper identifies the recurrence family with the enumerator of increasing
runs in ternary words. That counting identity is cited rather than formalized
here; the interlacing and real-rootedness consequences are proved from the
explicit recurrence.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.EulerianVariations

private lemma ternaryRunPolynomial_succ_eq_linear_add_derivative (n : ℕ) :
    ternaryRunPolynomial (n + 1) =
      (C (-(n : ℝ) / ((n : ℝ) + 1)) +
          C ((4 * (n : ℝ) + 3) / ((n : ℝ) + 1)) * X) *
          ternaryRunPolynomial n +
        (C (3 / ((n : ℝ) + 1)) * X * (1 - X)) *
          (ternaryRunPolynomial n).derivative := by
  rw [ternaryRunPolynomial_succ]
  rw [show -3 / ((n : ℝ) + 1) = -(3 / ((n : ℝ) + 1)) by ring]
  simp only [map_neg]
  ring

/-- Consecutive ternary-run polynomials are in weak proper position. -/
theorem ternaryRunPolynomial_prec (n : ℕ) :
    Prec (ternaryRunPolynomial n) (ternaryRunPolynomial (n + 1)) := by
  induction n with
  | zero =>
      have hdeg : (ternaryRunPolynomial 1).natDegree = 1 :=
        natDegree_ternaryRunPolynomial 1
      simpa [ternaryRunPolynomial] using (interlaces_one_linear hdeg).toPrec
  | succ n ih =>
      let m := n + 1
      change Prec (ternaryRunPolynomial m) (ternaryRunPolynomial (m + 1))
      have ih' : Prec (ternaryRunPolynomial n) (ternaryRunPolynomial m) := by
        simpa [m] using ih
      have hstep : Prec (ternaryRunPolynomial m)
          ((C (-(m : ℝ) / ((m : ℝ) + 1)) +
              C ((4 * (m : ℝ) + 3) / ((m : ℝ) + 1)) * X) *
              ternaryRunPolynomial m +
            (C (3 / ((m : ℝ) + 1)) * X * (1 - X)) *
              (ternaryRunPolynomial m).derivative) := by
        apply prec_mw_derivative_of_nonpos_of_pos_natDegree ih'.2.1.2
        · rw [natDegree_ternaryRunPolynomial]
          simp [m]
        · rw [← ternaryRunPolynomial_succ_eq_linear_add_derivative,
            natDegree_ternaryRunPolynomial, natDegree_ternaryRunPolynomial]
          lia
        · rw [← ternaryRunPolynomial_succ_eq_linear_add_derivative,
            natDegree_ternaryRunPolynomial, natDegree_ternaryRunPolynomial]
        · simpa [← ternaryRunPolynomial_succ_eq_linear_add_derivative] using
            ternaryRunPolynomial_pos_leadingCoeff (m + 1)
        · exact ternaryRunPolynomial_pos_leadingCoeff m
        · intro r hr
          have hrNonpos : r ≤ 0 := isRoot_nonpos_of_hasNonnegCoeffs
            (ternaryRunPolynomial_hasNonnegCoeffs m)
            (ternaryRunPolynomial_pos_leadingCoeff m).ne_zero hr
          have hden : 0 ≤ 3 / ((m : ℝ) + 1) := by positivity
          have hOne : 0 ≤ 1 - r := by linarith
          simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one]
          simpa [mul_assoc] using mul_nonpos_of_nonneg_of_nonpos hden
            (mul_nonpos_of_nonpos_of_nonneg hrNonpos hOne)
      rw [← ternaryRunPolynomial_succ_eq_linear_add_derivative m] at hstep
      exact hstep

/-- The ternary increasing-run recurrence polynomial is a Pólya-frequency
polynomial at every rank. -/
theorem ternaryRunPolynomial_isPF (n : ℕ) :
    IsPFPolynomial (ternaryRunPolynomial n) := by
  apply IsPFPolynomial.of_realRooted_nonneg
    (ternaryRunPolynomial_hasNonnegCoeffs n)
  cases n with
  | zero => simp [ternaryRunPolynomial]
  | succ n => exact (ternaryRunPolynomial_prec n).2.1.2

end RealRooted.Applications.EulerianVariations
