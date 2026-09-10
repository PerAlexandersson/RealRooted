import RealRooted.BorceaBranden.Applications.HarmonicSubstitution.BFJOutput.Product
import RealRooted.Mathlib.Algebra.Polynomial.Eval.ShiftedChoose
import RealRooted.PolynomialValueEulerNumerator.PF

/-!
# Products of polynomial-value Euler numerators

This file identifies the BFJ product construction with the canonical Euler
numerator of a pointwise product of polynomial-value sequences.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- The BFJ output of the canonical Euler numerators is the canonical Euler
numerator of the polynomial product. -/
theorem bfjOutput_homogenize_polynomialValueEulerNumerator_eq
    (f g : ℝ[X]) :
    MvPolynomial.bfjOutput
        ((polynomialValueEulerNumerator f).homogenize f.natDegree)
        ((polynomialValueEulerNumerator g).homogenize g.natDegree)
        g.natDegree =
      polynomialValueEulerNumerator (f * g) := by
  by_cases hf : f = 0
  · subst f
    simp [MvPolynomial.bfjOutput, MvPolynomial.bfjCoefficient,
      MvPolynomial.bfjAuxiliary, MvPolynomial.addAuxiliary]
  by_cases hg : g = 0
  · subst g
    simp [MvPolynomial.bfjOutput, MvPolynomial.bfjCoefficient,
      MvPolynomial.bfjAuxiliary, MvPolynomial.harmonicClear]
  have hdeg : (f * g).natDegree = f.natDegree + g.natDegree :=
    Polynomial.natDegree_mul hf hg
  apply Polynomial.eq_of_sum_coeff_mul_shifted_choose_eq
      (d := (f * g).natDegree)
  · rw [hdeg]
    exact MvPolynomial.natDegree_bfjOutput_le
      (Polynomial.isHomogeneous_homogenize _)
      (Polynomial.isHomogeneous_homogenize _)
  · exact natDegree_polynomialValueEulerNumerator_le (f * g)
  · intro t _
    rw [hdeg]
    calc
      _ = (∑ k ∈ Finset.range (f.natDegree + 1),
            (polynomialValueEulerNumerator f).coeff k *
              (Nat.choose (t + f.natDegree - k) f.natDegree : ℝ)) *
          ∑ l ∈ Finset.range (g.natDegree + 1),
            (polynomialValueEulerNumerator g).coeff l *
              (Nat.choose (t + g.natDegree - l) g.natDegree : ℝ) := by
        simpa only [Nat.add_assoc] using
          (MvPolynomial.sum_coeff_mul_shifted_choose_bfjOutput_homogenize
            (p := polynomialValueEulerNumerator f)
            (q := polynomialValueEulerNumerator g)
            (a := f.natDegree) (b := g.natDegree)
            (natDegree_polynomialValueEulerNumerator_le f)
            (natDegree_polynomialValueEulerNumerator_le g) t)
      _ = f.eval (t : ℝ) * g.eval (t : ℝ) := by
        rw [eval_nat_eq_sum_eulerNumerator_coeff_mul_choose,
          eval_nat_eq_sum_eulerNumerator_coeff_mul_choose]
      _ = (f * g).eval (t : ℝ) := (Polynomial.eval_mul ..).symm
      _ = _ := by
        rw [eval_nat_eq_sum_eulerNumerator_coeff_mul_choose, hdeg]

end

end RealRooted
