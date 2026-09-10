import RealRooted.PFPolynomial
import RealRooted.PolynomialValueEulerNumerator
import RealRooted.PolyaFrequencyConvolution.Basic
import RealRooted.PolyaFrequencyConvolution.InverseOneSubPow

/-!
# Pólya-frequency consequence of an Euler-numerator certificate

This file turns a PF certificate for the canonical Euler numerator of a
polynomial-value sequence into a PF certificate for the sequence itself.
-/

open Polynomial

namespace RealRooted

/-- Polynomial values are the Cauchy convolution of the coefficients of their
canonical Euler numerator with the appropriate inverse-power kernel. -/
theorem polynomialValueSeq_eq_eulerNumeratorCoeff_convolution (p : ℝ[X]) :
    polynomialValueSeq p =
      natCauchyConvolution (fun n => (polynomialValueEulerNumerator p).coeff n)
        (invOneSubPowCoeff p.natDegree) := by
  funext n
  have h := congrArg (PowerSeries.coeff n)
    (polynomialValueSeries_eq_eulerNumerator_mul_invOneSubPow p)
  rw [PowerSeries.coeff_mk, coeff_mul_eq_natCauchyConvolution] at h
  simpa only [Polynomial.coeff_coe, coeff_invOneSubPow_val_succ] using h

/-- Evaluation of a polynomial in the nonnegative integers in the binomial
basis determined by the coefficients of its canonical Euler numerator. -/
theorem eval_nat_eq_sum_eulerNumerator_coeff_mul_choose (p : ℝ[X]) (t : ℕ) :
    p.eval (t : ℝ) =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        (polynomialValueEulerNumerator p).coeff i *
          (Nat.choose (t + p.natDegree - i) p.natDegree : ℝ) := by
  have hconv := congrFun
    (polynomialValueSeq_eq_eulerNumeratorCoeff_convolution p) t
  change p.eval (t : ℝ) = _ at hconv
  rw [hconv]
  unfold natCauchyConvolution invOneSubPowCoeff
  have hreindex :
      (∑ i ∈ Finset.range (t + 1),
        (polynomialValueEulerNumerator p).coeff i *
          (Nat.choose (p.natDegree + (t - i)) p.natDegree : ℝ)) =
        ∑ i ∈ Finset.range (t + 1),
          (polynomialValueEulerNumerator p).coeff i *
            (Nat.choose (t + p.natDegree - i) p.natDegree : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    have hit : i ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [Nat.add_comm t p.natDegree, Nat.add_sub_assoc hit]
  rw [hreindex]
  by_cases hdt : p.natDegree ≤ t
  · symm
    apply Finset.sum_subset
    · intro i hi
      rw [Finset.mem_range] at hi ⊢
      lia
    · intro i hi _hiSmall
      have hdi : p.natDegree < i := by
        rw [Finset.mem_range] at hi
        simp only [Finset.mem_range, not_lt] at _hiSmall
        lia
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (natDegree_polynomialValueEulerNumerator_le p |>.trans_lt hdi)]
      simp
  · have htd : t < p.natDegree := Nat.lt_of_not_ge hdt
    apply Finset.sum_subset
    · intro i hi
      rw [Finset.mem_range] at hi ⊢
      lia
    · intro i hi _hiSmall
      have hti : t < i := by
        rw [Finset.mem_range] at hi
        simp only [Finset.mem_range, not_lt] at _hiSmall
        lia
      rw [Nat.choose_eq_zero_of_lt (by
        have hid : i ≤ p.natDegree :=
          Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        lia)]
      simp

/-- A PF canonical Euler numerator certifies that the associated
polynomial-value sequence is PF. -/
theorem isPolyaFreqSeq_polynomialValueSeq_of_eulerNumerator
    {p : ℝ[X]} (h : IsPFPolynomial (polynomialValueEulerNumerator p)) :
    IsPolyaFreqSeq (polynomialValueSeq p) := by
  rw [polynomialValueSeq_eq_eulerNumeratorCoeff_convolution]
  exact h.to_sequence.natCauchyConvolution
    (invOneSubPowCoeff_isPolyaFreqSeq p.natDegree)

end RealRooted
