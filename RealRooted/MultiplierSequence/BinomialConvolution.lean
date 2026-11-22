module

public import RealRooted.MultiplierSequence.JensenProduct
public import RealRooted.MultiplierSequence.Infinite
import RealRooted.MultiplierSequence.JensenConvolution
import RealRooted.MultiplierSequence.PolyaSchur

/-!
# Binomial convolution of positive multiplier sequences

The product rule for exponential generating functions preserves the positive
multiplier-sequence cone. The finite Jensen convolution theorem proves this
directly, including zero sequences and vanishing constant coefficients.
-/

public section

open Polynomial

namespace RealRooted

/-- Binomial convolution of nonnegative sequences is nonnegative. -/
theorem binomialConvolution_nonneg {gamma delta : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) (hdelta : ∀ k, 0 ≤ delta k) (n : ℕ) :
    0 ≤ binomialConvolution gamma delta n := by
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hgamma k)) (hdelta (n - k))

/-- Scaling both inputs scales their binomial convolution by the product. -/
theorem binomialConvolution_const_mul (gamma delta : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    binomialConvolution (fun k => a * gamma k) (fun k => b * delta k) n =
      a * b * binomialConvolution gamma delta n := by
  simp only [binomialConvolution, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Binomial convolution preserves PF multiplier sequences. -/
theorem IsPFMultiplierSequence.binomialConvolution {gamma delta : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (hdelta : IsPFMultiplierSequence delta) :
    IsPFMultiplierSequence (RealRooted.binomialConvolution gamma delta) := by
  rw [isPFMultiplierSequence_iff_jensenPolynomial_isPF]
  intro n
  apply IsPFPolynomial.of_realRooted_nonneg
  · intro k
    rw [coeff_jensenPolynomial]
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _)
        (binomialConvolution_nonneg hgamma.nonneg hdelta.nonneg k)
    · exact le_rfl
  · exact jensenProductPolynomial_splits n
      ((isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence hgamma n).splits)
      ((isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence hdelta n).splits)

end RealRooted
