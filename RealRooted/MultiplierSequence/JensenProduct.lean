module

public import RealRooted.MultiplierSequence
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Jensen polynomials of products

The binomial convolution of two exponential Taylor sequences is the Taylor
sequence of their product. This defines the Jensen family used in the general
auxiliary-function criterion, without assuming either sequence is nonzero.
-/

@[expose] public section

open Polynomial Complex

namespace RealRooted

/-- Binomial convolution, the coefficient rule for exponential generating functions. -/
noncomputable def binomialConvolution (gamma delta : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * gamma k * delta (n - k)

/-- Jensen polynomials associated with the product of exponential generating functions. -/
noncomputable def jensenProductPolynomial (d : ℕ) (gamma delta : ℕ → ℝ) : ℝ[X] :=
  jensenPolynomial d (binomialConvolution gamma delta)

/-- The constant binomial-convolution coefficient is the product of constants. -/
@[simp] theorem binomialConvolution_zero (gamma delta : ℕ → ℝ) :
    binomialConvolution gamma delta 0 = gamma 0 * delta 0 := by
  simp [binomialConvolution]

/-- Jensen product coefficients in binomial normalization. -/
@[simp] theorem coeff_jensenProductPolynomial (d : ℕ) (gamma delta : ℕ → ℝ) (k : ℕ) :
    (jensenProductPolynomial d gamma delta).coeff k =
      if k ≤ d then (d.choose k : ℝ) * binomialConvolution gamma delta k else 0 :=
  coeff_jensenPolynomial d _ k

/-- A Jensen product polynomial has degree at most its index. -/
theorem natDegree_jensenProductPolynomial_le (d : ℕ) (gamma delta : ℕ → ℝ) :
    (jensenProductPolynomial d gamma delta).natDegree ≤ d :=
  natDegree_jensenPolynomial_le d _

/-- Leibniz's rule identifies binomial convolution with the Taylor data of a product. -/
theorem iteratedDeriv_mul_eq_binomialConvolution {f g : ℂ → ℂ}
    {gamma delta : ℕ → ℝ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hgamma : ∀ k, iteratedDeriv k f 0 = (gamma k : ℂ))
    (hdelta : ∀ k, iteratedDeriv k g 0 = (delta k : ℂ)) (n : ℕ) :
    iteratedDeriv n (f * g) 0 = (binomialConvolution gamma delta n : ℂ) := by
  rw [iteratedDeriv_mul (hf.contDiff.contDiffAt) (hg.contDiff.contDiffAt)]
  simp [binomialConvolution, hgamma, hdelta]

end RealRooted
