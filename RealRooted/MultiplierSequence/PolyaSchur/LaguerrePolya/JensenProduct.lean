module

public import RealRooted.MultiplierSequence.JensenProduct
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen

/-!
# An auxiliary-product form of Jensen's criterion

The Jensen polynomials of binomially convolved Taylor data detect membership
of the product in the Laguerre--Pólya class. This identity is the core of
O'Sullivan's Theorem 3.5, https://arxiv.org/abs/2007.13582.
-/

public section

open Complex

namespace RealRooted

/-- All Jensen product polynomials split exactly when the entire product is
Laguerre--Pólya. No nonvanishing assumption is needed for this product statement. -/
theorem isLaguerrePolya_mul_iff_jensenProductPolynomial_splits {f g : ℂ → ℂ}
    {gamma delta : ℕ → ℝ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hgamma : ∀ k, iteratedDeriv k f 0 = (gamma k : ℂ))
    (hdelta : ∀ k, iteratedDeriv k g 0 = (delta k : ℂ)) :
    IsLaguerrePolya (f * g) ↔ ∀ d, (jensenProductPolynomial d gamma delta).Splits :=
  isLaguerrePolya_iff_jensenPolynomial_splits (hf.mul hg)
    (iteratedDeriv_mul_eq_binomialConvolution hf hg hgamma hdelta)

end RealRooted
