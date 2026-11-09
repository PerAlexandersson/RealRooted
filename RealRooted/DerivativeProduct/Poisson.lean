module

public import RealRooted.DerivativeProduct.Associative
public import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar

/-!
# Poisson products as derivative products

The univariate Poisson product `starC c f g = ∑ j, c ^ j / j! * X ^ j * f ^ (j) * g ^ (j)` is the
derivative product with weight `X` and coefficients `c ^ k / k!`.  It is the member of the
associative family `assocProduct` with parameter `c` and weight `X` (quadratic coefficient
`A = 0`).
-/

public section

open Polynomial

namespace RealRooted.Poisson

/-- The Poisson product is the derivative product with weight `X` and coefficients
`c ^ k / k!`. -/
theorem starC_eq_derivProduct (c : ℝ) (f g : ℝ[X]) :
    starC c f g = derivProduct X (fun k ↦ c ^ k / (k.factorial : ℝ)) f g :=
  rfl

/-- The Poisson product is the member `assocProduct c X` of the associative family. -/
theorem starC_eq_assocProduct (c : ℝ) (f g : ℝ[X]) : starC c f g = assocProduct c X f g := by
  have h : assocCoeff c ((X : ℝ[X]).coeff 2) = fun k ↦ c ^ k / (k.factorial : ℝ) := by
    funext k
    simp [assocCoeff, coeff_X]
  rw [starC_eq_derivProduct, assocProduct, h]

end RealRooted.Poisson
