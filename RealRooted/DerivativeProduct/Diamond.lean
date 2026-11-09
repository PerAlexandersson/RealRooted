module

public import RealRooted.DerivativeProduct.Transform
public import RealRooted.Transforms.BrandenE.Inverse

/-!
# The diamond product and Brändén's `E` transform

Brändén's `E` transform (`RealRooted.brandenE`) is the generalized geometric transform
`betaTransform 1`, and therefore the diamond product `f ⋄ g = betaProduct 1 f g` satisfies
`f ⋄ g = E (E⁻¹ f * E⁻¹ g)`.  See P. Brändén, *On linear transformations preserving the Pólya
frequency property*, Section 4 (the `E`-transform product identity).
-/

public section

open Polynomial

namespace RealRooted

/-- At `β = 1` the generalized geometric polynomials are the ordered Bell polynomials. -/
theorem generalizedGeometricPolynomial_one (n : ℕ) :
    generalizedGeometricPolynomial 1 n = orderedBellPolynomial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [generalizedGeometricPolynomial_succ, orderedBellPolynomial_succ, ih, map_one, one_mul]

/-- Brändén's `E` transform is the generalized geometric transform at `β = 1`. -/
theorem betaTransform_one_eq_brandenE (p : ℝ[X]) : betaTransform 1 p = brandenE p := by
  have h : generalizedGeometricPolynomial 1 = orderedBellPolynomial :=
    funext generalizedGeometricPolynomial_one
  rw [betaTransform, brandenE, h]

/-- `E` turns ordinary multiplication into the diamond product. -/
theorem betaProduct_one_brandenE (u v : ℝ[X]) :
    betaProduct 1 (brandenE u) (brandenE v) = brandenE (u * v) := by
  rw [← betaTransform_one_eq_brandenE, ← betaTransform_one_eq_brandenE,
    ← betaTransform_one_eq_brandenE, betaTransform_mul one_pos]

/-- The diamond product is `f ⋄ g = E (E⁻¹ f * E⁻¹ g)`, where `E⁻¹` is `brandenEPreimage`. -/
theorem betaProduct_one_eq_brandenE (f g : ℝ[X]) :
    betaProduct 1 f g = brandenE (brandenEPreimage f * brandenEPreimage g) := by
  rw [← betaProduct_one_brandenE, brandenE_preimage, brandenE_preimage]

end RealRooted
