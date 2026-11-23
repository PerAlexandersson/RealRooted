module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.LaguerreInequalities.DerivativeFormula
import RealRooted.BrandenLC.Sequence
import Mathlib.Tactic.Linarith

/-!
# The quartic auxiliary inequality

The inequality in Cardon, *Extended Laguerre inequalities and a criterion
for real zeros*, Example 1, follows from the degree-independent Newton bound
for the generalized Laguerre coefficients. The expression is
`6 * (L_1^2 - 2 * L_0 * L_2)`, so the proof includes real centers where `f` vanishes.
-/

public section

namespace RealRooted

/-- The quartic derivative inequality associated to the auxiliary `X^4 + 4`
holds for every Laguerre--Pólya function and every real center. -/
theorem IsLaguerrePolya.quartic_derivative_nonneg {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (x : ℝ) :
    0 ≤ -(f x).re ^ 3 * (iteratedDeriv 4 f x).re +
      3 * (f x).re ^ 2 * (iteratedDeriv 2 f x).re ^ 2 +
      6 * (iteratedDeriv 1 f x).re ^ 4 +
      4 * (f x).re ^ 2 * (iteratedDeriv 3 f x).re * (iteratedDeriv 1 f x).re -
      12 * (f x).re * (iteratedDeriv 1 f x).re ^ 2 * (iteratedDeriv 2 f x).re := by
  obtain ⟨p, hp, hlim⟩ := hf.exists_pf_laguerreCoefficient_approx x
  have h := logConcavitySequence_lower_bound_of_limit hp hlim 1
  norm_num [logConcavitySequence] at h
  rw [laguerreCoefficient_zero hf.differentiable hf.conj,
    laguerreCoefficient_one hf.differentiable hf.conj,
    laguerreCoefficient_two hf.differentiable hf.conj] at h
  nlinarith

end RealRooted
