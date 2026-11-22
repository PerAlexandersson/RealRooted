module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RealRooted.Mathlib.Analysis.Convex.LogDerivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.LaguerreInequalities.DerivativeFormula

/-!
# Logarithmic concavity between real zeros

A Laguerre--Pólya function has concave logarithmic absolute value on every
convex set of real points where it does not vanish. This gives bounds for its
logarithmic derivative from real secant slopes.
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

/-- A Laguerre--Pólya function has concave logarithmic absolute value on any
convex zero-free part of the real line. The real logarithm handles either sign. -/
theorem IsLaguerrePolya.concaveOn_log_re {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    {S : Set ℝ} (hS : Convex ℝ S) (hne : ∀ x ∈ S, f x ≠ 0) :
    ConcaveOn ℝ S (fun x : ℝ => Real.log (f x).re) := by
  have hreal (x : ℝ) : ((f x).re : ℂ) = f x := by
    apply conj_eq_iff_re.mp
    simpa using (hf.conj x).symm
  apply concaveOn_log_of_deriv_sq_sub_nonneg hS
    (f' := fun x : ℝ => (_root_.deriv f x).re)
    (f'' := fun x : ℝ => (_root_.deriv (_root_.deriv f) x).re)
  · intro x _
    exact (hf.differentiable x).hasDerivAt.real_of_complex
  · intro x _
    exact (hf.differentiable.deriv x).hasDerivAt.real_of_complex
  · intro x hx hzero
    exact hne x hx (by rw [← hreal x, hzero, ofReal_zero])
  · intro x _
    have hL := hf.laguerreCoefficient_nonneg x 1
    rw [laguerreCoefficient_one hf.differentiable hf.conj] at hL
    simpa [iteratedDeriv_succ] using hL

end RealRooted
