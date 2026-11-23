module

public import RealRooted.LaguerreInequalities.Analytic
public import TauCeti.Analysis.Complex.Pick.Nevanlinna
import RealRooted.LaguerreInequalities.LogDerivative

/-!
# Nevanlinna representation from generalized Laguerre inequalities

Every real entire function satisfying all generalized Laguerre inequalities has
a negative logarithmic derivative with a finite Nevanlinna representing measure.
This is an intermediate step toward the unrestricted converse in
Csordas--Vishnyakova (2013), Theorem 2.3. No order, genus, strict Pick inequality,
or nonvanishing value at the origin is assumed.
-/

public section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace RealRooted

/-- All generalized Laguerre inequalities give a finite Nevanlinna representation
of the negative logarithmic derivative. The closed Pick inequality allows zero
measure and zero linear coefficient, including constant and exponential cases. -/
theorem exists_nevanlinna_neg_logDeriv_of_laguerreCoefficient_nonneg {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z))
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    ∃ (ρ : Measure ℝ) (b : ℝ), IsFiniteMeasure ρ ∧ 0 ≤ b ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        -logDeriv f z = (b : ℂ) * z + ∫ x, TauCeti.nevanlinnaKernel z x ∂ρ +
          (-logDeriv f I).re :=
  TauCeti.exists_isFiniteMeasure_eq_nevanlinnaKernel_add
    (differentiableOn_neg_logDeriv_of_laguerreCoefficient_nonneg hf hc h)
    (fun _ hz => im_neg_logDeriv_nonneg_of_laguerreCoefficient_nonneg hf hc h hz.le)

end RealRooted
