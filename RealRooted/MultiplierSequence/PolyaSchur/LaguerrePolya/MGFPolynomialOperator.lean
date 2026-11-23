/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
public import Mathlib.Probability.Moments.ComplexMGF
import RealRooted.Mathlib.MeasureTheory.Integral.PolynomialTranslation
import RealRooted.Mathlib.Probability.Moments.MGFTaylor
import Mathlib.Tactic.TypeStar

/-!
# Polynomial translation averages as moment-generating differential operators

The complex moment-generating function is only required to be analytic near
zero. No Laguerre-Polya or PF assumption occurs in this identity. Applying it
to a nonpositive translation variable gives polynomial convolution directly.
-/

public section

open Complex MeasureTheory Polynomial ProbabilityTheory Set

namespace RealRooted

variable {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} {Y : Ω → ℝ}

/-- The Taylor differential operator of a complex moment-generating function
is exactly averaging translations of the polynomial input. The interior-domain
hypothesis supplies all genuine moments and justifies the finite integration. -/
theorem taylorDifferentialOperator_complexMGF_eval
    (h0 : 0 ∈ interior (integrableExpSet Y mu)) (p : ℝ[X]) (x : ℝ) :
    (taylorDifferentialOperator (complexMGF Y mu) p).eval x =
      ∫ w, p.eval (x + Y w) ∂mu := by
  have hmom := integrable_pow_of_mem_interior_integrableExpSet h0
  rw [integral_polynomial_eval_add_eq_sum_derivative hmom,
    taylorDifferentialOperator, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [eval_mul, eval_C, iteratedDeriv_complexMGF_zero h0, ← ofReal_natCast,
    ← ofReal_div, ofReal_re]

/-- A negative real translation variable gives the one-sided convolution form.
Nonnegativity is not needed for this algebraic identity, only for later root location. -/
theorem taylorDifferentialOperator_complexMGF_neg_eval
    {T : Ω → ℝ} (h0 : 0 ∈ interior (integrableExpSet (fun w => -T w) mu))
    (p : ℝ[X]) (x : ℝ) :
    (taylorDifferentialOperator (complexMGF (fun w => -T w) mu) p).eval x =
      ∫ w, p.eval (x - T w) ∂mu := by
  simpa only [sub_eq_add_neg] using taylorDifferentialOperator_complexMGF_eval h0 p x

end RealRooted
