module

public import RealRooted.MultiplierSequence
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import RealRooted.MultiplierSequence.JensenBessel
import RealRooted.QuadraticRoot
import Mathlib.Tactic.Ring

/-!
# The quadratic obstruction below the Bessel parameter range

Outside the negative integers, the reciprocal-Gamma scale is nonzero.
The degree-two Jensen polynomial then has the Laguerre discriminant sign,
which excludes every parameter below `-2`.
-/

public section

open Polynomial

namespace RealRooted

/-- Below `-2`, every nonintegral parameter already fails at the quadratic
Jensen polynomial. Negative integers are excluded from this obstruction. -/
theorem not_splits_jensenPolynomial_inv_gamma_two {alpha : ℝ}
    (halpha : alpha < -2) (hnat : ∀ n : ℕ, alpha ≠ -(n : ℝ)) :
    ¬ (jensenPolynomial 2
      (fun k ↦ (-1 : ℝ) ^ k * (Real.Gamma (alpha + k + 1))⁻¹)).Splits := by
  have hGamma : Real.Gamma (alpha + 2 + 1) ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro n hn
    apply hnat (n + 3)
    push_cast
    linarith
  have hbad : ¬ (generalizedLaguerre 2 alpha).Splits := by
    rw [generalizedLaguerre_two, monicQuadraticPoly_not_splits_iff_discrim_neg]
    nlinarith
  intro hs
  rw [jensenPolynomial_inv_gamma_eq] at hs
  norm_num only [Nat.cast_ofNat] at hs
  have hscale : (C ((Real.Gamma (alpha + 2 + 1))⁻¹) : ℝ[X]) ≠ 0 :=
    C_ne_zero.mpr (inv_ne_zero hGamma)
  have hsplit := (splits_mul_iff_right hscale (Splits.C _)).mp hs
  apply hbad
  simpa only [comp_neg_X_comp_neg_X] using hsplit.comp_neg_X

end RealRooted
