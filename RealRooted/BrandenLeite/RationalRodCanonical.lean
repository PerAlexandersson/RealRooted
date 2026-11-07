module

public import RealRooted.BrandenLeite.StationaryTiling
public import RealRooted.Mathlib.RingTheory.PowerSeries.AffineNegativePower
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerOne
import Mathlib.Tactic.Ring

/-! # Rational rod rows as canonical exponent-one negative-power coefficients -/

public section

namespace RealRooted.BrandenLeite

/-- The finite rational rod row agrees with the canonical negative-power
coefficient at exponent one. This identity includes constant backgrounds. -/
theorem rationalRodRow_eq_affineNegativePowerCoeff
    (ys : List ℝ) (c : ℝ) {r : ℕ} (hr : r ≠ 0)
    (xs : List ℝ) (n : ℕ) :
    rationalRodRow ys c r xs n =
      PowerSeries.affineNegativePowerCoeff 1 (rationalBackgroundDenominator ys)
        (markedFactorSeries c r xs) n := by
  let H := rationalRodDenominatorSeries ys c r xs
  have hQ : PowerSeries.constantCoeff (rationalBackgroundDenominator ys) = 1 :=
    constantCoeff_rationalBackgroundDenominator ys
  have hB : PowerSeries.constantCoeff (markedFactorSeries c r xs) = 0 :=
    constantCoeff_markedFactorSeries c hr xs
  have hlift (f : PowerSeries ℝ) : polynomialLift f = PowerSeries.map Polynomial.C f := by
    ext k
    simp [polynomialLift]
  have hH : PowerSeries.constantCoeff H = 1 := by
    simp [H, rationalRodDenominatorSeries, polynomialLift, hQ, hB]
  have hcanonical := PowerSeries.mul_subst_binomialSeries_neg_one H hH
  have hold : H * rationalRodGeneratingSeries ys c r xs = 1 :=
    rationalRodDenominator_mul_generatingSeries ys c hr xs
  have heq : rationalRodGeneratingSeries ys c r xs =
      PowerSeries.subst (H - 1)
        (PowerSeries.binomialSeries (Polynomial ℝ) (-1 : Polynomial ℝ)) := by
    calc
      _ = rationalRodGeneratingSeries ys c r xs *
          (H * PowerSeries.subst (H - 1)
            (PowerSeries.binomialSeries (Polynomial ℝ) (-1 : Polynomial ℝ))) := by
          rw [hcanonical, mul_one]
      _ = (H * rationalRodGeneratingSeries ys c r xs) *
          PowerSeries.subst (H - 1)
            (PowerSeries.binomialSeries (Polynomial ℝ) (-1 : Polynomial ℝ)) := by ring
      _ = _ := by rw [hold, one_mul]
  rw [← coeff_rationalRodGeneratingSeries, heq]
  simp only [PowerSeries.affineNegativePowerCoeff, H,
    rationalRodDenominatorSeries, hlift, map_one]

end RealRooted.BrandenLeite
