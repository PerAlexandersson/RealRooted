module

public import RealRooted.EffectiveBKW.PathCube.GeneratingFunction
public import RealRooted.EffectiveBKW.PathCube.ConjugateModes
import Mathlib.Tactic.Ring

/-!
# Normalization of the actual rational generating function
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube

/-- Rescale a real series and then include its coefficients in the complex field. -/
noncomputable def normalization (R : ℝ) : PowerSeries ℝ →+* PowerSeries ℂ :=
  (PowerSeries.map Complex.ofRealHom).comp (PowerSeries.rescale R⁻¹)

/-- The actual transfer series in normalized reciprocal-root coordinates. -/
noncomputable def normalizedSeries (t R : ℝ) : PowerSeries ℂ :=
  normalization R (PowerSeries.mk (fun r ↦ (row r).eval t))

/-- The denominator after rescaling the actual generating function. -/
noncomputable def normalizedDenominator (t R : ℝ) : PowerSeries ℂ :=
  normalization R (denominator t)

/-- The numerator after rescaling the actual generating function. -/
noncomputable def normalizedNumerator (t R : ℝ) : PowerSeries ℂ :=
  normalization R (numerator t)

/-- Coefficients of the normalized orbit are exactly the normalized row values. -/
theorem coeff_normalizedSeries (t R : ℝ) (n : ℕ) :
    PowerSeries.coeff n (normalizedSeries t R) =
      ((R⁻¹ ^ n * (row n).eval t : ℝ) : ℂ) := by
  simp [normalizedSeries, normalization, PowerSeries.coeff_map]

/-- The rational identity is preserved by the normalization ring homomorphism. -/
theorem normalized_generating_function (t R : ℝ) :
    normalizedDenominator t R * normalizedSeries t R = normalizedNumerator t R := by
  simpa only [normalizedDenominator, normalizedSeries, normalizedNumerator, map_mul] using
    congrArg (normalization R) (generating_function t)

private theorem normalization_C (R u : ℝ) :
    normalization R (PowerSeries.C u) = PowerSeries.C (u : ℂ) := by
  ext n
  by_cases hn : n = 0 <;> simp [normalization, PowerSeries.coeff_map, PowerSeries.coeff_C, hn]

private theorem normalization_X (R : ℝ) :
    normalization R PowerSeries.X = PowerSeries.C (R⁻¹ : ℂ) * PowerSeries.X := by
  simp [normalization, PowerSeries.map_C]

/-- The normalized numerator has precisely the three certified scalar weights. -/
theorem normalizedNumerator_eq (t R : ℝ) :
    normalizedNumerator t R =
      (RationalSeries.cubicPolynomial (-2 * t * R⁻¹) (-2 * t * R⁻¹ ^ 2)
        (-t ^ 2 * (1 - t) * R⁻¹ ^ 3) : PowerSeries ℂ) := by
  simp only [normalizedNumerator, numerator, map_sub, map_mul, map_pow, map_one,
    normalization_C, normalization_X, RationalSeries.cubicPolynomial, Polynomial.coe_add,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_one, Polynomial.coe_C,
    Polynomial.coe_X]
  push_cast
  simp only [map_neg, map_mul, map_pow, map_ofNat, map_sub, map_one]
  ring

end RealRooted.EffectiveBKW.PathCube
