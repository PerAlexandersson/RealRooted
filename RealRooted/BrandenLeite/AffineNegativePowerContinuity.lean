module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import RealRooted.BrandenLeite.AffineNegativePower
import RealRooted.BrandenLeite.AffineNegativePowerRecurrence
import RealRooted.BrandenLeite.RecurrenceContinuity

/-! Coefficientwise limits of canonical affine negative powers. -/

public section

open Filter Topology Polynomial

namespace RealRooted.BrandenLeite

/-- Canonical negative-power coefficient rows vary coefficientwise
continuously with the real exponent and both denominator power series. -/
theorem tendsto_coeff_affineNegativePowerCoeff
    {ι : Type*} {l : Filter ι}
    {κ : ι → ℝ} {κ₀ : ℝ}
    {Q B : ι → PowerSeries ℝ} {Q₀ B₀ : PowerSeries ℝ}
    (hQzero : ∀ t, PowerSeries.constantCoeff (Q t) = 1)
    (hBzero : ∀ t, PowerSeries.constantCoeff (B t) = 0)
    (hQ₀zero : PowerSeries.constantCoeff Q₀ = 1)
    (hB₀zero : PowerSeries.constantCoeff B₀ = 0)
    (hκ : Tendsto κ l (𝓝 κ₀))
    (hQ : ∀ k, Tendsto (fun t => PowerSeries.coeff k (Q t)) l
      (𝓝 (PowerSeries.coeff k Q₀)))
    (hB : ∀ k, Tendsto (fun t => PowerSeries.coeff k (B t)) l
      (𝓝 (PowerSeries.coeff k B₀)))
    (n i : ℕ) :
    Tendsto (fun t => (affineNegativePowerCoeff (κ t) (Q t) (B t) n).coeff i)
      l (𝓝 ((affineNegativePowerCoeff κ₀ Q₀ B₀ n).coeff i)) := by
  refine tendsto_of_negative_power_coefficient_recurrence
    (p := fun t n i => (affineNegativePowerCoeff (κ t) (Q t) (B t) n).coeff i)
    (p₀ := fun n i => (affineNegativePowerCoeff κ₀ Q₀ B₀ n).coeff i)
    (h := fun t k j => (Polynomial.C (PowerSeries.coeff k (Q t)) -
      Polynomial.X * Polynomial.C (PowerSeries.coeff k (B t))).coeff j)
    (h₀ := fun k j => (Polynomial.C (PowerSeries.coeff k Q₀) -
      Polynomial.X * Polynomial.C (PowerSeries.coeff k B₀)).coeff j)
    hκ ?_ ?_ ?_ ?_ n i
  · intro k j
    simp only [mul_comm (Polynomial.X : ℝ[X]), Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
    by_cases hj₀ : j = 0
    · subst j
      simpa using hQ k
    by_cases hj₁ : j = 1
    · subst j
      simpa using (hB k).neg
    simpa [hj₀, hj₁] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 0))
  · intro j
    simp only [affineNegativePowerCoeff_zero _ _ _ (hQzero _) (hBzero _),
      affineNegativePowerCoeff_zero _ _ _ hQ₀zero hB₀zero]
    exact tendsto_const_nhds
  · intro t m j
    exact coeff_affineNegativePowerCoeff_recurrence
      (κ t) (Q t) (B t) (hQzero t) (hBzero t) m j
  · intro m j
    exact coeff_affineNegativePowerCoeff_recurrence
      κ₀ Q₀ B₀ hQ₀zero hB₀zero m j

end RealRooted.BrandenLeite
