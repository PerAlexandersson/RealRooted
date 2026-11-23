module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Hermite.FormalDifferential.CenteredLimit
import RealRooted.Hermite.FormalDifferential.Covariance
import RealRooted.Hermite.FormalDifferential.Translation
import RealRooted.Hermite.FormalDifferential.Composition
import RealRooted.Mathlib.RingTheory.PowerSeries.ExponentialJet

/-!
# Centered root-scaled limits of actual formal iterates

The symbol need only agree with an exponential to a finite order. The
normalization is root scaling by `m^(-1/p)` after translation by `-m*a`.
For a monic degree-`d` input this equals the usual
`m^(-d/p) phi(D)^m P(m^(1/p) X-m*a)` for positive `m`.
-/

public section

open Polynomial Filter Topology

namespace RealRooted.HermitePoulain

/-- The literal iterated output, translated and root-scaled, has the
exponential differential limit determined by its first possible centered term.
Zero inputs, constants and a zero discrepancy are allowed. -/
theorem tendsto_coeff_rescaled_iterate_of_exponential_jet
    {φ : PowerSeries ℝ} (a : ℝ) {p : ℕ} (hp : 0 < p)
    (hjet : ∀ k < p, PowerSeries.coeff k φ = a ^ k / (k.factorial : ℝ))
    (P : ℝ[X]) (j : ℕ) :
    Tendsto (fun m : ℕ ↦
      ((((formalDifferentialOperator φ)^[m] P).comp (X + C (-(m : ℝ) * a))).scaleRoots
        ((m : ℝ) ^ (-(p : ℝ)⁻¹))).coeff j) atTop
      (𝓝 ((formalDifferentialOperator
        (PowerSeries.expand p hp.ne'
          (PowerSeries.rescale (PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ))
            (PowerSeries.exp ℝ))) (P.scaleRoots 0)).coeff j)) := by
  obtain ⟨ψ, hfactor, hψ⟩ :=
    PowerSeries.exists_centered_factor_of_exponential_jet a p hjet
  have hχ : PowerSeries.constantCoeff (1 + PowerSeries.X ^ p * ψ) = 1 := by
    simp [hp.ne']
  have heq (m : ℕ) (r : ℝ) :
      formalDifferentialOperator
          ((PowerSeries.rescale r (1 + PowerSeries.X ^ p * ψ)) ^ m) (P.scaleRoots r) =
        (((formalDifferentialOperator φ)^[m] P).comp
          (X + C (-(m : ℝ) * a))).scaleRoots r := by
    rw [← map_pow, ← scaleRoots_formalDifferentialOperator
      (by rw [map_pow, hχ, one_pow]; exact one_ne_zero), ← hfactor,
      formalDifferentialOperator_linear_exp_mul_pow, formalDifferentialOperator_pow]
    simp only [mul_neg, neg_mul]
  have hlim := tendsto_coeff_centered_formalDifferentialOperator ψ hp P j
  simpa only [heq, hψ] using hlim

end RealRooted.HermitePoulain
