module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Hermite.FormalDifferential.OperatorLimits
import RealRooted.Mathlib.RingTheory.PowerSeries.RescaledPowerLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The centered finite-input limit

After rescaling a centered symbol and the roots of a fixed polynomial, the
iterated differential action tends coefficientwise to the exponential of
the first possible differential term acting on the leading monomial.
-/

public section

open Polynomial Filter Topology

namespace RealRooted.HermitePoulain

/-- Shrinking input roots and rescaling a centered formal symbol give the
generalized exponential differential limit. The input may be zero or constant. -/
theorem tendsto_coeff_centered_formalDifferentialOperator
    (ψ : PowerSeries ℝ) {p : ℕ} (hp : 0 < p) (P : ℝ[X]) (j : ℕ) :
    Tendsto (fun m : ℕ ↦ (formalDifferentialOperator
      ((PowerSeries.rescale ((m : ℝ) ^ (-(p : ℝ)⁻¹))
        (1 + PowerSeries.X ^ p * ψ)) ^ m)
      (P.scaleRoots ((m : ℝ) ^ (-(p : ℝ)⁻¹)))).coeff j) atTop
      (𝓝 ((formalDifferentialOperator
        (PowerSeries.expand p hp.ne'
          (PowerSeries.rescale (PowerSeries.constantCoeff ψ) (PowerSeries.exp ℝ)))
        (P.scaleRoots 0)).coeff j)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hr : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (-(p : ℝ)⁻¹)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (inv_pos.mpr hpR)).comp tendsto_natCast_atTop_atTop
  apply tendsto_coeff_formalDifferentialOperator (N := P.natDegree)
  · intro m
    exact le_of_eq (natDegree_scaleRoots P _)
  · exact le_of_eq (natDegree_scaleRoots P 0)
  · exact PowerSeries.tendsto_coeff_rescale_pow_exp ψ hp
  · intro k
    simpa only [coeff_scaleRoots] using
      (tendsto_const_nhds.mul (hr.pow (P.natDegree - k)))

end RealRooted.HermitePoulain
