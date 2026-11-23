module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import RealRooted.AissenSchoenbergWhitneyBase
public import Mathlib.Analysis.CStarAlgebra.Classes
import RealRooted.RiemannHypothesis.TotalPositivity
public import RealRooted.LaguerreInequalities.AuxiliaryProduct
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.AuxiliaryPowers

/-!
# Higher-even auxiliary inequalities for xi derivatives under RH

Cardon's auxiliary `X^n + 1`, for every positive even `n`, gives nonnegative
Taylor coefficients at every real center for each xi derivative shift.
Compressing the coefficients by `n` gives the stronger PF conclusion.
-/

public section

open Polynomial

namespace RealRooted

/-- Under RH, compressed higher-even auxiliary coefficients of every xi
derivative form a PF sequence at every real center. -/
theorem isPolyaFreqSeq_auxiliaryCoefficient_riemannXiTheta (hRH : RiemannHypothesis)
    (s : ℕ) {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝ) :
    IsPolyaFreqSeq (fun k ↦ auxiliaryCoefficient (X ^ n + 1)
      (iteratedDeriv s riemannXiTheta) x (n * k)) :=
  IsLaguerrePolya.isPolyaFreqSeq_auxiliaryCoefficient
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s).toLaguerrePolya hn he x

/-- Under RH, every Taylor coefficient of a positive-even auxiliary
product of an xi derivative is nonnegative at every real center. -/
theorem auxiliaryCoefficient_riemannXiTheta_nonneg (hRH : RiemannHypothesis)
    (s : ℕ) {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝ) (k : ℕ) :
    0 ≤ auxiliaryCoefficient (X ^ n + 1) (iteratedDeriv s riemannXiTheta) x k :=
  IsLaguerrePolya.auxiliaryCoefficient_power_nonneg
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s).toLaguerrePolya hn he x k

end RealRooted
