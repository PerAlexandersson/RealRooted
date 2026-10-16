module

public import RealRooted.MultiplierSequence.QuadraticExponential
public import RealRooted.BorceaBranden.Applications.RealCoordinatePFMultiplier

/-!
# Coordinatewise quadratic exponential multipliers
-/

public noncomputable section

namespace RealRooted.BorceaBranden

/-- The quadratic exponential diagonal action preserves real stability in
each coordinate. -/
theorem mvRealStable_quadraticExponentialMultiplier
    {σ : Type*} [Finite σ] {t : ℝ} (ht : 0 ≤ t) (q : σ)
    {p : _root_.MvPolynomial σ ℝ} (hp : MvRealStable p) :
    MvRealStable
      (realCoordinateDiagonalOperator
        (quadraticExponentialMultiplier t) q p) :=
  IsPFMultiplierSequence.mvRealStable_realCoordinateDiagonalOperator
    (isPFMultiplierSequence_quadraticExponentialMultiplier ht)
    (fun _ => Real.exp_ne_zero _) q hp

end RealRooted.BorceaBranden
