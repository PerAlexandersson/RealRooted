module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.LogDerivativeStrict
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.RiemannHypothesis.JensenSimple
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Derivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative

/-!
# Strict logarithmic xi moment inequalities under RH

Under Mathlib's RH, the signed logarithmic-derivative coefficients of every
xi derivative give positive definite Hankel matrices at every size and shift.
Their determinants are strictly positive, including the empty determinant.
Infinitely many distinct zeros suffice; no xi zero simplicity is assumed.
-/

public section

open Complex

namespace RealRooted

/-- Under RH, every shifted logarithmic-derivative moment matrix of every
xi derivative is positive definite. -/
theorem posDef_logDeriv_iteratedDeriv_riemannXiTheta
    (hRH : RiemannHypothesis) (s n r : ℕ) :
    Matrix.PosDef (fun i j : Fin n =>
      let k := i.val + j.val + r
      (-1 : ℝ) ^ k *
        (iteratedDeriv k (logDeriv (iteratedDeriv s riemannXiTheta)) 0).re / k.factorial) :=
  (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH s).posDef_logDeriv
    (iteratedDeriv_riemannXiTheta_zero_ne_zero s)
    (orderLE_half_riemannXiTheta.iteratedDeriv differentiable_riemannXiTheta s)
    (by norm_num) (iteratedDeriv_riemannXiTheta_ne_polynomial s) n r

/-- Under RH, all shifted logarithmic-derivative Hankel determinants of
all xi derivatives are strictly positive. -/
theorem det_logDeriv_iteratedDeriv_riemannXiTheta_pos
    (hRH : RiemannHypothesis) (s n r : ℕ) :
    0 < Matrix.det (fun i j : Fin n =>
      let k := i.val + j.val + r
      (-1 : ℝ) ^ k *
        (iteratedDeriv k (logDeriv (iteratedDeriv s riemannXiTheta)) 0).re / k.factorial) :=
  (posDef_logDeriv_iteratedDeriv_riemannXiTheta hRH s n r).det_pos

end RealRooted
