import RealRooted.EulerianCompletion
import RealRooted.EulerOperator.Polar.Pencil

/-!
# Proper position for the lowering Euler step

This module keeps the heavier proper-position dependencies separate from the
algebraic and coefficientwise lowering-Euler API in `EulerianCompletion`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- At the tight degree boundary, the lowering Euler step precedes a
nonnegative self-reciprocal input. -/
theorem loweringEulerStep_prec_self_of_reflect {M : ℕ} {p : ℝ[X]}
    (hM : 2 ≤ M) (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree = M) (hconst : p.coeff 0 ≠ 0)
    (hsym : p.reflect M = p) :
    StrictInterl (loweringEulerStep M p) p := by
  have hp0 : p ≠ 0 := fun hzero ↦ hconst (by simp [hzero])
  have hshift : 2 ≤ (reciprocalShift M p).natDegree := by
    rw [reciprocalShift, hsym, hpdeg]
    exact hM
  have hpolar : StrictInterl (polarTheta M p) p :=
    prec_polarTheta_self hp hpdeg.le hshift
  have hderiv : StrictInterl p.derivative p :=
    (derivative_interlaces (hp.ne_zero_and_splits hp0).2 (by lia)).toStrictInterl
  have hpolarPos : HasPosLeadingCoeff (polarTheta M p) :=
    (polarTheta_preserves_pf hp hpdeg.le).hasNonnegCoeffs.pos_leadingCoeff
      hpolar.1.1
  have hderivPos : HasPosLeadingCoeff p.derivative :=
    (hp.hasNonnegCoeffs.pos_leadingCoeff hp0).derivative (by lia)
  have hcore : StrictInterl (polarTheta M p + p.derivative) p :=
    StrictInterl.add_of_right_of_posLeadingCoeff hpolar hderiv hpolarPos hderivPos
  have heq : loweringEulerStep M p = polarTheta M p + p.derivative := by
    simp [loweringEulerStep, polarTheta, theta]
    ring
  rw [heq]
  exact hcore

end RealRooted
