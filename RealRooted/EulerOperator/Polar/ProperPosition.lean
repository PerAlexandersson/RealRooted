import RealRooted.EulerOperator.Polar
import RealRooted.ReciprocalShift.ProperPosition

/-!
# Proper position for the polar-theta operator

The polar-theta operator is reciprocal-shift conjugate to differentiation.
This module combines that identity with the reciprocal-shift proper-position
swap and derivative preservation.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The polar-theta operator preserves weak proper position on the bounded
degree PF cone. -/
theorem polarTheta_preserves_prec0 : polarThetaPreservesPrec0Statement := by
  intro N p q hp hq hpd hqd hpq
  rcases hpq with hpzero | hqzero | hpq
  · left
    rw [hpzero]
    simp [polarTheta, theta]
  · right
    left
    rw [hqzero]
    simp [polarTheta, theta]
  · have hstep₁ : Prec (reciprocalShift N q) (reciprocalShift N p) :=
      reciprocalShift_reverses_prec hp hq hpd hqd hpq
    have hsp : IsPFPolynomial (reciprocalShift N p) :=
      reciprocalShift_preserves_pf hp hpd
    have hsq : IsPFPolynomial (reciprocalShift N q) :=
      reciprocalShift_preserves_pf hq hqd
    have hspd : (reciprocalShift N p).natDegree ≤ N := by
      unfold reciprocalShift
      exact (Polynomial.natDegree_reflect_le).trans (max_le le_rfl hpd)
    have hsqd : (reciprocalShift N q).natDegree ≤ N := by
      unfold reciprocalShift
      exact (Polynomial.natDegree_reflect_le).trans (max_le le_rfl hqd)
    have hstep₂ : Prec0 (reciprocalShift N q).derivative (reciprocalShift N p).derivative :=
      derivativePreservesPrec0 hstep₁.toPrec0
    have hdq : IsPFPolynomial (reciprocalShift N q).derivative := hsq.derivative
    have hdp : IsPFPolynomial (reciprocalShift N p).derivative := hsp.derivative
    have hdqd : (reciprocalShift N q).derivative.natDegree ≤ N - 1 :=
      (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right hsqd 1)
    have hdpd : (reciprocalShift N p).derivative.natDegree ≤ N - 1 :=
      (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right hspd 1)
    rcases hstep₂ with hzero | hzero | hprec
    · right
      left
      rw [polarTheta_eq_reciprocalShift_derivative_reciprocalShift N q hqd, hzero]
      simp [reciprocalShift]
    · left
      rw [polarTheta_eq_reciprocalShift_derivative_reciprocalShift N p hpd, hzero]
      simp [reciprocalShift]
    · have hstep₃ : Prec (reciprocalShift (N - 1) ((reciprocalShift N p).derivative))
          (reciprocalShift (N - 1) ((reciprocalShift N q).derivative)) :=
        reciprocalShift_reverses_prec hdq hdp hdqd hdpd hprec
      rw [polarTheta_eq_reciprocalShift_derivative_reciprocalShift N p hpd,
        polarTheta_eq_reciprocalShift_derivative_reciprocalShift N q hqd]
      exact hstep₃.toPrec0

end RealRooted
