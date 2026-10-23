import RealRooted.OperatorMatrix.Composition
import RealRooted.OperatorMatrix.OneThetaX

/-!
# The Euler-derivative lag operator matrices

This file begins the structural operator-matrix proof for polynomial families
satisfying `P (n + 2) = theta (P (n + 1)) + X * theta (P n)`.  The first
factor is the identity-top matrix `[[0, I], [X, theta]]`.
-/

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix.EulerDerivativeLag

/-- The identity-top factor `U = [[0, I], [X, theta]]`. -/
def identityTop : Matrix (Fin 2) (Fin 2) (Module.End ℝ ℝ[X]) :=
  !![0, Letter.one.linearMap; Letter.x.linearMap, Letter.theta.linearMap]

/-- The identity-top factor preserves every zero-aware ordered PF pair. -/
theorem preservesOrderedPFPair_identityTop :
    PreservesOrderedPFPair 0 Letter.one.linearMap
      Letter.x.linearMap Letter.theta.linearMap := by
  intro p q hp hq hpq
  have hXp : IsPFPolynomial (X * p) := hp.X_mul
  have hthetaQ : IsPFPolynomial (RealRooted.theta q) := theta_preserves_pf hq
  have hqXp : Interl q (X * p) :=
    (interl_iff_interl_X_mul hp hq).mp hpq
  have hqthetaQ : Interl q (RealRooted.theta q) := hq.interl_theta
  have hinterl : Interl q (X * p + RealRooted.theta q) :=
    interl_add_right_of_common_left_of_nonneg hqXp hqthetaQ
      hXp.hasNonnegCoeffs hthetaQ.hasNonnegCoeffs
  have hbottom : IsPFPolynomial (X * p + RealRooted.theta q) := by
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    · exact hXp.hasNonnegCoeffs.add hthetaQ.hasNonnegCoeffs
    by_cases hq0 : q = 0
    · subst q
      simpa [RealRooted.theta] using hXp.eq_zero_or_splits
    by_cases hzero : X * p + RealRooted.theta q = 0
    · exact Or.inl hzero
    · exact Or.inr (hinterl.toStrictInterl_of_ne hq0 hzero).2.1.2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Letter.linearMap_one, LinearMap.zero_apply, zero_add] using hq
  · simpa only [Letter.linearMap_x, Letter.linearMap_theta, LinearMap.zero_apply,
      zero_add] using hbottom
  · simpa only [Letter.linearMap_one, Letter.linearMap_x, Letter.linearMap_theta,
      LinearMap.zero_apply, zero_add] using hinterl

/-- The matrix `identityTop` preserves ordered PF vectors. -/
theorem preservesOrderedPF_identityTop : PreservesOrderedPF identityTop := by
  rw [preservesOrderedPF_two_two_iff]
  simpa [identityTop] using preservesOrderedPFPair_identityTop

end RealRooted.OperatorMatrix.EulerDerivativeLag
