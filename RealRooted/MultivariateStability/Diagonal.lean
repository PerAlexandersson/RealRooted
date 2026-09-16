import RealRooted.Mathlib.Algebra.MvPolynomial.Diagonal
import RealRooted.MultivariateStability.SamePhase

/-!
# Real stability and diagonal restriction

This file transfers multivariate real stability to real-rootedness after all
variables are identified with one univariate coordinate.
-/

namespace RealRooted

/-- Identifying every variable is the unit-weight common-phase restriction. -/
@[simp] theorem commonPhaseRestriction_one_eq_diagonal {σ : Type*}
    (P : MvPolynomial σ ℝ) :
    commonPhaseRestriction (fun _ => 1) P = MvPolynomial.diagonal P := by
  unfold commonPhaseRestriction MvPolynomial.diagonal
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext i
  simp

/-- The diagonal restriction of a multivariate real-stable polynomial splits
over the reals. -/
theorem MvRealStable.diagonal_splits {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvRealStable P) :
    (MvPolynomial.diagonal P).Splits := by
  rw [← commonPhaseRestriction_one_eq_diagonal]
  exact hP.samePhaseStable (fun _ => 1) fun _ => zero_le_one

end RealRooted
