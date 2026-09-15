import RealRooted.Basic.Coefficients
import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative
import RealRooted.SamePhaseStability

/-!
# Nonnegative common-phase restrictions

This file proves the coefficientwise nonnegativity of common-phase
restrictions without importing stability or root-location machinery.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- Nonnegative weights and multivariate coefficients give a univariate
polynomial with nonnegative coefficients. -/
theorem commonPhaseRestriction_hasNonnegCoeffs {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvPolynomial.HasNonnegCoeffs P)
    (wt : σ → ℝ) (hwt : ∀ i, 0 ≤ wt i) :
    HasNonnegCoeffs (commonPhaseRestriction wt P) := by
  classical
  rw [MvPolynomial.as_sum P]
  unfold commonPhaseRestriction
  rw [map_sum]
  apply hasNonnegCoeffs_finsetSum
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial]
  apply (hasNonnegCoeffs_C (hP d)).mul
  unfold Finsupp.prod
  apply hasNonnegCoeffs_finsetProd
  intro i hi
  exact (nonnegCoeffs_C_mul (hwt i) hasNonnegCoeffs_X).pow (d i)

end

end RealRooted
