import RealRooted.MultivariateStability.SamePhase
import RealRooted.PFPolynomial
import RealRooted.SamePhaseStability.Nonnegative

/-!
# Pólya-frequency restrictions of multivariate stable polynomials

This file combines multivariate real stability with coefficientwise
nonnegativity.  Every nonnegative common-phase restriction is then a
Pólya-frequency polynomial and in particular has only nonpositive real roots.
-/

namespace RealRooted

noncomputable section

/-- A nonnegative common-phase restriction of a same-phase stable polynomial
with nonnegative coefficients is Pólya-frequency. -/
theorem SamePhaseStable.commonPhaseRestriction_isPFPolynomial
    {σ : Type*} {P : MvPolynomial σ ℝ} (hstable : SamePhaseStable P)
    (hnonneg : MvPolynomial.HasNonnegCoeffs P)
    (wt : σ → ℝ) (hwt : ∀ i, 0 ≤ wt i) :
    IsPFPolynomial (commonPhaseRestriction wt P) :=
  IsPFPolynomial.of_realRooted_nonneg
    (commonPhaseRestriction_hasNonnegCoeffs hnonneg wt hwt)
    (hstable wt hwt)

/-- Every nonnegative common-phase restriction of a real-stable polynomial
with nonnegative coefficients is Pólya-frequency. -/
theorem MvRealStable.commonPhaseRestriction_isPFPolynomial
    {σ : Type*} {P : MvPolynomial σ ℝ} (hstable : MvRealStable P)
    (hnonneg : MvPolynomial.HasNonnegCoeffs P)
    (wt : σ → ℝ) (hwt : ∀ i, 0 ≤ wt i) :
    IsPFPolynomial (commonPhaseRestriction wt P) :=
  hstable.samePhaseStable.commonPhaseRestriction_isPFPolynomial
    hnonneg wt hwt

/-- A nonnegative common-phase restriction is Pólya-frequency when the source
polynomial is zero or multivariate real stable. -/
theorem commonPhaseRestriction_isPFPolynomial_of_eq_zero_or_mvRealStable
    {σ : Type*} {P : MvPolynomial σ ℝ}
    (hstable : P = 0 ∨ MvRealStable P)
    (hnonneg : MvPolynomial.HasNonnegCoeffs P)
    (wt : σ → ℝ) (hwt : ∀ i, 0 ≤ wt i) :
    IsPFPolynomial (commonPhaseRestriction wt P) :=
  SamePhaseStable.commonPhaseRestriction_isPFPolynomial
    (samePhaseStable_of_eq_zero_or_mvRealStable hstable) hnonneg wt hwt

end

end RealRooted
