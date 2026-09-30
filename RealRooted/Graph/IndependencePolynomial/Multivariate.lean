import RealRooted.Graph.IndependencePolynomial.ClawFree
import RealRooted.SamePhaseStability

/-!
# Multivariate independence polynomials

This file defines the multivariate independence polynomial and its weighted
coordinate scaling.  Common-phase restriction recovers the existing weighted
univariate independence polynomial.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- The multivariate independence polynomial of a finite graph. -/
def multivariateIndepPoly {V : Type u} [Fintype V]
    (G : _root_.SimpleGraph V) : MvPolynomial V ℝ := by
  classical
  exact ∑ s ∈ indepSetsOn G Finset.univ,
    ∏ v ∈ s, MvPolynomial.X v

/-- The vertex-weighted multivariate independence polynomial. -/
def weightedMultivariateIndepPoly {V : Type u} [Fintype V]
    (G : _root_.SimpleGraph V) (wt : V → ℝ) : MvPolynomial V ℝ :=
  coordinateScale wt (multivariateIndepPoly G)

theorem weightedMultivariateIndepPoly_eq_coordinateScale
    {V : Type u} [Fintype V] (G : _root_.SimpleGraph V) (wt : V → ℝ) :
    weightedMultivariateIndepPoly G wt =
      coordinateScale wt (multivariateIndepPoly G) := by
  rfl

/-- A common-phase specialization is the weighted univariate independence
polynomial. -/
theorem commonPhaseRestriction_multivariateIndepPoly
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ) :
    commonPhaseRestriction wt (multivariateIndepPoly G) =
      weightedIndepPoly G wt := by
  classical
  simp only [commonPhaseRestriction, multivariateIndepPoly, map_sum, map_prod,
    MvPolynomial.eval₂Hom_X', prod_mul_distrib, prod_const,
    weightedIndepPoly, weightedIndepPolyOn]
  apply Finset.sum_congr
  · ext s
    simp [indepSetsOn]
  · intro s hs
    rfl

theorem commonPhaseRestriction_weightedMultivariateIndepPoly
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (wt t : V → ℝ) :
    commonPhaseRestriction t (weightedMultivariateIndepPoly G wt) =
      weightedIndepPoly G (fun v => wt v * t v) := by
  rw [weightedMultivariateIndepPoly_eq_coordinateScale,
    commonPhaseRestriction_coordinateScale,
    commonPhaseRestriction_multivariateIndepPoly]

/-- Setting every common-phase coordinate to `X` recovers the ordinary
univariate independence polynomial. -/
@[simp] theorem commonPhaseRestriction_one_multivariateIndepPoly
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    commonPhaseRestriction (fun _ => 1) (multivariateIndepPoly G) =
      indepPoly G := by
  classical
  rw [commonPhaseRestriction_multivariateIndepPoly, weightedIndepPoly_one]

/-- Setting the phase direction to one recovers the existing weighted
univariate independence polynomial. -/
@[simp] theorem commonPhaseRestriction_one_weightedMultivariateIndepPoly
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (wt : V → ℝ) :
    commonPhaseRestriction (fun _ => 1)
        (weightedMultivariateIndepPoly G wt) =
      weightedIndepPoly G wt := by
  simpa using
    commonPhaseRestriction_weightedMultivariateIndepPoly G wt (fun _ => 1)

/-- The forward implication in the Leake--Ryder characterization. -/
theorem ClawFree.multivariateIndepPoly_samePhaseStable
    {V : Type u} [Fintype V] {G : _root_.SimpleGraph V} (hG : ClawFree G) :
    SamePhaseStable (multivariateIndepPoly G) := by
  classical
  intro wt hwt
  rw [commonPhaseRestriction_multivariateIndepPoly]
  exact clawFree_weightedIndepPoly_splits hG wt hwt

/-- Nonnegative vertex weighting preserves same-phase stability for a
claw-free graph. -/
theorem ClawFree.weightedMultivariateIndepPoly_samePhaseStable
    {V : Type u} [Fintype V] {G : _root_.SimpleGraph V} (hG : ClawFree G)
    (wt : V → ℝ) (hwt : ∀ v, 0 ≤ wt v) :
    SamePhaseStable (weightedMultivariateIndepPoly G wt) := by
  classical
  rw [weightedMultivariateIndepPoly_eq_coordinateScale]
  exact hG.multivariateIndepPoly_samePhaseStable.coordinateScale hwt

/-- The unit common-phase specialization recovers the checked weighted
univariate splitness theorem. -/
theorem ClawFree.commonPhaseRestriction_one_weightedMultivariateIndepPoly_splits
    {V : Type u} [Fintype V] {G : _root_.SimpleGraph V} (hG : ClawFree G)
    (wt : V → ℝ) (hwt : ∀ v, 0 ≤ wt v) :
    (commonPhaseRestriction (fun _ => 1)
      (weightedMultivariateIndepPoly G wt)).Splits := by
  classical
  rw [commonPhaseRestriction_one_weightedMultivariateIndepPoly]
  exact clawFree_weightedIndepPoly_splits hG wt hwt

end Graph
end RealRooted
