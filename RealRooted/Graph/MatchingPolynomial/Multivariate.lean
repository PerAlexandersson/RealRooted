import RealRooted.Graph.IndependencePolynomial.Multivariate
import RealRooted.Graph.MatchingPolynomial

/-!
# Multivariate matching-generating polynomials

The intrinsic edge-variable polynomial agrees with the multivariate
independence polynomial of the line graph.  Consequently it is same-phase
stable, as is every nonnegative edge-weighted coordinate scaling.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

noncomputable local instance edgeSetFintype {V : Type u} [Fintype V]
    (G : _root_.SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-- The intrinsic multivariate edge-matching polynomial. -/
def multivariateMatchingPolynomialByEdges {V : Type u} [Fintype V]
    (G : _root_.SimpleGraph V) : MvPolynomial G.edgeSet ℝ := by
  classical
  exact ∑ M ∈ (Finset.univ.filter fun M : Finset G.edgeSet =>
      IsMatchingEdgeFinset G M),
    ∏ e ∈ M, MvPolynomial.X e

/-- The intrinsic edge-weighted multivariate matching polynomial. -/
def weightedMultivariateMatchingPolynomialByEdges
    {V : Type u} [Fintype V] (G : _root_.SimpleGraph V)
    (wt : G.edgeSet → ℝ) : MvPolynomial G.edgeSet ℝ :=
  coordinateScale wt (multivariateMatchingPolynomialByEdges G)

theorem weightedMultivariateMatchingPolynomialByEdges_eq_coordinateScale
    {V : Type u} [Fintype V] (G : _root_.SimpleGraph V)
    (wt : G.edgeSet → ℝ) :
    weightedMultivariateMatchingPolynomialByEdges G wt =
      coordinateScale wt (multivariateMatchingPolynomialByEdges G) := by
  rfl

/-- Edge matchings are independent sets of the line graph, also at the
multivariate level. -/
theorem multivariateMatchingPolynomialByEdges_eq_multivariateIndepPoly_lineGraph
    {V : Type u} [Fintype V] (G : _root_.SimpleGraph V) :
    multivariateMatchingPolynomialByEdges G =
      multivariateIndepPoly G.lineGraph := by
  classical
  unfold multivariateMatchingPolynomialByEdges multivariateIndepPoly indepSetsOn
  congr 1
  ext M
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
    true_and]
  exact (and_iff_right (Finset.mem_univ M)).trans
    (isMatchingEdgeFinset_iff_lineGraph_isIndepSet G M)

/-- The edge-weighted matching polynomial is the correspondingly weighted
multivariate independence polynomial of the line graph. -/
theorem weightedMultivariateMatchingPolynomialByEdges_eq_weightedMultivariateIndepPoly_lineGraph
    {V : Type u} [Fintype V] (G : _root_.SimpleGraph V)
    (wt : G.edgeSet → ℝ) :
    weightedMultivariateMatchingPolynomialByEdges G wt =
      weightedMultivariateIndepPoly G.lineGraph wt := by
  rw [weightedMultivariateMatchingPolynomialByEdges_eq_coordinateScale,
    weightedMultivariateIndepPoly_eq_coordinateScale,
    multivariateMatchingPolynomialByEdges_eq_multivariateIndepPoly_lineGraph]

/-- Common-phase restriction recovers the intrinsic weighted univariate
matching polynomial. -/
theorem commonPhaseRestriction_multivariateMatchingPolynomialByEdges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ) :
    commonPhaseRestriction wt (multivariateMatchingPolynomialByEdges G) =
      weightedMatchingPolynomialByEdges G wt := by
  classical
  simp only [commonPhaseRestriction, multivariateMatchingPolynomialByEdges,
    map_sum, map_prod, MvPolynomial.eval₂Hom_X', prod_mul_distrib,
    prod_const, weightedMatchingPolynomialByEdges]
  apply Finset.sum_congr
  · ext M
    simp
  · intro M hM
    rfl

theorem commonPhaseRestriction_weightedMultivariateMatchingPolynomialByEdges
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt t : G.edgeSet → ℝ) :
    commonPhaseRestriction t
        (weightedMultivariateMatchingPolynomialByEdges G wt) =
      weightedMatchingPolynomialByEdges G (fun e => wt e * t e) := by
  rw [weightedMultivariateMatchingPolynomialByEdges_eq_coordinateScale,
    commonPhaseRestriction_coordinateScale,
    commonPhaseRestriction_multivariateMatchingPolynomialByEdges]

/-- Multivariate matching polynomials are same-phase stable. -/
theorem multivariateMatchingPolynomialByEdges_samePhaseStable
    {V : Type u} [Fintype V]
    (G : _root_.SimpleGraph V) :
    SamePhaseStable (multivariateMatchingPolynomialByEdges G) := by
  classical
  rw [multivariateMatchingPolynomialByEdges_eq_multivariateIndepPoly_lineGraph]
  exact (lineGraph_clawFree G).multivariateIndepPoly_samePhaseStable

/-- Nonnegative edge weighting preserves same-phase stability. -/
theorem weightedMultivariateMatchingPolynomialByEdges_samePhaseStable
    {V : Type u} [Fintype V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    SamePhaseStable (weightedMultivariateMatchingPolynomialByEdges G wt) := by
  classical
  rw [weightedMultivariateMatchingPolynomialByEdges_eq_coordinateScale]
  exact (multivariateMatchingPolynomialByEdges_samePhaseStable G).coordinateScale hwt

end Graph
end RealRooted
