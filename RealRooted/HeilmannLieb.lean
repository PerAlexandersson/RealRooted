import RealRooted.Graph.IndependencePolynomial.ClawFree
import RealRooted.Graph.MatchingPolynomial

/-!
# Heilmann--Lieb theorem

This file applies the claw-free independence-polynomial theorem to line graphs
and derives real-rootedness and Pólya-frequency results for matching
polynomials.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- Heilmann--Lieb theorem for the matching-generating polynomial: it is the
independence polynomial of the claw-free line graph. -/
theorem matchingGeneratingPolynomial_splits
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    (matchingGeneratingPolynomial G).Splits := by
  classical
  exact clawFree_indepPoly_splits (G := G.lineGraph) (lineGraph_clawFree G)

/-- Heilmann--Lieb theorem for the intrinsic edge-matching polynomial. -/
theorem matchingPolynomialByEdges_splits
    {V : Type u} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    (matchingPolynomialByEdges G).Splits := by
  rw [matchingPolynomialByEdges_eq_matchingGeneratingPolynomial]
  exact matchingGeneratingPolynomial_splits G

/-- Weighted Heilmann--Lieb theorem for the line-graph matching polynomial. -/
theorem weightedMatchingGeneratingPolynomial_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    (weightedMatchingGeneratingPolynomial G wt).Splits := by
  classical
  exact clawFree_weightedIndepPoly_splits
    (G := G.lineGraph) (lineGraph_clawFree G) wt hwt

/-- Weighted Heilmann--Lieb theorem for the intrinsic edge-matching
polynomial. -/
theorem weightedMatchingPolynomialByEdges_splits
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    (weightedMatchingPolynomialByEdges G wt).Splits := by
  rw [weightedMatchingPolynomialByEdges_eq_weightedMatchingGeneratingPolynomial]
  exact weightedMatchingGeneratingPolynomial_splits G wt hwt

/-- The intrinsic weighted matching polynomial is PF for nonnegative edge
weights. -/
theorem weightedMatchingPolynomialByEdges_isPFPolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    IsPFPolynomial (weightedMatchingPolynomialByEdges G wt) := by
  apply IsPFPolynomial.of_realRooted_nonneg
  · intro k
    rw [coeff_weightedMatchingPolynomialByEdges, weightedMatchingNumber]
    apply Finset.sum_nonneg
    intro M hM
    split_ifs
    · apply Finset.prod_nonneg
      intro e he
      exact hwt e
    · positivity
  · exact weightedMatchingPolynomialByEdges_splits G wt hwt

end Graph
end RealRooted
