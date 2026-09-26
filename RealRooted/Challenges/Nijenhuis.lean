import RealRooted.RookPolynomial

/-!
# Nijenhuis's weighted rook-polynomial theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "nijenhuis-rook-polynomials"
authors = ["Nijenhuis"]
years = [1976]

[[definitions]]
name = "RealRooted.Rook.IsRookPlacement"
module = "RealRooted.RookPolynomial"

[[definitions]]
name = "RealRooted.Rook.weightedRookPolynomial"
module = "RealRooted.RookPolynomial"

[[definitions]]
name = "RealRooted.Rook.nijenhuisRookPolynomial"
module = "RealRooted.RookPolynomial"

[[theorems]]
name = "RealRooted.Challenges.Nijenhuis.bipartiteMatchingIdentity"

[[theorems]]
name = "RealRooted.Challenges.Nijenhuis.weightedRealRooted"

[[theorems]]
name = "RealRooted.Challenges.Nijenhuis.signedRoots_nonnegative"

[[theorems]]
name = "RealRooted.Challenges.Nijenhuis.ordinaryRealRooted"
-->

<!-- realrooted-catalog-content -->
# Rook polynomials

Weighted rook polynomials are weighted matching polynomials of complete
bipartite graphs. For every nonnegative finite matrix they are real-rooted,
with nonpositive roots; Nijenhuis’s signed normalization has nonnegative roots.

## References

A. Nijenhuis, “On permanents and the zeros of rook polynomials,” *Journal of
Combinatorial Theory, Series A* 21 (1976), 240–244. See also the
[rook-polynomial overview on
symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedGraphs.htm#rookPolynomials).
<!-- /realrooted-catalog-content -->

This challenge entry uses ordinary nonattacking rook placements. It is
separate from the project's non-nesting rook-polynomial model.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Challenges
namespace Nijenhuis

universe u v

/-- Weighted rook placements are exactly weighted matchings in the complete
bipartite row-column graph. -/
theorem bipartiteMatchingIdentity {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) :
    Rook.weightedRookPolynomial A =
      Graph.weightedMatchingPolynomialByEdges
        (_root_.completeBipartiteGraph Row Column)
        (Rook.matrixEdgeWeight A) :=
  Rook.weightedRookPolynomial_eq_weightedMatchingPolynomialByEdges A

/-- Nijenhuis's theorem: a nonnegative finite rectangular matrix has a
real-rooted weighted rook polynomial. -/
theorem weightedRealRooted {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) (hA : ∀ r c, 0 ≤ A r c) :
    (Rook.weightedRookPolynomial A).Splits :=
  Rook.weightedRookPolynomial_splits A hA

/-- The roots in Nijenhuis's signed (-X)^k normalization are nonnegative. -/
theorem signedRoots_nonnegative {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) (hA : ∀ r c, 0 ≤ A r c) :
    ∀ z ∈ (Rook.nijenhuisRookPolynomial A).roots, 0 ≤ z :=
  Rook.nijenhuisRookPolynomial_roots_nonneg A hA

/-- The ordinary rook polynomial of every finite rectangular board is
real-rooted. -/
theorem ordinaryRealRooted {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (B : Finset (Row × Column)) :
    (Rook.rookPolynomial B).Splits :=
  Rook.rookPolynomial_splits B

end Nijenhuis
end Challenges
end RealRooted
