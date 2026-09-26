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
name = "RealRooted.Challenges.Nijenhuis.NonattackingRookPlacement"

[[definitions]]
name = "RealRooted.Challenges.Nijenhuis.WeightedRookPolynomial"

[[definitions]]
name = "RealRooted.Challenges.Nijenhuis.SignedRookPolynomial"

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

A rook placement is a finite set of matrix positions in which no two
positions share a row or a column. Its weight is the product of the
corresponding matrix entries. The weighted rook polynomial sums these
weights with one factor of X per rook.

Matrix positions are the edges of the complete bipartite graph on the row and
column types. The selected identity proves that nonattacking placements and
edge matchings give exactly the same weighted polynomial. Weighted
Heilmann–Lieb then proves Nijenhuis's theorem for every finite rectangular
matrix with nonnegative entries. In the positive-coefficient convention all
roots are nonpositive. Substituting -X, as in Nijenhuis's signed
normalization, gives nonnegative roots. Ordinary finite boards are the
zero-one specialization.

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

/-- A set of positions with no repeated row or column. -/
abbrev NonattackingRookPlacement {Row : Type u} {Column : Type v}
    (P : Finset (Row × Column)) : Prop :=
  Rook.IsRookPlacement P

/-- The weighted generating polynomial of nonattacking rook placements. -/
abbrev WeightedRookPolynomial {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) : ℝ[X] :=
  Rook.weightedRookPolynomial A

/-- Nijenhuis's signed normalization, obtained by substituting -X. -/
abbrev SignedRookPolynomial {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) : ℝ[X] :=
  Rook.nijenhuisRookPolynomial A

/-- Weighted rook placements are exactly weighted matchings in the complete
bipartite row-column graph. -/
theorem bipartiteMatchingIdentity {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) :
    WeightedRookPolynomial A =
      Graph.weightedMatchingPolynomialByEdges
        (_root_.completeBipartiteGraph Row Column)
        (Rook.matrixEdgeWeight A) :=
  Rook.weightedRookPolynomial_eq_weightedMatchingPolynomialByEdges A

/-- Nijenhuis's theorem: a nonnegative finite rectangular matrix has a
real-rooted weighted rook polynomial. -/
theorem weightedRealRooted {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) (hA : ∀ r c, 0 ≤ A r c) :
    (WeightedRookPolynomial A).Splits :=
  Rook.weightedRookPolynomial_splits A hA

/-- The roots in Nijenhuis's signed (-X)^k normalization are nonnegative. -/
theorem signedRoots_nonnegative {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column] [DecidableEq Row] [DecidableEq Column]
    (A : Row → Column → ℝ) (hA : ∀ r c, 0 ≤ A r c) :
    ∀ z ∈ (SignedRookPolynomial A).roots, 0 ≤ z :=
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
