module

public import RealRooted.RookPolynomial

/-!
# Nijenhuis's weighted rook-polynomial theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "nijenhuis-rook-polynomials"
formalized = "2026-09-26"
references = [
  "Nijenhuis1976",
]
authors = ["Nijenhuis"]
years = [1976]

[[definitions]]
name = "RealRooted.Rook.IsRookPlacement"
module = "RealRooted.RookPolynomial"
label = "Rook placement"

[[definitions]]
name = "RealRooted.Rook.weightedRookPolynomial"
module = "RealRooted.RookPolynomial"
label = "Weighted rook polynomial"

[[definitions]]
name = "RealRooted.Rook.nijenhuisRookPolynomial"
module = "RealRooted.RookPolynomial"
label = "Nijenhuis's signed rook polynomial"

[[definitions]]
name = "RealRooted.Rook.rookPolynomial"
module = "RealRooted.RookPolynomial"
label = "Rook polynomial of a finite board"

[[theorems]]
name = "RealRooted.Rook.weightedRookPolynomial_eq_weightedMatchingPolynomialByEdges"
module = "RealRooted.RookPolynomial"
label = "Rook polynomials are bipartite matching polynomials"

[[theorems]]
name = "RealRooted.Rook.weightedRookPolynomial_splits"
module = "RealRooted.RookPolynomial"
label = "Weighted rook polynomials are real-rooted"

[[theorems]]
name = "RealRooted.Rook.nijenhuisRookPolynomial_roots_nonneg"
module = "RealRooted.RookPolynomial"
label = "The signed rook polynomial has nonnegative roots"

[[theorems]]
name = "RealRooted.Rook.rookPolynomial_splits"
module = "RealRooted.RookPolynomial"
label = "Rook polynomials of boards are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.Rook.weightedRookPolynomial_isPFPolynomial"
module = "RealRooted.RookPolynomial"
label = "Nonnegative weighted rook polynomials are PF"

[[theorems]]
name = "RealRooted.Rook.rookPolynomial_isPFPolynomial"
module = "RealRooted.RookPolynomial"
label = "Rook polynomials of finite boards are PF"
-->

<!-- realrooted-catalog-content -->
# Rook polynomials

A *rook placement* in an $m\times n$ array is a set of cells, no two of which
share a row or a column. For a matrix $A=(a_{rc})$ with nonnegative entries,
the *weighted rook polynomial* is
$$
\sum_P \prod_{(r,c)\in P} a_{rc}\,x^{|P|},
$$
summed over rook placements $P$. For a board $B$, that is, a set of cells, the
ordinary rook polynomial $\sum_k r_k(B)x^k$ is the case of the $0/1$ indicator
matrix of $B$.

Weighted rook polynomials are weighted matching polynomials of complete
bipartite graphs. For every nonnegative finite matrix they are PF polynomials,
so they are real-rooted with nonpositive roots. In particular, every rook
polynomial of a finite board is PF and real-rooted. Nijenhuis's signed
normalization $p(-x)$ has nonnegative roots.

## References

See [@Nijenhuis1976] and the
[rook-polynomial overview on symmetricfunctions.com](sf:rookPolynomials).
<!-- /realrooted-catalog-content -->

This challenge entry uses ordinary nonattacking rook placements. It is
separate from the project's non-nesting rook-polynomial model.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted
namespace Challenges
namespace Nijenhuis

universe u v

/-- Weighted rook placements are exactly weighted matchings in the complete
bipartite row-column graph. -/
theorem bipartiteMatchingIdentity {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column]
    (A : Row → Column → ℝ) :
    Rook.weightedRookPolynomial A =
      Graph.weightedMatchingPolynomialByEdges
        (_root_.completeBipartiteGraph Row Column)
        (Rook.matrixEdgeWeight A) :=
  Rook.weightedRookPolynomial_eq_weightedMatchingPolynomialByEdges A

/-- Nijenhuis's theorem: a nonnegative finite rectangular matrix has a
real-rooted weighted rook polynomial. -/
theorem weightedRealRooted {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column]
    (A : Row → Column → ℝ) (hA : ∀ r c, 0 ≤ A r c) :
    (Rook.weightedRookPolynomial A).Splits :=
  Rook.weightedRookPolynomial_splits A hA

/-- The roots in Nijenhuis's signed (-X)^k normalization are nonnegative. -/
theorem signedRoots_nonnegative {Row : Type u} {Column : Type v}
    [Fintype Row] [Fintype Column]
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
