module

public import RealRooted.RookPolynomial

/-!
# Weighted rook polynomials are real-rooted (Nijenhuis)

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "nijenhuis-rook-polynomials"
formalized = "2026-09-26"
tags = []
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
headline = true

[[theorems]]
name = "RealRooted.Rook.nijenhuisRookPolynomial_roots_nonneg"
module = "RealRooted.RookPolynomial"
label = "The signed rook polynomial has nonnegative roots"

[[theorems]]
name = "RealRooted.Rook.rookPolynomial_splits"
module = "RealRooted.RookPolynomial"
label = "Rook polynomials of boards are real-rooted"

[[theorems]]
name = "RealRooted.Rook.weightedRookPolynomial_isPFPolynomial"
module = "RealRooted.RookPolynomial"
label = "Nonnegative weighted rook polynomials are Pólya frequency"

[[theorems]]
name = "RealRooted.Rook.rookPolynomial_isPFPolynomial"
module = "RealRooted.RookPolynomial"
label = "Rook polynomials of finite boards are Pólya frequency"
-->

<!-- realrooted-catalog-content -->
# Weighted rook polynomials are real-rooted (Nijenhuis)

Weighted rook polynomials of finite matrices with nonnegative entries are Pólya frequency
polynomials, hence real-rooted with nonpositive roots.

A *rook placement* in a finite array is a set of cells, no two of which share a row or a
column. For a matrix $A=(a_{rc})$, the *weighted rook polynomial* is
$$
\sum_P \prod_{(r,c)\in P} a_{rc}\,x^{|P|},
$$
summed over rook placements $P$, the empty placement included. For a board $B$, that is, a set
of cells, the ordinary rook polynomial $\sum_k r_k(B)x^k$ is the case of the $0/1$ indicator
matrix of $B$.

## Results

**Theorem (Nijenhuis).** Let $A$ be a finite matrix with nonnegative entries.

- The weighted rook polynomial of $A$ is a weighted matching polynomial of the complete
  bipartite graph on the rows and columns of $A$.
- It is a Pólya frequency polynomial, so it is real-rooted with nonpositive roots.
- In Nijenhuis's signed normalization $p(-x)$ the roots are nonnegative.

In particular, the rook polynomial of every finite board is a real-rooted Pólya frequency
polynomial.

## References

See [@Nijenhuis1976] and the
[rook-polynomial overview on symmetricfunctions.com](sf:rookPolynomials).
<!-- /realrooted-catalog-content -->

This challenge entry uses ordinary nonattacking rook placements. It is
separate from the project's non-nesting rook-polynomial model.
-/

noncomputable section
