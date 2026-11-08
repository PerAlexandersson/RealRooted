module

import RealRooted.Graph.IndependencePolynomial.PathSquareMatching
import RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion

/-!
# Weighted matchings of the square of a path and simplicial-clique deletion

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "path-square-matching"
formalized = "2026-11-01"
references = [
  "ChudnovskySeymour2007",
]
authors = ["Chudnovsky", "Seymour"]
years = [2007]
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.PathSquareEdge.polynomial"
module = "RealRooted.Graph.IndependencePolynomial.PathSquareMatching"
label = "The weighted matching polynomial of the square of a path"

[[definitions]]
name = "RealRooted.Graph.weightedMatchingGeneratingPolynomialDeleteVertex"
module = "RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion"
label = "The weighted matching polynomial after deleting a vertex"

[[theorems]]
name = "RealRooted.PathSquareEdge.polynomial_add_four"
module = "RealRooted.Graph.IndependencePolynomial.PathSquareMatching"
label = "A four-term recurrence for the matching polynomials of path squares"
headline = true

[[theorems]]
name = "RealRooted.PathSquareEdge.polynomial_splits"
module = "RealRooted.Graph.IndependencePolynomial.PathSquareMatching"
label = "The weighted matching polynomials of path squares are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.PathSquareEdge.polynomial_strictInterl_succ"
module = "RealRooted.Graph.IndependencePolynomial.PathSquareMatching"
label = "Consecutive matching polynomials of path squares interlace"
headline = true

[[theorems]]
name = "RealRooted.PathSquareEdge.isRoot_lt_zero"
module = "RealRooted.Graph.IndependencePolynomial.PathSquareMatching"
label = "All roots are negative"

[[theorems]]
name = "RealRooted.PathSquareEdge.polynomial_natDegree"
module = "RealRooted.Graph.IndependencePolynomial.PathSquareMatching"
label = "For u > 0 the n-th polynomial has degree ⌊n/2⌋"

[[theorems]]
name = "RealRooted.PathSquareEdge.eq_polynomial_of_satisfiesRecurrence"
module = "RealRooted.Graph.IndependencePolynomial.PathSquareMatching"
label = "The four-term recurrence with its initial rows characterizes the family"

[[theorems]]
name = "RealRooted.Graph.strictInterl_weightedIndepPolyOn_sdiff_of_simplicialClique"
module = "RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion"
label = "Deleting a simplicial clique of a claw-free graph interlaces weighted independence polys"
headline = true

[[theorems]]
name = "RealRooted.Graph.strictInterl_weightedMatchingGeneratingPolynomial_deleteVertex"
module = "RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion"
label = "Deleting a vertex gives directed proper position of weighted matching polynomials"
-->

<!-- realrooted-catalog-content -->
# Weighted matchings of the square of a path and simplicial-clique deletion

## Matchings of the square of a path

The square of the infinite path has the vertex set $\mathbb N$ with edges $\{i,i+1\}$
(*short*) and $\{i,i+2\}$ (*long*). Give each short edge weight $u$ and each long edge
weight $v$, and let $P_n(x)=P_n^{(u,v)}(x)$ be the weighted matching-generating polynomial
of the path square on any $n$ consecutive vertices: the weighted independence
polynomial of the conflict graph whose vertices are the edges, two being adjacent
when they share an endpoint. Then $P_0=P_1=1$, $P_2=1+ux$, $P_3=1+(2u+v)x$ and
$$
P_{n+4}=P_{n+3}+u\,x\,P_{n+2}+v\,x\,P_{n+1}+v^2x^2P_n ,
$$
and this recurrence with the initial rows determines the family.

**Theorem.** If $u,v\ge0$, then every $P_n$ has constant term $1$, nonnegative
coefficients, only real negative roots, and consecutive polynomials interlace. If
$u>0$, then $\deg P_n=\lfloor n/2\rfloor$.

## Deleting a simplicial clique

Let $G$ be claw-free with nonnegative vertex weights, let $S$ be a vertex set, and let
$K\subseteq S$ be a simplicial clique of $G$ restricted to $S$. Using the weighted
Chudnovsky–Seymour induction invariant [@ChudnovskySeymour2007], the weighted
independence polynomial of $S\setminus K$ interlaces that of $S$. The edges at a vertex
$v$ of a graph form a simplicial clique of its line graph, so deleting a vertex gives
directed proper position of weighted matching-generating polynomials: the polynomial of
$G-v$ interlaces that of $G$ for nonnegative edge weights.

## What is new

The path-square recurrence and the deletion consequences were developed in this
library; the underlying claw-free interlacing is from [@ChudnovskySeymour2007].

## References

See [@ChudnovskySeymour2007]. See also the [Chudnovsky–Seymour
page](/RealRooted/theorems/chudnovsky-seymour/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Graph.IndependencePolynomial.PathSquareMatching` and
`RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion`.
-/
