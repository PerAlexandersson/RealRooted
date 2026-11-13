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

[[theorems]]
name = "RealRooted.PathSquareEdge.polynomial_splits"
module = "RealRooted.Graph.IndependencePolynomial.PathSquareMatching"
label = "The weighted matching polynomials of path squares are real-rooted"

[[theorems]]
objects = ["Matching polynomials of path squares"]
property = "interlacing"
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
label = "Deleting a simplicial clique interlaces the weighted independence polynomial"

[[theorems]]
name = "RealRooted.Graph.matchingPolynomial_strictInterl_deleteVertex"
module = "RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion"
label = "Deleting a vertex: the weighted matching polynomial of G - v interlaces that of G"
-->

<!-- realrooted-catalog-content -->
# Weighted matchings of the square of a path and simplicial-clique deletion

Deleting a simplicial clique from a claw-free graph gives an interlacing weighted independence
polynomial. For line graphs this is vertex deletion for weighted matching polynomials, and for
the square of a path it makes consecutive weighted matching polynomials interlace.

## Results

The square of the infinite path has vertex set $\mathbb N$ and edges $\{i,i+1\}$ (*short*) and
$\{i,i+2\}$ (*long*). Give each short edge weight $u$ and each long edge weight $v$. Let
$P_n(x)=P_n^{(u,v)}(x)$ be the weighted matching-generating polynomial of the path square on
the vertices $0,\dots,n-1$. Then $P_0=P_1=1$, $P_2=1+ux$, $P_3=1+(2u+v)x$ and
$$
P_{n+4}=P_{n+3}+u\,x\,P_{n+2}+v\,x\,P_{n+1}+v^2x^2P_n,
$$
and this recurrence with these initial rows determines the family.

**Theorem (path squares).** If $u,v\ge0$, then every $P_n$ has constant term $1$, nonnegative
coefficients and only real negative roots, and $P_n\ll P_{n+1}$ for all $n$. If $u>0$, then
$\deg P_n=\lfloor n/2\rfloor$.

**Theorem (simplicial-clique deletion).** Let $G$ be a finite claw-free graph with weights
$w(v)\ge0$, let $S$ be a vertex set, and let $K\subseteq S$ be a clique such that, for each
$v\in K$, the neighbors of $v$ in $S\setminus K$ form a clique. Then the weighted independence
polynomial of $G[S\setminus K]$ interlaces that of $G[S]$.

**Corollary (vertex deletion).** Let $G$ be a finite graph with edge weights $w(e)\ge0$ and let
$v$ be a vertex. The weighted matching-generating polynomial of $G-v$ interlaces that of $G$.

## Proof

The weighted matching-generating polynomial of $G$ is the weighted independence polynomial of
the claw-free line graph $L(G)$. The edges at a vertex $v$ form a clique of $L(G)$ whose
outside neighbors form a clique, so the clique deletion theorem gives the corollary. For path
squares, delete the edges at the last vertex.

## References

The clique deletion theorem refines the induction in [@ChudnovskySeymour2007]; see the
[Chudnovsky--Seymour page](rr:chudnovsky-seymour).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Graph.IndependencePolynomial.PathSquareMatching` and
`RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion`.
-/
