module

import RealRooted.Graph.ClawFree
import RealRooted.Graph.IndependencePolynomial.Basic
import RealRooted.Graph.IndependencePolynomial.ClawFree
import RealRooted.Graph.IndependencePolynomial.Multivariate
import RealRooted.Graph.IndependencePolynomial.PathSquareMatching
import RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion
import RealRooted.Graph.LeakeRyder
import RealRooted.Graph.MatchingPolynomial.Multivariate
import RealRooted.SamePhaseStability

/-!
# Independence polynomials of claw-free graphs

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "chudnovsky-seymour"
formalized = "2026-07-09"
references = [
  "ChudnovskySeymour2007",
  {key = "Engstrom2007", at = "Thm. 2.5"},
  "LeakeRyder2019",
]
authors = ["Chudnovsky", "Seymour", "Engström", "Leake", "Ryder"]
years = [2007, 2019]

[[definitions]]
name = "RealRooted.Graph.ClawFree"
module = "RealRooted.Graph.ClawFree"
label = "Claw-free graph"

[[definitions]]
name = "RealRooted.Graph.indepPoly"
module = "RealRooted.Graph.IndependencePolynomial.Basic"
label = "Independence polynomial"

[[definitions]]
name = "RealRooted.SamePhaseStable"
module = "RealRooted.SamePhaseStability"
label = "Same-phase stability"

[[definitions]]
name = "RealRooted.Graph.multivariateIndepPoly"
module = "RealRooted.Graph.IndependencePolynomial.Multivariate"
label = "Multivariate independence polynomial"

[[theorems]]
objects = ["Independence polynomials of claw-free graphs"]
name = "RealRooted.Graph.clawFree_indepPoly_splits"
module = "RealRooted.Graph.IndependencePolynomial.ClawFree"
label = "Chudnovsky–Seymour: a claw-free graph has a real-rooted independence polynomial"
headline = true

[[theorems]]
objects = ["Weighted independence polynomials of claw-free graphs"]
name = "RealRooted.Graph.clawFree_weightedIndepPoly_splits"
module = "RealRooted.Graph.IndependencePolynomial.ClawFree"
label = "Engström: with nonnegative vertex weights it stays real-rooted"
symcat = "weightedIndependencePolynomial"

[[theorems]]
name = "RealRooted.Graph.multivariateIndepPoly_samePhaseStable_iff_clawFree"
module = "RealRooted.Graph.LeakeRyder"
label = "Leake–Ryder: same-phase stable if and only if claw-free"

[[theorems]]
name = "RealRooted.Graph.clawFree_of_weightedIndepPoly_splits"
module = "RealRooted.Graph.LeakeRyder"
label = "Real-rooted for all nonnegative vertex weights forces claw-freeness"

[[theorems]]
name = "RealRooted.Graph.multivariateMatchingPolynomialByEdges_samePhaseStable"
module = "RealRooted.Graph.MatchingPolynomial.Multivariate"
label = "The edge-variable matching polynomial is same-phase stable"

[[theorems]]
name = "RealRooted.Graph.strictInterl_weightedIndepPolyOn_sdiff_of_simplicialClique"
module = "RealRooted.Graph.IndependencePolynomial.SimplicialCliqueDeletion"
label = "Deleting a simplicial clique gives an interlacing weighted independence polynomial"
tags = ["realrooted-original"]

[[theorems]]
objects = ["Matching polynomials of path squares"]
property = "interlacing"
name = "RealRooted.PathSquareEdge.polynomial_strictInterl_succ"
module = "RealRooted.Graph.IndependencePolynomial.PathSquareMatching"
label = "Consecutive weighted matching polynomials of path squares interlace"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Independence polynomials of claw-free graphs

A graph is claw-free if no vertex has three pairwise non-adjacent neighbours. M. Chudnovsky and
P. Seymour proved that the independence polynomial of a claw-free graph is real-rooted. The
theorem contains the Heilmann–Lieb theorem, since line graphs are claw-free, and Leake and Ryder
showed that claw-freeness is exactly what makes it hold for all vertex weights.

## Results

Let $G$ be a finite graph and $w\colon V(G)\to[0,\infty)$. The weighted independence
polynomial is
$$
I(G,w;x)=\sum_A x^{|A|}\prod_{v\in A}w(v),
$$
summed over the independent sets $A$ of $G$; for $w=1$ it is the independence polynomial.

**Theorem (Chudnovsky–Seymour).** [@ChudnovskySeymour2007] If $G$ is claw-free, then its
independence polynomial is real-rooted.

**Theorem (Engström).** [@Engstrom2007, Thm. 2.5] If $G$ is claw-free and $w\ge0$, then
$I(G,w;x)$ is real-rooted.

A multivariate polynomial $P(x_1,\dots,x_n)$ is *same-phase stable* if $P(w_1x,\dots,w_nx)$ is
real-rooted in $x$ for all $w_1,\dots,w_n\ge0$.

**Theorem (Leake–Ryder).** [@LeakeRyder2019] The multivariate independence polynomial
$\sum_A\prod_{v\in A}x_v$ of $G$ is same-phase stable if and only if $G$ is claw-free.
Equivalently, $I(G,w;x)$ is real-rooted for all $w\ge0$ only if $G$ is claw-free; on a claw
with unit weights it is $1+4x+3x^2+x^3$, which has non-real roots. The edge-variable matching
polynomial $\sum_M\prod_{e\in M}x_e$ of every finite graph is same-phase stable.

**Theorem (simplicial-clique deletion).** Let $G$ be claw-free, $w\ge0$, $S\subseteq V(G)$, and
let $K\subseteq S$ be a clique such that for each $v\in K$ the neighbours of $v$ in
$S\setminus K$ form a clique. Then $I(G[S\setminus K],w;x)$ interlaces $I(G[S],w;x)$.

**Corollary (path squares).** Give the edges $\{i,i+1\}$ and $\{i,i+2\}$ of the square of a path
weights $u,v\ge0$, and let $P_n$ be the weighted matching polynomial on the vertices
$0,\dots,n-1$. Then every $P_n$ has only real negative roots and $P_n\ll P_{n+1}$.

## Use

The matchings of a graph are the independent sets of its line graph, so the theorem gives the
[Heilmann–Lieb theorem](rr:heilmann-lieb). Many polynomials become weighted independence
polynomials of claw-free graphs after a shift, for example the
[sink polynomials of graph orientations](rr:graph-sink-polynomials).

## Proof

Chudnovsky and Seymour show by induction on the vertex set that the independence polynomials of
the induced subgraphs of a claw-free graph have common interleavers; the same induction works
with weights. Simplicial-clique deletion refines their induction step. For path squares, the
edges at the last vertex form such a clique in the line graph.

## References

[@ChudnovskySeymour2007]; [@Engstrom2007, Thm. 2.5]; [@LeakeRyder2019]. Background on
[claw-free graphs](sf:clawFreeGraph) and
[same-phase stability](sf:samePhaseStabilityDefinition) is on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
