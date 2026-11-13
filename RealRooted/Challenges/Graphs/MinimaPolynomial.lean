module

import RealRooted.Graph.MinimaForest

/-!
# Minima polynomial of local edge orders

<!-- realrooted-catalog
version = 1
section = "families"
slug = "minima-polynomial"
formalized = "2026-10-02"
references = []
tags = ["coauthored-paper"]
authors = ["Alexandersson", "Leite"]
years = [2026]

[[definitions]]
name = "RealRooted.Graph.LocalOrder"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "Local order"

[[definitions]]
name = "RealRooted.Graph.LocalOrder.mutualMinima"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "Mutual minima"

[[definitions]]
name = "RealRooted.Graph.minimaPolynomial"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "Minima polynomial"

[[definitions]]
name = "RealRooted.Graph.minimaPolynomialShiftedModel"
module = "RealRooted.Graph.MinimaPolynomial"
label = "The weighted matching model"

[[theorems]]
name = "RealRooted.Graph.minimaPolynomial_comp_X_add_one"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "The shifted minima polynomial as a weighted matching polynomial"

[[theorems]]
objects = ["Minima polynomials of local edge orders"]
name = "RealRooted.Graph.minimaPolynomial_splits"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "Minima polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.Graph.minimaPolynomial_eq_ordinaryAcyclicSinkPolynomial_lineGraph"
module = "RealRooted.Graph.MinimaForest"
label = "Forests: the minima polynomial is the acyclic sink polynomial of the line graph"

[[theorems]]
objects = ["Acyclic sink polynomials of line graphs of forests"]
name = "RealRooted.Graph.ordinaryAcyclicSinkPolynomial_lineGraph_splits"
module = "RealRooted.Graph.MinimaForest"
label = "Line graphs of forests have real-rooted acyclic sink polynomials"
-->

<!-- realrooted-catalog-content -->
# Minima polynomial of local edge orders

The number of local edge orders of a finite graph, counted by mutual minima, is a real-rooted
polynomial.

## Results

A *local order* of a finite graph $G$ chooses, at every vertex $v$, a linear order of the
$\deg v$ edges at $v$. An edge is a *mutual minimum* if it comes first at both endpoints. The
minima polynomial is
$$
M_G(t)=\sum_{L}t^{\operatorname{mm}(L)},
$$
summed over the $\prod_v\deg v!$ local orders $L$, where $\operatorname{mm}(L)$ is the number of
mutual minima.

**Identity.** For every finite graph $G$,
$$
M_G(t+1)=\prod_v\deg v!\ \sum_{S}\ \prod_{uv\in S}\frac{1}{\deg u\,\deg v}\,t^{|S|},
$$
summed over the matchings $S$ of $G$.

**Theorem.** For every finite graph $G$, $M_G(t)$ is real-rooted.

**Theorem (forests).** If $F$ is a finite forest, then $M_F(t)$ is the acyclic sink polynomial
of the line graph $L(F)$. In particular that polynomial is real-rooted.

## Use

For sinks of acyclic orientations see [chordal claw-free
graphs](rr:chordal-claw-free-acyclic-sinks) and [all orientations of
claw-free graphs](rr:claw-free-orientation-sinks).

## Proof

The mutual minima of a local order form a matching. For a matching $S$, a fraction
$\prod_{uv\in S}1/(\deg u\deg v)$ of the local orders has every edge of $S$ first at both of
its endpoints. Summing over the subsets of the mutual minima gives the identity. The right-hand
side is a matching polynomial with positive edge weights, hence real-rooted by the
[Heilmann--Lieb theorem](rr:heilmann-lieb); equivalently, a weighted
independence polynomial of the claw-free line graph $L(G)$ (see the
[Chudnovsky--Seymour](rr:chudnovsky-seymour) and
[Leake--Ryder](rr:leake-ryder) pages).

For a forest, the edges at a vertex form a clique of $L(F)$, so local orders are the
orientations of $L(F)$ that are acyclic on these cliques, and every cycle of $L(F)$ lies in such
a clique. Hence local orders are exactly the acyclic orientations of $L(F)$, and the mutual
minima are the sinks.

## References

P. Alexandersson and L. Saud Maia Leite, manuscript (2026).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Graph.MinimaPolynomial`, `RealRooted.Graph.MinimaLocalOrder` and
`RealRooted.Graph.MinimaForest`.
-/
