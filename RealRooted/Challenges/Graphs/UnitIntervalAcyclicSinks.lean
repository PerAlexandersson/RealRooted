module

import RealRooted.Graph.AcyclicOrientation
import RealRooted.Graph.AllOrientationSink
import RealRooted.Graph.AllOrientationSinkIdentity
import RealRooted.Graph.ChordalAcyclicSink
import RealRooted.Graph.MinimaForest
import RealRooted.Graph.MinimaLocalOrder
import RealRooted.UnitIntervalGraph.AcyclicSink

/-!
# Sink polynomials of graph orientations

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "families"
slug = "graph-sink-polynomials"
formalized = "2026-09-13"
tags = ["coauthored-paper"]
references = [
  "AlexanderssonLeite2026x",
]
authors = ["Alexandersson", "Leite"]
years = [2026]

[[definitions]]
name = "RealRooted.Graph.ordinaryAcyclicSinkPolynomial"
module = "RealRooted.Graph.ChordalAcyclicSink"
label = "Acyclic sink polynomial"

[[definitions]]
name = "RealRooted.Graph.ReversePerfectEliminationOrder"
module = "RealRooted.Graph.ChordalAcyclicSink"
label = "Reverse perfect elimination order"

[[definitions]]
name = "RealRooted.Graph.acyclicSinkPolynomial"
module = "RealRooted.Graph.AcyclicOrientation"
label = "Ascent-refined acyclic sink polynomial"

[[definitions]]
name = "RealRooted.Graph.allOrientationSinkPolynomial"
module = "RealRooted.Graph.AllOrientationSink"
label = "Sink polynomial over all orientations"

[[definitions]]
name = "RealRooted.Graph.LocalOrder"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "Local order: a linear order of the edges at each vertex"

[[definitions]]
name = "RealRooted.Graph.minimaPolynomial"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "Minima polynomial"

[[theorems]]
objects = ["Acyclic sink polynomials of chordal claw-free graphs"]
name = """RealRooted.Graph.ReversePerfectEliminationOrder.ordinaryAcyclicSinkPolynomial_splits_of_\
clawFree"""
module = "RealRooted.Graph.ChordalAcyclicSink"
label = "Chordal claw-free graphs have real-rooted acyclic sink polynomials"
headline = true

[[theorems]]
objects = ["Acyclic sink polynomials of natural unit interval graphs"]
name = "RealRooted.UnitIntervalGraph.acyclicSinkPolynomial_splits"
module = "RealRooted.UnitIntervalGraph.AcyclicSink"
label = "Natural unit interval graphs: the ascent-refined sink polynomial is real-rooted"

[[theorems]]
name = "RealRooted.Graph.allOrientationSinkPolynomial_comp_X_add_one"
module = "RealRooted.Graph.AllOrientationSinkIdentity"
label = "The shifted sink polynomial is a weighted independence polynomial"

[[theorems]]
objects = ["Sink polynomials of all orientations of claw-free graphs"]
name = "RealRooted.Graph.allOrientationSinkPolynomial_splits_of_clawFree"
module = "RealRooted.Graph.AllOrientationSinkIdentity"
label = "Claw-free graphs: the sink polynomial over all orientations is real-rooted"

[[theorems]]
name = "RealRooted.Graph.minimaPolynomial_comp_X_add_one"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "The shifted minima polynomial is a weighted matching polynomial"

[[theorems]]
objects = ["Minima polynomials of local edge orders"]
name = "RealRooted.Graph.minimaPolynomial_splits"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "Minima polynomials of finite graphs are real-rooted"

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
# Sink polynomials of graph orientations

Counting the orientations of a graph by sinks gives a polynomial. P. Alexandersson and
L. Saud Maia Leite show that it is real-rooted for acyclic orientations of chordal claw-free
graphs and for all orientations of claw-free graphs. A related count of local edge orders by
mutual minima is real-rooted for every graph.

## Results

A *sink* of an orientation is a vertex with no outgoing edge. For a finite graph $G$ let
$$
S_G(t)=\sum_{O\text{ acyclic}}t^{\operatorname{sink}(O)},\qquad
\Sigma_G(t)=\sum_{O}t^{\operatorname{sink}(O)},
$$
summed over the acyclic orientations and over all $2^{|E(G)|}$ orientations of $G$. A *reverse
perfect elimination order* is a linear order of the vertices in which the earlier neighbours of
every vertex form a clique; a graph has one exactly when it is [chordal](sf:chordalGraph).

**Theorem (chordal claw-free graphs).** [@AlexanderssonLeite2026x, Thm. 3.1] If a finite claw-free
graph $G$ has a reverse perfect elimination order, then $S_G(t)$ is real-rooted.

**Theorem (natural unit interval graphs).** [@AlexanderssonLeite2026x, Thm. 5.2] Let $G$ be a
natural unit interval graph on $0,\dots,n-1$ and $q\ge0$. Then
$\sum_{O}q^{\operatorname{asc}(O)}t^{\operatorname{sink}(O)}$, summed over the acyclic orientations,
is real-rooted; $\operatorname{asc}(O)$ counts the edges directed from the smaller to the larger
vertex. At $q=1$ this is $S_G(t)$.

**Theorem (all orientations).** [@AlexanderssonLeite2026x, Prop. 4.1, Thm. 4.3] For every finite
graph $G$,
$$
\Sigma_G(t+1)=2^{|E(G)|}\sum_{A}\ \prod_{v\in A}2^{-\deg v}\,t^{|A|},
$$
summed over the independent sets $A$ of $G$. Hence $\Sigma_G$ is real-rooted if $G$ is
claw-free.

A *local order* of $G$ orders the edges at every vertex. An edge is a *mutual minimum* if it
comes first at both ends. Let $M_G(t)=\sum_Lt^{\operatorname{mm}(L)}$, summed over the
$\prod_v\deg v!$ local orders $L$, where $\operatorname{mm}(L)$ counts the mutual minima.

**Theorem (minima polynomial).** [@AlexanderssonLeite2026x, Thms. 3.8, 3.16] For every finite graph
$G$,
$$
M_G(t+1)=\prod_v\deg v!\ \sum_{S}\ \prod_{uv\in S}\frac1{\deg u\,\deg v}\,t^{|S|},
$$
summed over the matchings $S$ of $G$, so $M_G$ is real-rooted. If $G$ is a forest, then
$M_G=S_{L(G)}$ for its line graph $L(G)$.

## Use

These results turn questions about orientations into questions about independent sets: after the
shift $t\mapsto t+1$ each polynomial is a weighted independence polynomial of a claw-free graph,
or a weighted matching polynomial.

## Proof

Expanding $(t+1)^{\operatorname{sink}(O)}$ over sets of sinks gives the identities. For acyclic
orientations, insert the vertices along the elimination order: the earlier neighbours of each
vertex form a clique, so $S_G(t+1)$ is a positive multiple of a weighted independence polynomial
with nonnegative weights. All cases then follow from the weighted
[Chudnovsky–Seymour theorem](rr:chudnovsky-seymour), or from the
[Heilmann–Lieb theorem](rr:heilmann-lieb) for the minima polynomial. For a forest, the local
orders are exactly the acyclic orientations of $L(G)$, with mutual minima as sinks.

## References

[@AlexanderssonLeite2026x]. Background on
[claw-free graphs](sf:clawFreeGraph) is on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
