module

import RealRooted.UnitIntervalGraph.AcyclicSink

/-!
# Acyclic sink polynomials of natural unit interval graphs

<!-- realrooted-catalog
version = 1
section = "families"
slug = "unit-interval-acyclic-sinks"
formalized = "2026-09-12"
references = []
tags = ["coauthored-paper"]
authors = ["Alexandersson", "Leite"]
years = [2026]

[[definitions]]
name = "RealRooted.UnitIntervalGraph.Data"
module = "RealRooted.UnitIntervalGraph.AcyclicSink"
label = "Left-endpoint data of a natural unit interval graph"

[[definitions]]
name = "RealRooted.UnitIntervalGraph.Data.graph"
module = "RealRooted.UnitIntervalGraph.AcyclicSink"
label = "The natural unit interval graph"

[[definitions]]
name = "RealRooted.Graph.acyclicSinkPolynomial"
module = "RealRooted.Graph.AcyclicOrientation"
label = "Ascent-refined acyclic sink polynomial"

[[definitions]]
name = "RealRooted.UnitIntervalGraph.acyclicSinkClosedForm"
module = "RealRooted.UnitIntervalGraph.AcyclicSink"
label = "Shifted weighted independence polynomial"

[[theorems]]
name = "RealRooted.UnitIntervalGraph.acyclicSinkPolynomial_eq_closedForm"
module = "RealRooted.UnitIntervalGraph.AcyclicSink"
label = "The sink polynomial as a shifted weighted independence polynomial"

[[theorems]]
objects = ["Acyclic sink polynomials of natural unit interval graphs"]
name = "RealRooted.UnitIntervalGraph.acyclicSinkPolynomial_splits"
module = "RealRooted.UnitIntervalGraph.AcyclicSink"
label = "Acyclic sink polynomials of natural unit interval graphs are real-rooted"
headline = true
-->

<!-- realrooted-catalog-content -->
# Acyclic sink polynomials of natural unit interval graphs

The acyclic sink polynomial of a natural unit interval graph, refined by ascents, is
real-rooted.

## Results

A natural unit interval graph on the vertices $0,\dots,n-1$ is given by left endpoints
$\ell(0)\le\dots\le\ell(n-1)$ with $\ell(i)\le i$: two vertices $i<j$ are adjacent when
$\ell(j)\le i$. For such a graph $G$ and a real number $q$, the ascent-refined acyclic sink
polynomial is
$$
S_G(t;q)=\sum_{O}q^{\operatorname{asc}(O)}\,t^{\operatorname{sink}(O)},
$$
summed over the acyclic orientations $O$ of $G$. Here $\operatorname{sink}(O)$ is the number of
vertices with no outgoing edge and $\operatorname{asc}(O)$ is the number of edges directed from
a smaller to a larger vertex.

**Theorem.** For every natural unit interval graph $G$ and every real $q\ge0$, the polynomial
$S_G(t;q)$ is real-rooted.

## Use

The statistic $\operatorname{asc}$ depends on the natural vertex order. At $q=1$ we obtain the
ordinary acyclic sink polynomial. There the theorem is a special case of the result for
[chordal claw-free graphs](rr:chordal-claw-free-acyclic-sinks), since the
natural order is a reverse perfect elimination order and natural unit interval graphs are
claw-free. See also the [minima polynomial](rr:minima-polynomial) page.

## Proof

After a positive normalization, $S_G(t+1;q)$ is a weighted independence polynomial of $G$ with
nonnegative vertex weights. It is real-rooted by the weighted form of the
[Chudnovsky--Seymour theorem](rr:chudnovsky-seymour).

## References

P. Alexandersson and L. Saud Maia Leite, unpublished manuscript (2026). Background on claw-free
graphs is on the [Chudnovsky--Seymour](rr:chudnovsky-seymour) and
[Leake--Ryder](rr:leake-ryder) pages.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.UnitIntervalGraph.AcyclicSink`.
-/
