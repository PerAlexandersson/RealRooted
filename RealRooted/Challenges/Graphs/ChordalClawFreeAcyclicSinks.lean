module

import RealRooted.Graph.ChordalAcyclicSink

/-!
# Acyclic sink polynomials of chordal claw-free graphs

<!-- realrooted-catalog
version = 1
section = "families"
slug = "chordal-claw-free-acyclic-sinks"
formalized = "2026-09-13"
references = []
tags = ["coauthored-paper"]
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

[[theorems]]
name = """RealRooted.Graph.ReversePerfectEliminationOrder.ordinaryAcyclicSinkPolynomial_splits_of_\
clawFree"""
module = "RealRooted.Graph.ChordalAcyclicSink"
label = "Chordal claw-free graphs have real-rooted acyclic sink polynomials"
headline = true

[[theorems]]
name = "RealRooted.Graph.acyclicSinkPolynomial_one_eq_ordinary"
module = "RealRooted.Graph.ChordalAcyclicSink"
label = "At q = 1 the ascent-refined sink polynomial is the ordinary one"
-->

<!-- realrooted-catalog-content -->
# Acyclic sink polynomials of chordal claw-free graphs

A claw-free graph with a reverse perfect elimination order has a real-rooted acyclic sink
polynomial.

## Results

For a finite graph $G$, the acyclic sink polynomial is
$$
S_G(t)=\sum_{O}t^{\operatorname{sink}(O)},
$$
summed over the acyclic orientations $O$ of $G$, where $\operatorname{sink}(O)$ is the number of
vertices with no outgoing edge. A *reverse perfect elimination order* is a linear order of the
vertices in which the earlier neighbors of every vertex form a clique. A graph has such an order
exactly when it is [chordal](sf:chordalGraph).

**Theorem.** If a finite claw-free graph $G$ has a reverse perfect elimination order, then
$S_G(t)$ is real-rooted.

The ascent-refined polynomial $S_G(t;q)$ of [acyclic sinks of natural unit interval
graphs](rr:unit-interval-acyclic-sinks) depends on a vertex labelling, and
$S_G(t;1)=S_G(t)$.

## Use

Line graphs of forests are chordal and claw-free. For them $S_{L(F)}$ is the
[minima polynomial](rr:minima-polynomial) of the forest $F$.

## Proof

Insert the vertices along the order. Since the earlier neighbors of each vertex form a clique,
$S_G(t+1)$ is a positive multiple of a weighted independence polynomial of $G$ with nonnegative
weights. This is real-rooted for claw-free $G$ by the weighted form of the
[Chudnovsky--Seymour theorem](rr:chudnovsky-seymour).

## References

P. Alexandersson and L. Saud Maia Leite, unpublished manuscript (2026). Background on claw-free
graphs is on the [Chudnovsky--Seymour](rr:chudnovsky-seymour) and
[Leake--Ryder](rr:leake-ryder) pages.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Graph.ChordalAcyclicSink`.
-/
