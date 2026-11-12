module

import RealRooted.Graph.AllOrientationSinkIdentity

/-!
# Sink polynomials of all orientations of claw-free graphs

<!-- realrooted-catalog
version = 1
section = "families"
slug = "claw-free-orientation-sinks"
formalized = "2026-09-12"
references = []
tags = ["coauthored-paper"]
authors = ["Alexandersson", "Leite"]
years = [2026]

[[definitions]]
name = "RealRooted.Graph.allOrientationSinkPolynomial"
module = "RealRooted.Graph.AllOrientationSink"
label = "Sink polynomial over all orientations"

[[definitions]]
name = "RealRooted.Graph.allOrientationSinkPolynomialShiftedModel"
module = "RealRooted.Graph.AllOrientationSink"
label = "The shifted model: 2^{|E|} times a weighted independence polynomial"

[[theorems]]
name = "RealRooted.Graph.allOrientationSinkPolynomial_comp_X_add_one"
module = "RealRooted.Graph.AllOrientationSinkIdentity"
label = "The shifted sink polynomial as a weighted independence polynomial"

[[theorems]]
name = "RealRooted.Graph.allOrientationSinkPolynomial_splits_of_clawFree"
module = "RealRooted.Graph.AllOrientationSinkIdentity"
label = "Claw-free graphs have real-rooted sink polynomials"
headline = true
-->

<!-- realrooted-catalog-content -->
# Sink polynomials of all orientations of claw-free graphs

The sink polynomial summed over all orientations of a claw-free graph is real-rooted.

## Results

For a finite graph $G$, the sink polynomial is
$$
S_G(t)=\sum_{O}t^{\operatorname{sink}(O)},
$$
summed over all $2^{|E(G)|}$ orientations $O$ of $G$, where $\operatorname{sink}(O)$ is the
number of vertices with no outgoing edge; isolated vertices are sinks.

**Identity.** For every finite graph $G$,
$$
S_G(t+1)=2^{|E(G)|}\sum_{S}\ \prod_{v\in S}2^{-\deg v}\,t^{|S|},
$$
summed over the independent sets $S$ of $G$.

**Theorem.** If $G$ is a finite claw-free graph, then $S_G(t)$ is real-rooted.

## Proof

Expand $(t+1)^{\operatorname{sink}(O)}$ over the subsets of sinks. The orientations in which
every vertex of $S$ is a sink exist only if $S$ is independent, and then there are
$2^{|E(G)|-\sum_{v\in S}\deg v}$ of them. This gives the identity. Its right-hand side is a
weighted independence polynomial with positive weights, hence real-rooted for claw-free $G$ by
the weighted form of the [Chudnovsky--Seymour theorem](/RealRooted/theorems/chudnovsky-seymour/).

## Use

For acyclic orientations see [natural unit interval
graphs](/RealRooted/families/unit-interval-acyclic-sinks/) and [chordal claw-free
graphs](/RealRooted/families/chordal-claw-free-acyclic-sinks/).

## References

P. Alexandersson and L. Saud Maia Leite, manuscript (2026). Background on claw-free graphs is
on the [Chudnovsky--Seymour](/RealRooted/theorems/chudnovsky-seymour/) and
[Leake--Ryder](/RealRooted/theorems/leake-ryder/) pages, and on
[symmetricfunctions.com](sf:clawFreeGraph).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Graph.AllOrientationSink` and `RealRooted.Graph.AllOrientationSinkIdentity`.
-/
