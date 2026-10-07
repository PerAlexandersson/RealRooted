import RealRooted.Graph.ChordalAcyclicSink

/-!
# Acyclic sink polynomials of chordal claw-free graphs

<!-- realrooted-catalog
version = 1
section = "families"
slug = "chordal-claw-free-acyclic-sinks"
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
name = """RealRooted.Graph.ReversePerfectEliminationOrder.\
ordinaryAcyclicSinkPolynomial_splits_of_clawFree"""
module = "RealRooted.Graph.ChordalAcyclicSink"
label = "Chordal claw-free graphs have real-rooted acyclic sink polynomials"
headline = true

[[theorems]]
name = "RealRooted.Graph.acyclicSinkPolynomial_one_eq_ordinary"
module = "RealRooted.Graph.ChordalAcyclicSink"
label = "The ascent-refined polynomial at q = 1"
-->

<!-- realrooted-catalog-content -->
# Acyclic sink polynomials of chordal claw-free graphs

For a finite graph $G$, the acyclic sink polynomial is

$$S_G(t) = \sum_{O} t^{\operatorname{sink}(O)},$$

summed over the acyclic orientations $O$ of $G$, where $\operatorname{sink}(O)$
counts the vertices with no outgoing edge. It does not depend on a labelling of
the vertices.

A **reverse perfect elimination order** is a linear order of the vertices in
which the earlier neighbors of every vertex form a clique. A finite graph has
such an order exactly when it is chordal; here the order is part of the
hypothesis.

**Theorem.** If a finite claw-free graph $G$ has a reverse perfect elimination
order, then $S_G(t)$ is real-rooted.

The proof inserts the vertices along the order. Since the earlier neighbors of
each vertex form a clique, the shifted polynomial $S_G(t + 1)$ is, up to a
positive factor, a weighted independence polynomial of $G$ with nonnegative
weights. For claw-free graphs that polynomial is real-rooted by the weighted form
of the [Chudnovsky–Seymour theorem](/RealRooted/theorems/chudnovsky-seymour/).

The theorem is about the ordinary sink polynomial only. The ascent-refined
version $S_G(t; q)$ depends on a vertex labelling; at $q = 1$ it equals $S_G(t)$.
For the refined polynomial of natural unit interval graphs, see
[acyclic sinks of natural unit interval graphs](/RealRooted/families/unit-interval-acyclic-sinks/).

Line graphs of forests are also chordal and claw-free. For them the library
proves real-rootedness by a separate route: the acyclic sink polynomial of
$L(F)$ is the [minima polynomial](/RealRooted/families/minima-polynomial/) of
the forest $F$.

## References

P. Alexandersson and L. Saud Maia Leite, unpublished manuscript (2026).

The theorem was formalized in RealRooted issue #677. For the claw-free
background, see the
[Chudnovsky–Seymour](/RealRooted/theorems/chudnovsky-seymour/) and
[Leake–Ryder](/RealRooted/theorems/leake-ryder/) pages.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Graph.ChordalAcyclicSink`.
-/
