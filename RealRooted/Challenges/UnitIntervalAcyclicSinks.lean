import RealRooted.UnitIntervalGraph.AcyclicSink

/-!
# Acyclic sink polynomials of natural unit interval graphs

<!-- realrooted-catalog
version = 1
section = "families"
slug = "unit-interval-acyclic-sinks"
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
name = "RealRooted.UnitIntervalGraph.acyclicSinkPolynomial_splits"
module = "RealRooted.UnitIntervalGraph.AcyclicSink"
label = "Acyclic sink polynomials of natural unit interval graphs are real-rooted"
headline = true
-->

<!-- realrooted-catalog-content -->
# Acyclic sink polynomials of natural unit interval graphs

A natural unit interval graph on the vertices $1, \dotsc, n$ is given by left
endpoints $\ell(1) \leq \dotsb \leq \ell(n)$ with $\ell(i) \leq i$: two vertices
$i < j$ are adjacent when $\ell(j) \leq i$. For such a graph $G$ and a real
parameter $q$, the ascent-refined acyclic sink polynomial is

$$S_G(t; q) = \sum_{O} q^{\operatorname{asc}(O)}\, t^{\operatorname{sink}(O)},$$

summed over the acyclic orientations $O$ of $G$. Here $\operatorname{sink}(O)$
counts the vertices with no outgoing edge, and $\operatorname{asc}(O)$ counts
the edges directed from a smaller to a larger vertex in the natural order.

**Theorem.** For every natural unit interval graph and every real $q \geq 0$,
the polynomial $S_G(t; q)$ is real-rooted.

The case $q = 1$ is the ordinary acyclic sink polynomial, which counts acyclic
orientations by sinks alone. The theorem includes $q = 0$, disconnected graphs
and the empty graph. The ascent statistic depends on the natural vertex order,
and the theorem is about that labelling; it is not claimed for other labellings.

The proof identifies $S_G(t + 1; q)$, after a positive normalization, with a
weighted independence polynomial of $G$ with nonnegative vertex weights. Natural
unit interval graphs are claw-free, so that polynomial is real-rooted by the
weighted form of the [Chudnovsky–Seymour theorem](/RealRooted/theorems/chudnovsky-seymour/).

Natural unit interval graphs are chordal, and the natural order is a reverse
perfect elimination order. At $q = 1$ the theorem is therefore a special case
of the result for
[chordal claw-free graphs](/RealRooted/families/chordal-claw-free-acyclic-sinks/),
which also covers line graphs of trees; see also the
[minima polynomial](/RealRooted/families/minima-polynomial/) page.

## References

P. Alexandersson and L. Saud Maia Leite, unpublished manuscript (2026).

The orientation theorem was formalized in RealRooted issue #639. For the
claw-free background, see the
[Chudnovsky–Seymour](/RealRooted/theorems/chudnovsky-seymour/) and
[Leake–Ryder](/RealRooted/theorems/leake-ryder/) pages.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.UnitIntervalGraph.AcyclicSink`.
-/
