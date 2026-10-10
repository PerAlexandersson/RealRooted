import RealRooted.Graph.MinimaForest

/-!
# The minima polynomial of local edge orders

<!-- realrooted-catalog
version = 1
section = "families"
slug = "minima-polynomial"
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
name = "RealRooted.Graph.minimaPolynomial_splits"
module = "RealRooted.Graph.MinimaLocalOrder"
label = "Minima polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.Graph.minimaPolynomial_eq_ordinaryAcyclicSinkPolynomial_lineGraph"
module = "RealRooted.Graph.MinimaForest"
label = "Forests: the minima polynomial is the acyclic sink polynomial of the line graph"

[[theorems]]
name = "RealRooted.Graph.ordinaryAcyclicSinkPolynomial_lineGraph_splits"
module = "RealRooted.Graph.MinimaForest"
label = "Line graphs of forests have real-rooted acyclic sink polynomials"
-->

<!-- realrooted-catalog-content -->
# The minima polynomial of local edge orders

A **local order** of a finite graph $G$ chooses, at every vertex $v$, a linear
order of the $\deg v$ edges at $v$. An edge is a **mutual minimum** if it comes
first at both of its endpoints. The minima polynomial is

$$M_G(t) = \sum_{L} t^{\operatorname{mm}(L)},$$

summed over the $\prod_v \deg v!$ local orders $L$, where $\operatorname{mm}(L)$
counts the mutual minima.

The edges at a vertex form a clique of the line graph $L(G)$, so local orders are
the orientations of $L(G)$ that are acyclic on each of these cliques, and the
mutual minima are their sinks.

**Identity.** The mutual minima of a local order form a matching. For a matching
$S$, every edge $uv \in S$ comes first at $u$ and at $v$ in exactly a
$\prod_{uv \in S} 1/(\deg u \deg v)$ fraction of the local orders. Hence
$$M_G(t + 1) = \prod_v \deg v! \sum_{S} \prod_{uv \in S} \frac{1}{\deg u \deg v}\, t^{|S|},$$
summed over the matchings $S$ of $G$.

**Theorem.** For every finite graph $G$, $M_G(t)$ is real-rooted.

The right-hand side of the identity is a matching polynomial with positive edge
weights, so it is real-rooted by the Heilmann–Lieb theorem. It is also a weighted
independence polynomial of the claw-free line graph $L(G)$; see the
[Chudnovsky–Seymour](/RealRooted/theorems/chudnovsky-seymour/) and
[Leake–Ryder](/RealRooted/theorems/leake-ryder/) pages.

**Forests.** If $F$ is a forest, every orientation of $L(F)$ that is acyclic on
the vertex cliques is acyclic, and every acyclic orientation of $L(F)$ arises
from exactly one local order. Hence $M_F(t)$ is the acyclic sink polynomial of
the line graph $L(F)$, and the acyclic sink polynomial of the line graph of a
forest is real-rooted.

For sinks of acyclic orientations, see the pages on
[chordal claw-free graphs](/RealRooted/families/chordal-claw-free-acyclic-sinks/) and
[all orientations of claw-free graphs](/RealRooted/families/claw-free-orientation-sinks/).

## References

P. Alexandersson and L. Saud Maia Leite, manuscript (2026).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Graph.MinimaPolynomial`, `RealRooted.Graph.MinimaLocalOrder` and
`RealRooted.Graph.MinimaForest`.
-/
