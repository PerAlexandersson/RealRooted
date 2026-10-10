import RealRooted.Graph.AllOrientationSinkIdentity

/-!
# Sink polynomials of all orientations of claw-free graphs

<!-- realrooted-catalog
version = 1
section = "families"
slug = "claw-free-orientation-sinks"
authors = ["Alexandersson", "Leite"]
years = [2026]

[[definitions]]
name = "RealRooted.Graph.allOrientationSinkPolynomial"
module = "RealRooted.Graph.AllOrientationSink"
label = "Sink polynomial over all orientations"

[[definitions]]
name = "RealRooted.Graph.allOrientationSinkPolynomialShiftedModel"
module = "RealRooted.Graph.AllOrientationSink"
label = "The weighted independence model"

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

For a finite graph $G$, sum over all $2^{|E(G)|}$ orientations:

$$S_G(t) = \sum_{O} t^{\operatorname{sink}(O)},$$

where $\operatorname{sink}(O)$ counts the vertices with no outgoing edge
(isolated vertices are sinks).

**Identity.** Expanding each sink indicator and counting forced and free edge
directions gives
$$S_G(t + 1) = 2^{|E(G)|} \sum_{S} \prod_{v \in S} 2^{-\deg v}\, t^{|S|},$$
summed over the independent sets $S$ of $G$: the orientations in which every
vertex of $S$ is a sink exist only when $S$ is independent, and then number
$2^{|E(G)| - \sum_{v \in S} \deg v}$.

**Theorem.** If $G$ is claw-free, then $S_G(t)$ is real-rooted.

The right-hand side of the identity is a weighted independence polynomial with
positive weights, which is real-rooted for claw-free graphs by the weighted form
of the [Chudnovsky–Seymour theorem](/RealRooted/theorems/chudnovsky-seymour/).
Line graphs are one claw-free subfamily.

For acyclic orientations, see the pages on
[natural unit interval graphs](/RealRooted/families/unit-interval-acyclic-sinks/) and
[chordal claw-free graphs](/RealRooted/families/chordal-claw-free-acyclic-sinks/).

## References

P. Alexandersson and L. Saud Maia Leite, manuscript (2026).

For the claw-free background, see the
[Chudnovsky–Seymour](/RealRooted/theorems/chudnovsky-seymour/) and
[Leake–Ryder](/RealRooted/theorems/leake-ryder/) pages.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Graph.AllOrientationSink` and `RealRooted.Graph.AllOrientationSinkIdentity`.
-/
