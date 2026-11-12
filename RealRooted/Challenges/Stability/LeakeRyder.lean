module

import RealRooted.Graph.LeakeRyder
import RealRooted.Graph.MatchingPolynomial.Multivariate

/-!
# Leake--Ryder same-phase stability

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "leake-ryder"
formalized = "2026-09-06"
tags = []
references = [
  "LeakeRyder2019",
]
authors = ["Leake", "Ryder"]
years = [2019]

[[definitions]]
name = "RealRooted.SamePhaseStable"
module = "RealRooted.SamePhaseStability"
label = "Same-phase stability"

[[definitions]]
name = "RealRooted.Graph.multivariateIndepPoly"
module = "RealRooted.Graph.IndependencePolynomial.Multivariate"
label = "Multivariate independence polynomial"

[[definitions]]
name = "RealRooted.Graph.multivariateMatchingPolynomialByEdges"
module = "RealRooted.Graph.MatchingPolynomial.Multivariate"
label = "Edge-variable matching polynomial"

[[theorems]]
name = "RealRooted.Graph.multivariateIndepPoly_samePhaseStable_iff_clawFree"
module = "RealRooted.Graph.LeakeRyder"
label = "Leake–Ryder: same-phase stable if and only if claw-free"
headline = true

[[theorems]]
name = "RealRooted.Graph.ClawFree.indepPoly_splits_of_leakeRyder"
module = "RealRooted.Graph.LeakeRyder"
label = "Chudnovsky–Seymour via Leake–Ryder"

[[theorems]]
name = "RealRooted.Graph.clawFree_of_weightedIndepPoly_splits"
module = "RealRooted.Graph.LeakeRyder"
label = "Real-rooted weighted independence polynomials force claw-freeness"

[[theorems]]
name = "RealRooted.Graph.multivariateMatchingPolynomialByEdges_samePhaseStable"
module = "RealRooted.Graph.MatchingPolynomial.Multivariate"
label = "The matching polynomial is same-phase stable"
-->

<!-- realrooted-catalog-content -->
# Same-phase stability for graph polynomials

The multivariate independence polynomial of a finite graph is same-phase stable exactly when
the graph is claw-free.

## Results

A multivariate polynomial $P$ is *same-phase stable* if $P(w_1x,\dots,w_nx)$ is real-rooted in
$x$ for every choice of nonnegative weights $w_i$.

**Theorem (Leake–Ryder).** For a finite graph $G$, the multivariate independence polynomial
$\sum_S\prod_{v\in S}x_v$, summed over the independent sets $S$, is same-phase stable if and only
if $G$ is claw-free. In particular the independence polynomial of a claw-free graph is real-rooted
(the Chudnovsky–Seymour theorem, obtained by setting every variable equal to $x$).

**Theorem (weights).** If the weighted independence polynomial
$\sum_S\prod_{v\in S}w_v\,x^{|S|}$ is real-rooted for every choice of nonnegative vertex weights
$w$, then $G$ is claw-free. Weights $1$ on a claw and $0$ elsewhere give
$1+4x+3x^2+x^3$, which has non-real roots.

**Theorem (matchings).** The edge-variable matching polynomial
$\sum_M\prod_{e\in M}x_e$, summed over the matchings $M$ of $G$, is same-phase stable.

## References

The first theorem is due to Leake and Ryder [@LeakeRyder2019]. See also the discussion of
[same-phase stability](sf:samePhaseStabilityDefinition) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
