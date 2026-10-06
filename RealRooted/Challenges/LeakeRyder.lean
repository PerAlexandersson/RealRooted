import RealRooted.Graph.LeakeRyder
import RealRooted.Graph.MatchingPolynomial.Multivariate

/-!
# Leake--Ryder same-phase stability

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "leake-ryder"
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

A multivariate polynomial is same-phase stable when every nonnegative
one-dimensional specialization is real-rooted. Leake and Ryder proved that the
multivariate independence polynomial is same-phase stable exactly for
claw-free graphs. Their result also gives same-phase stability of the
edge-variable matching polynomial and recovers the Chudnovsky–Seymour theorem
by setting every variable equal to the same univariate variable.

Conversely, if the weighted independence polynomial
$\sum_{S} \prod_{v \in S} w_v\, x^{|S|}$, summed over the independent sets $S$,
is real-rooted for every choice of nonnegative vertex weights $w$, then the
graph is claw-free. Weights $1$ on a claw and $0$ elsewhere give
$1 + 4x + 3x^2 + x^3$, which has non-real roots.

## References

J. D. Leake and N. R. Ryder, “Generalizations of the matching polynomial to
the multivariate independence polynomial,” *Algebraic Combinatorics* 2 (2019),
781–802. See the discussion of
[same-phase stability][same-phase]
on symmetricfunctions.com.

[same-phase]: https://www.symmetricfunctions.com/stablePolynomials.htm#samePhaseStabilityDefinition
<!-- /realrooted-catalog-content -->
-/
