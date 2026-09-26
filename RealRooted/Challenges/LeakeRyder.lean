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

[[definitions]]
name = "RealRooted.Graph.multivariateIndepPoly"
module = "RealRooted.Graph.IndependencePolynomial.Multivariate"

[[definitions]]
name = "RealRooted.Graph.multivariateMatchingPolynomialByEdges"
module = "RealRooted.Graph.MatchingPolynomial.Multivariate"

[[theorems]]
name = "RealRooted.Graph.multivariateIndepPoly_samePhaseStable_iff_clawFree"
module = "RealRooted.Graph.LeakeRyder"

[[theorems]]
name = "RealRooted.Graph.ClawFree.indepPoly_splits_of_leakeRyder"
module = "RealRooted.Graph.LeakeRyder"

[[theorems]]
name = "RealRooted.Graph.multivariateMatchingPolynomialByEdges_samePhaseStable"
module = "RealRooted.Graph.MatchingPolynomial.Multivariate"
-->

<!-- realrooted-catalog-content -->
# Same-phase stability for graph polynomials

A multivariate polynomial is same-phase stable when every nonnegative
one-dimensional specialization is real-rooted. Leake and Ryder proved that the
multivariate independence polynomial is same-phase stable exactly for
claw-free graphs. Their result also gives same-phase stability of the
edge-variable matching polynomial and recovers the Chudnovsky--Seymour theorem
by setting every variable equal to the same univariate variable.

## References

J. D. Leake and N. R. Ryder, “Generalizations of the matching polynomial to
the multivariate independence polynomial,” *Algebraic Combinatorics* 2 (2019),
781–802. See the discussion of
[same-phase stability](https://symmetricfunctions.com/stablePolynomials.htm#samePhaseStable)
on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
