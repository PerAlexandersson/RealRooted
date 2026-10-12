import RealRooted.BorceaBranden.Applications.CoordinatePFMultiplier
import RealRooted.BorceaBranden.FiniteOrderWeylPreserver
import RealRooted.BorceaBranden.Applications.PoissonStability
import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol
import RealRooted.BorceaBranden.FiniteSymbolClassification
import RealRooted.BorceaBranden.UnivariateFiniteSymbol

/-!
# Borcea--Branden finite-symbol classification challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "borcea-branden"
formalized = "2026-08-09"
authors = ["Borcea", "Brändén"]
years = [2009]

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesComplexStabilityOnDegreeBox"
module = "RealRooted.BorceaBranden.FiniteSymbolClassification"
label = "Stability preserver on a degree box"

[[definitions]]
name = "RealRooted.BorceaBranden.HasStableRankOneRepresentation"
module = "RealRooted.BorceaBranden.FiniteSymbolClassification"
label = "Rank-one operator with stable image"

[[definitions]]
name = "RealRooted.BorceaBranden.finiteAlgebraicSymbol"
module = "RealRooted.BorceaBranden.UnivariateFiniteSymbol"
label = "Algebraic symbol of an operator"

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesRealRootedUpTo"
module = "RealRooted.BorceaBranden.UnivariateFiniteSymbol"
label = "Real-rootedness preserver up to degree d"

[[theorems]]
name = "RealRooted.BorceaBranden.finiteComplexSymbolClassification"
module = "RealRooted.BorceaBranden.FiniteSymbolClassification"
label = "Classification of stability preservers on a degree box"

[[theorems]]
name = "RealRooted.BorceaBranden.finiteSymbol_preservesRealRootedUpTo"
module = "RealRooted.BorceaBranden.Applications.RealUnivariateSymbol"
label = "Finite-symbol theorem: a stable symbol gives a real-rootedness preserver"

[[theorems]]
name = "RealRooted.BorceaBranden.coordinateDiagonalOperator_preserves_stability"
module = "RealRooted.BorceaBranden.Applications.CoordinatePFMultiplier"
label = "Coordinate PF multipliers preserve multivariate stability"

[[theorems]]
name = "RealRooted.BorceaBranden.finiteOrderWeylOperator_preserves_stability"
module = "RealRooted.BorceaBranden.FiniteOrderWeylPreserver"
label = "A stable signed Weyl symbol gives a stability preserver of any degree"

[[theorems]]
name = "RealRooted.Poisson.star_assoc"
module = "RealRooted.BorceaBranden.Applications.PoissonStar"
label = "The Poisson star product is associative"

[[theorems]]
name = "RealRooted.Poisson.spectatorAction_stable"
module = "RealRooted.BorceaBranden.Applications.PoissonStability"
label = "Poisson left multiplication preserves real stability"
-->

<!-- realrooted-catalog-content -->
# Borcea–Brändén finite-symbol theorems

A linear operator on a finite multidegree box preserves stability precisely in
the rank-one or stable-symbol cases. The real univariate theorem gives the
corresponding positive-symbol criterion for bounded-degree polynomials.

Applied in one coordinate, the finite-symbol theorem tensorizes multiplier sequences. Let
$\gamma$ act diagonally on the exponent of one variable $x_q$. If the Jensen polynomial
$\sum_{k \le d} \binom{d}{k} \gamma(k) t^k$ is a PF polynomial, then this operator maps every
stable polynomial of degree at most $d$ in $x_q$ to a stable polynomial or to zero. The other
variables are unrestricted. In particular, every PF multiplier sequence, and every falling
factorial $k \mapsto n^{\underline{k}}$, acts stably in a single coordinate.

Combining the falling-factorial multiplier with the finite-symbol theorem on each degree box
gives the finite-order Weyl-symbol theorem: if $T = \sum_{j \le m} Q_j(x) \partial_q^j$ has a
stable signed symbol $\sum_j Q_j(x) (-w)^j$, then $T$ maps every stable polynomial, of any
degree, to a stable polynomial or to zero.

One application is the Poisson star product
$f \star g = \sum_{a,b} f_{a,b} z^a v^b (1 + \partial_v)^{a+b} g$. It is associative, and left
multiplication by a nonzero real stable $f(z, v)$ with nonnegative coefficients preserves real
stability of any right input, spectator variables included. The signed Weyl symbol of this
operator is $f(z(1-w), v(1-w))$.

## References

J. Borcea and P. Brändén, “The Lee–Yang and Pólya–Schur programs. I. Linear
operators preserving stability,” *Inventiones Mathematicae* 177 (2009),
541–569.  See the
[finite-symbol discussion on symmetricfunctions.com](https://www.symmetricfunctions.com/stablePolynomials.htm#borceaBrandenFiniteSymbol).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/stablePolynomials.htm#borceaBrandenFiniteSymbol

Original reference: J. Borcea and P. Branden, "The Lee-Yang and Polya-Schur
programs. I. Linear operators preserving stability", Invent. Math. 177 (2009),
541--569.

The proofs use the reusable complex and real-univariate theorem modules.
-/

namespace RealRooted
namespace Challenges
namespace BorceaBranden

export RealRooted.BorceaBranden
  (PreservesComplexStabilityOnDegreeBox
    shiftedBoxPolynomial
    shiftedBoxPolynomial_eq_prod
    mvUpperHalfPlaneStable_shiftedBoxPolynomial
    HasShiftedBoxPerturbations
    IsUniformlyDominatedByShiftedBox
    hasShiftedBoxPerturbations_of_uniformlyDominated
    uniformlyDominatedByShiftedBox
    hasShiftedBoxPerturbations
    specializeRight_algebraicSymbol
    eval_algebraicSymbol_eq_eval_shiftedBoxPolynomial
    algebraicSymbol_stable_of_preserves_of_shiftedBox_ne_zero
    HasStableRankOneRepresentation
    hasStableRankOneRepresentation_of_range_stableOrZero
    hasStableRankOneRepresentation_of_preserves_of_shiftedBox_eq_zero
    rankOne_or_algebraicSymbol_stable_of_preserves_of_perturbations
    rankOne_or_algebraicSymbol_stable_of_preserves_of_robust_perturbations
    rankOne_or_algebraicSymbol_stable_of_preserves
    HasStableRankOneRepresentation.preservesComplexStabilityOnDegreeBox
    finiteComplexSymbolClassification
    finiteComplexSymbolIff
    polynomialInFirstMv
    finiteAlgebraicSymbol
    PreservesRealRootedUpTo
    finiteSymbolTheorem
    finiteSymbol_preservesRealRootedUpTo)

end BorceaBranden
end Challenges
end RealRooted
