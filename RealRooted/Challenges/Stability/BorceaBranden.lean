module

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
tags = []
references = [
  "BorceaBranden2009I",
]
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
headline = true

[[theorems]]
name = "RealRooted.BorceaBranden.PreservesRealRootedUpTo.of_finiteSymbol"
module = "RealRooted.BorceaBranden.Applications.RealUnivariateSymbol"
label = "Finite-symbol theorem: a stable symbol gives a real-rootedness preserver"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.coordinateDiagonalOperator"
module = "RealRooted.BorceaBranden.Applications.CoordinatePFMultiplier"
label = "Coordinate PF multipliers preserve multivariate stability"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.finiteOrderWeylOperator"
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

A linear operator on a finite multidegree box preserves stability if and only if it has a
stable rank-one representation or a stable symbol; stable symbols give univariate
real-rootedness preservers, coordinate multipliers and stable differential operators.

## Results

**Theorem (finite-symbol classification)** [@BorceaBranden2009I]. Let $\sigma$ be a finite set,
$\kappa\colon\sigma\to\mathbb N$, and let $T$ be a $\mathbb C$-linear map from the polynomials of
degree at most $\kappa_i$ in each variable $x_i$ to $\mathbb C[x_\sigma]$. Then $T$ maps stable
polynomials to stable polynomials or zero if and only if $T$ has a stable rank-one
representation, $Tf=\alpha(f)P$ for a linear functional $\alpha$ and a stable polynomial $P$, or its
algebraic symbol is stable. Here stable means no zero with all coordinates in the open upper
half-plane.

**Theorem (real univariate form).** Let $T$ be a real-linear operator on $\mathbb R[x]$ and
$d\ge0$. If the finite algebraic symbol $T((x+y)^d)$ is real stable, then $T$ maps every
real-rooted polynomial of degree at most $d$ to zero or to a real-rooted polynomial.

**Theorem (coordinate multipliers).** Let $\gamma\colon\mathbb N\to\mathbb R$ act on the exponent
of one variable $x_q$, that is $x_q^k\mapsto\gamma(k)x_q^k$. If the Jensen polynomial
$\sum_{k\le d}\binom dk\gamma(k)t^k$ is a Pólya frequency polynomial, then the operator maps
every stable polynomial of degree at most $d$ in $x_q$ to a stable polynomial or to zero. The
other variables are unrestricted.

**Theorem (finite-order differential operators).** Let
$T=\sum_{j\le m}Q_j(x)\,\partial_q^j$ with polynomial coefficients $Q_j$. If the signed symbol
$\sum_jQ_j(x)(-w)^j$ is stable, then $T$ maps every stable polynomial, of any degree, to a
stable polynomial or to zero.

**Theorem (Poisson star product).** Define
$$f\star g=\sum_{a,b}f_{a,b}\,z^av^b\,(1+\partial_v)^{a+b}g.$$
Over any commutative ring $\star$ is associative. If $f(z,v)$ is real stable with nonnegative
coefficients and $P$ is real stable in $z,v$ and further variables, then $f\star P$, with $f$
acting on $z,v$, is real stable. The signed symbol of $g\mapsto f\star g$ is $f(z(1-w),v(1-w))$.

## Use

The coordinate-multiplier theorem is the finite-symbol theorem applied in one coordinate. The
differential-operator theorem combines the falling-factorial multiplier with the finite-symbol
theorem on each degree box.

## References

The real classification, which is the [site's finite-symbol theorem](sf:borceaBrandenFiniteSymbol),
is on the [classification page](rr:borcea-branden-classification). See
[@BorceaBranden2009I].
<!-- /realrooted-catalog-content -->

Human statement:
sf:borceaBrandenFiniteSymbol

Original reference: J. Borcea and P. Branden, "The Lee-Yang and Polya-Schur
programs. I. Linear operators preserving stability", Invent. Math. 177 (2009),
541--569.

The proofs use the reusable complex and real-univariate theorem modules.
-/
