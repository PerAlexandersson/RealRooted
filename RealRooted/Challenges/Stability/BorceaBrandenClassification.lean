module

import RealRooted.BorceaBranden.Applications.CoordinatePFMultiplier
import RealRooted.BorceaBranden.Applications.PoissonStability
import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol
import RealRooted.BorceaBranden.FiniteOrderWeylPreserver
import RealRooted.BorceaBranden.FiniteSymbolClassification
import RealRooted.BorceaBranden.RealFiniteClassificationIff
import RealRooted.BorceaBranden.Transcendental.ComplexClassification
import RealRooted.BorceaBranden.Transcendental.PivotForward
import RealRooted.BorceaBranden.Transcendental.RealClassification
import RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne
import RealRooted.BorceaBranden.UnivariateFiniteSymbol

/-!
# Borcea–Brändén classification of stability preservers

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "borcea-branden-classification"
formalized = "2026-10-13"
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
name = "RealRooted.BorceaBranden.PreservesRealStabilityOnDegreeBox"
module = "RealRooted.BorceaBranden.RealFiniteClassification"
label = "Real stability preserver on a degree box"

[[definitions]]
name = "RealRooted.BorceaBranden.HasStableRankTwoRepresentation"
module = "RealRooted.BorceaBranden.RealFiniteClassification"
label = "Stable rank-at-most-two degree-box representation"

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesComplexStability"
module = "RealRooted.BorceaBranden.Transcendental.ComplexClassification"
label = "Complex stability preserver"

[[definitions]]
name = "RealRooted.BorceaBranden.HasGlobalStableRankOneRepresentation"
module = "RealRooted.BorceaBranden.Transcendental.ComplexClassification"
label = "Stable rank-at-most-one representation"

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesRealStability"
module = "RealRooted.BorceaBranden.Transcendental.RealOperatorBasics"
label = "Real stability preserver"

[[definitions]]
name = "RealRooted.BorceaBranden.HasGlobalStableRankTwoRepresentation"
module = "RealRooted.BorceaBranden.Transcendental.RealOperatorBasics"
label = "Stable rank-at-most-two representation"

[[definitions]]
name = "RealRooted.BorceaBranden.IsComplexStableLimit"
module = "RealRooted.BorceaBranden.Transcendental.TranscendentalSymbol"
label = "Complex stable-limit class"

[[definitions]]
name = "RealRooted.BorceaBranden.IsRealStableLimit"
module = "RealRooted.BorceaBranden.Transcendental.TranscendentalSymbol"
label = "Real stable-limit class"

[[definitions]]
name = "RealRooted.BorceaBranden.transcendentalSymbolPolynomial"
module = "RealRooted.BorceaBranden.Transcendental.TranscendentalSymbol"
label = "Complex transcendental-symbol coefficient family"

[[definitions]]
name = "RealRooted.BorceaBranden.realTranscendentalSymbolPolynomial"
module = "RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne"
label = "Real transcendental-symbol coefficient family"

[[definitions]]
name = "RealRooted.BorceaBranden.negRightFamily"
module = "RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne"
label = "Right-sign reversal of a coefficient family"

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
label = "Complex finite-degree classification (Theorem 1.1)"

[[theorems]]
name = "RealRooted.BorceaBranden.realStabilityOnDegreeBox_iff_rankTwo_or_stable_symbol"
module = "RealRooted.BorceaBranden.RealFiniteClassificationIff"
label = "Real finite-degree classification (Theorem 1.2)"
symcat = "borceaBrandenFiniteSymbol"

[[theorems]]
name = "RealRooted.BorceaBranden.complexStability_iff_rankOne_or_stableLimit_symbol"
module = "RealRooted.BorceaBranden.Transcendental.ComplexClassification"
label = "Complex classification (Theorem 1.3)"

[[theorems]]
name = "RealRooted.BorceaBranden.realStability_iff_rankTwo_or_stableLimit_signedSymbol"
module = "RealRooted.BorceaBranden.Transcendental.RealClassification"
label = "Real classification (Theorem 1.4)"
headline = true
symcat = "borceaBrandenTranscendentalSymbol"

[[theorems]]
name = "RealRooted.BorceaBranden.isComplexStableLimit_iff_fallingFactorial_glue_stable"
module = "RealRooted.BorceaBranden.Transcendental.PivotForward"
label = "Complex stable-limit criterion (Theorem 5.1)"

[[theorems]]
name = "RealRooted.BorceaBranden.isRealStableLimit_iff_forall_realGlue_stableOrZero"
module = "RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne"
label = "Real stable-limit criterion (Theorem 5.1)"

[[theorems]]
name = "RealRooted.BorceaBranden.PreservesRealRootedUpTo.of_finiteSymbol"
module = "RealRooted.BorceaBranden.Applications.RealUnivariateSymbol"
label = "A real stable symbol T((x + y)^d) gives a real-rootedness preserver up to degree d"

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
# Borcea–Brändén classification of stability preservers

A linear operator on polynomials in finitely many variables preserves stability if and only if
it has rank at most one (two, in the real case) with a stable range, or its symbol is stable or
a limit of stable polynomials. Stable symbols give concrete preservers: univariate
real-rootedness preservers, coordinate multipliers and differential operators.

## Results

A polynomial in $z=(z_i)_{i\in\sigma}$, with $\sigma$ finite, is *stable* if it has no zero
with every $z_i$ in the open upper half-plane; *real stable* means stable with real
coefficients. An operator *preserves* (real) stability if it maps (real) stable polynomials to
(real) stable polynomials or to zero. For a linear operator $T$, the *algebraic symbol* on the
degree box $\kappa\in\mathbb N^\sigma$ is $T\bigl[\prod_i(z_i+w_i)^{\kappa_i}\bigr]$, and the
*transcendental symbol* is the series
$$
T\bigl[e^{-z\cdot w}\bigr]=\sum_\alpha(-1)^{|\alpha|}\,T(z^\alpha)\,\frac{w^\alpha}{\alpha!},
$$
with $T$ acting on $z$. Theorem numbers refer to [@BorceaBranden2009I].

**Theorem (Borcea–Brändén).** Let $T$ be a linear operator on polynomials in $z$.

1. *(Theorem 1.1)* A complex-linear $T$ on the polynomials of degree at most $\kappa_i$ in each
   $z_i$ preserves stability if and only if $Tf=\varphi(f)P$ for a linear functional $\varphi$ and
   a stable $P$, or its algebraic symbol is stable.
2. *(Theorem 1.2)* A real-linear $T$ on this degree box preserves real stability if and only if
   $Tf=\varphi(f)P+\psi(f)Q$, where every real linear combination of $P$ and $Q$ is real stable
   or zero, or one of $T\bigl[\prod_i(z_i+w_i)^{\kappa_i}\bigr]$ and
   $T\bigl[\prod_i(z_i-w_i)^{\kappa_i}\bigr]$ is real stable.
3. *(Theorem 1.3)* A complex-linear $T$ on all polynomials preserves stability if and only if
   it has the rank-one form above, or its transcendental symbol is a locally uniform limit of
   stable polynomials.
4. *(Theorem 1.4)* A real-linear $T$ on all polynomials preserves real stability if and only if
   it has the rank-two form above, or its transcendental symbol or the same series with $w$
   replaced by $-w$ is a locally uniform limit of real stable polynomials.

**Theorem 5.1.** A series $\sum_\alpha P_\alpha(z)\,w^\alpha$ is a locally uniform limit of
stable polynomials if and only if every truncation
$\sum_{\alpha\le\beta}\prod_i\binom{\beta_i}{\alpha_i}\alpha_i!\,P_\alpha(z)\,w^\alpha$ is
stable or zero. The same holds with real stable polynomials.

**Corollaries.**

- If $T$ is a real-linear operator on $\mathbb R[x]$ and $T\bigl[(x+y)^d\bigr]$ is real stable,
  then $T$ maps every real-rooted polynomial of degree at most $d$ to zero or to a real-rooted
  polynomial.
- If the Jensen polynomial $\sum_{k\le d}\binom dk\gamma(k)t^k$ has nonnegative coefficients
  and only real nonpositive roots, the multiplier
  $z_q^k\mapsto\gamma(k)z_q^k$ in one variable preserves stability of polynomials of degree at
  most $d$ in $z_q$ and of any degree in the other variables.
- If $Q_0,\dotsc,Q_m$ are polynomials and $\sum_jQ_j(z)(-w)^j$ is stable, then
  $\sum_jQ_j(z)\,\partial_q^j$ preserves stability in every degree.
- The Poisson star product $f\star g=\sum_{a,b}f_{a,b}\,z^av^b\,(1+\partial_v)^{a+b}g$ is
  associative, and if $f(z,v)$ is real stable with nonnegative coefficients, then $g\mapsto
  f\star g$ preserves real stability.

## Proof

The coordinate multipliers come from the finite-degree theorem in one variable, and the
differential operators from the falling-factorial multiplier together with the finite-degree
theorem on each degree box. Theorem 5.1 follows by induction on the number of variables in the
support and on its minimal total degree, using specialization and partial differentiation. This
replaces a step in the proof of [@BorceaBranden2009I, Theorem 5.6], which assumes that partial
differentiation lowers the largest degree among the minimal exponents of the support by one;
that fails for a general support.

## References

- [@BorceaBranden2009I]
<!-- /realrooted-catalog-content -->
-/
