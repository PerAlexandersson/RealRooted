module

public import RealRooted.EulerBidiagonal.Preservation
public import RealRooted.EulerOperator
public import RealRooted.EulerOperator.Polar.ProperPosition
public import RealRooted.OperatorPreservesInterlacing
public import RealRooted.PFPolynomial
public import RealRooted.PFPolynomial.PreserverClosure
public import RealRooted.ReciprocalShift.ProperPosition
public import RealRooted.Transforms.ReverseHermite.Preservation

/-!
# Operators preserving interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "operator-preservers"
formalized = "2026-10-05"
tags = []
references = [
  "Branden2004operators",
  "Branden2006",
]
authors = ["Brändén"]
years = [2004]

[[definitions]]
name = "RealRooted.PreservesRealRootedOrZero"
module = "RealRooted.OperatorPreservesInterlacing"
label = "Real-rootedness preserver"

[[definitions]]
name = "RealRooted.theta"
module = "RealRooted.EulerOperator"
label = "The Euler operator θ = x d/dx"

[[definitions]]
name = "RealRooted.polarTheta"
module = "RealRooted.EulerOperator"
label = "The polar Euler operator N − θ"

[[definitions]]
name = "RealRooted.reciprocalShift"
module = "RealRooted.PFPolynomial"
label = "The reciprocal x^D p(1/x)"

[[theorems]]
name = "RealRooted.PreservesRealRootedOrZero.interl_or_reverse"
module = "RealRooted.OperatorPreservesInterlacing"
label = "Real-rootedness preservers preserve interlacing"
headline = true
symcat = "operatorPreservesInterlacing"

[[theorems]]
name = "RealRooted.Interl.theta"
module = "RealRooted.EulerOperator"
label = "θ preserves interlacing"

[[theorems]]
name = "RealRooted.Interl.polarTheta"
module = "RealRooted.EulerOperator.Polar.ProperPosition"
label = "N − θ preserves interlacing of PF polynomials of degree at most N"

[[theorems]]
name = "RealRooted.StrictInterl.reciprocalShift"
module = "RealRooted.ReciprocalShift.ProperPosition"
label = "The reciprocal reverses interlacing of PF polynomials"

[[theorems]]
name = "RealRooted.IsPFPolynomial.reverseHermiteTransform"
module = "RealRooted.Transforms.ReverseHermite.Preservation"
label = "The reverse-Hermite transform preserves PF polynomials"

[[theorems]]
name = "RealRooted.Interl.reverseHermiteTransform"
module = "RealRooted.Transforms.ReverseHermite.Preservation"
label = "The reverse-Hermite transform preserves interlacing"

[[theorems]]
name = "RealRooted.isPFPolynomial_map_of_isNegativeSimple"
module = "RealRooted.PFPolynomial.PreserverClosure"
label = "Preserving simple negative-rooted inputs suffices for PF"

[[theorems]]
name = "RealRooted.isPFPolynomial_map_of_isNegativeSimple_of_natDegree_le"
module = "RealRooted.PFPolynomial.PreserverClosure"
label = "The degree-local version of the strict-to-weak transfer"

[[theorems]]
name = "RealRooted.IsPFPolynomial.eulerBidiagonal_step"
module = "RealRooted.EulerBidiagonal.Preservation"
label = "Euler bidiagonal steps preserve PF polynomials"
-->

<!-- realrooted-catalog-content -->
# Operators preserving interlacing

Every linear operator that maps nonzero real-rooted polynomials to zero or to real-rooted
polynomials preserves interlacing up to orientation; $\theta=x\,d/dx$, $N-\theta$ and the
reverse-Hermite transform preserve it exactly.

## Results

A polynomial is *PF* if it has nonnegative coefficients and is zero or has only real,
nonpositive roots. We use the [zero-aware interlacing convention](rr:about).

**Theorem (real-rootedness preservers).** Let $T$ be a real-linear operator on $\mathbb R[x]$
such that $Tp$ is zero or real-rooted for every nonzero real-rooted $p$. If $f\ll g$ in the
library's `StrictInterl` sense, which requires $f$ and $g$ to be nonzero and real-rooted,
then $Tf\ll Tg$ or $Tg\ll Tf$; the images may vanish.

**Theorem (concrete operators).**

- For all polynomials $p\ll q$, we have $\theta p\ll\theta q$.
- For PF polynomials $p\ll q$ of degree at most $N$, we have
  $(N-\theta)p\ll(N-\theta)q$, where $(N-\theta)p=Np-xp'$.
- For PF polynomials $p$, $q$ of degree at most $D$ with $p\ll q$ in the `StrictInterl`
  sense, the reciprocals $x^Dp(1/x)$ reverse the order:
  $x^Dq(1/x)\ll x^Dp(1/x)$, again in the `StrictInterl` sense.

**Theorem (reverse-Hermite transform).** Let $B_0=1$, $B_1=x$ and
$B_{n+2}=x\bigl(B_{n+1}+(n+1)B_n\bigr)$, and let $R$ be the linear map with $R(x^n)=B_n$.
Then $R$ maps PF polynomials to PF polynomials, and $p\ll q$ implies $Rp\ll Rq$ for PF
$p,q$.

**Theorem (from simple roots to PF).** Let $T$ be a real-linear operator, and suppose
$Tq$ is PF for every $q$ with positive leading coefficient and simple, negative roots.
Then $Tp$ is PF for every PF polynomial $p$. The degree-local version holds as well: if
this is assumed only for $q$ of degree at most $d$, then $Tp$ is PF for every PF
polynomial $p$ of degree at most $d$.

**Corollary (Euler bidiagonal step).** If $a,b\ge0$, $ab>0$ and $p$ is PF, then
$xp+(\theta+a)(\theta+b)p$ is PF.

## Proof

A PF polynomial $p$ of degree $d$ is the coefficientwise limit as $\varepsilon\to0^+$ of
$(1+\varepsilon D)^dp$, $D=d/dx$. These polynomials have positive leading coefficient and
simple negative roots and keep the degree, and the PF cone is closed under coefficientwise
limits of bounded degree.

## References

The finite-degree criterion is [@Branden2004operators, Thm. 8 in the arXiv version]. The
strict-to-weak transfer is [@Branden2006, Cor. 3.5]. See also the
[operator-preserver overview on symmetricfunctions.com](sf:operatorPreservesInterlacing).
<!-- /realrooted-catalog-content -->

Human statement:
sf:operatorPreservesInterlacing

Catalog reference: P. Brändén, J. Algebraic Combin. 20 (2004), 119–130,
arXiv:math/0303147; the site cites it as Theorem 9.

This module exposes the checked Obreschkoff-level theorem: a linear operator
that preserves real-rootedness up to zero preserves interlacing pairs up to the
orientation ambiguity of the current `StrictInterl` convention.
-/
