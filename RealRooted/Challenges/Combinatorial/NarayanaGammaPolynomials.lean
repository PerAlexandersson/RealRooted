module

import RealRooted.NarayanaTransformation.ContinuousNarayanaGamma
import RealRooted.NarayanaTransformation.ReflectedNarayanaGamma

/-!
# Gamma polynomials of the continuous Narayana interpolation

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "continuous-narayana-gamma"
formalized = "2026-11-01"
tags = []
references = [
  "Zeng2026x",
  "MaoWang2026x",
]
authors = ["Mao", "Wang", "Zeng"]
years = [2026]

[[definitions]]
name = "RealRooted.continuousNarayanaGamma"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "The γ-polynomial of the continuous Narayana interpolation"

[[theorems]]
name = "RealRooted.gammaTransform_continuousNarayanaGamma"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "The interpolation is the γ-transform of the γ-polynomial"

[[theorems]]
name = "RealRooted.continuousNarayanaGamma_splits"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "The γ-polynomials are real-rooted for θ > -1"

[[theorems]]
name = "RealRooted.continuousNarayanaGamma_hasSimpleRoots"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "The γ-polynomials have simple roots"

[[theorems]]
name = "RealRooted.strictInterl_continuousNarayanaGamma_succ"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "Consecutive γ-polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.continuousNarayanaGamma_deriv_rec"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "A first-order differential recurrence for the γ-polynomials"

[[theorems]]
name = "RealRooted.continuousNarayanaGamma_pure_rec"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "A three-term recurrence for the γ-polynomials"

[[theorems]]
name = "RealRooted.strictInterl_narayanaInterpolation_succ"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "Consecutive continuous Narayana interpolations interlace"

[[theorems]]
name = "RealRooted.narayanaInterpolation_hasSimpleRoots"
module = "RealRooted.NarayanaTransformation.ContinuousNarayanaGamma"
label = "The continuous Narayana interpolation has simple roots"

[[theorems]]
name = "RealRooted.reflectedNarayanaGamma_interlaces"
module = "RealRooted.NarayanaTransformation.ReflectedNarayanaGamma"
label = "The reflected γ-polynomials, monic of degree n, interlace"

[[theorems]]
name = "RealRooted.rootMultiplicity_zero_reflectedNarayanaGamma"
module = "RealRooted.NarayanaTransformation.ReflectedNarayanaGamma"
label = "The reflected γ-polynomial has the root zero with multiplicity ⌈n/2⌉"
-->

<!-- realrooted-catalog-content -->
# Gamma polynomials of the continuous Narayana interpolation

The $\gamma$-polynomials of the continuous Narayana interpolation are real-rooted with simple
negative zeros, and consecutive ones interlace; the same holds for the interpolation itself.

## Results

For real $\theta>-1$ the continuous Narayana interpolation is
$$
P_n^{(\theta)}(t)=\sum_{k\le n}\binom nk\frac{(\theta+1)_n}{(\theta+1)_k(\theta+1)_{n-k}}\,t^k,
$$
with $(a)_k=a(a+1)\dotsm(a+k-1)$; see the [Narayana polynomials](rr:narayana) page. The
$\gamma$-polynomial is
$$
\gamma_n^{(\theta)}(t)=\sum_{j\le n/2}\frac{n!}{j!\,(n-2j)!\,(\theta+1)_j}\,t^j,
$$
and $P_n^{(\theta)}(t)=\sum_{j\le n/2}[t^j]\gamma_n^{(\theta)}\cdot t^j(1+t)^{n-2j}$.

**Theorem (roots and interlacing).** For $\theta>-1$ and $n\ge0$, $\gamma_n^{(\theta)}$ has
constant term $1$, nonnegative coefficients, degree $\lfloor n/2\rfloor$, and only simple real
zeros. Moreover $\gamma_n^{(\theta)}\ll\gamma_{n+1}^{(\theta)}$ without common zeros, and the same
holds for $P_n^{(\theta)}$ and $P_{n+1}^{(\theta)}$. The polynomial $P_n^{(\theta)}$ has only
simple zeros.

**Theorem (recurrences).** For $\theta>-1$ and $n\ge0$,
$$
(n+2\theta+1)\gamma_{n+1}=(n+2\theta+1+4nt)\gamma_n+2t(1-4t)\gamma_n',
$$
$$
(n+2\theta+2)\gamma_{n+2}=(2n+2\theta+3)\gamma_{n+1}-(n+1)(1-4t)\gamma_n .
$$

**Theorem (reflected family).** For $\theta>-1$ let $R_n=t^{n}\gamma_n^{(\theta)}(1/t)$. Then
$R_n$ is monic of degree $n$ with nonnegative coefficients and real zeros, the zero $0$ has
multiplicity $\lceil n/2\rceil$, its other zeros are simple and negative, and
$R_n\ll R_{n+1}$.

## References

[@Zeng2026x; @MaoWang2026x]. The normalization follows [@MaoWang2026x].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.NarayanaTransformation.ContinuousNarayanaGamma` and
`RealRooted.NarayanaTransformation.ReflectedNarayanaGamma`.
-/
