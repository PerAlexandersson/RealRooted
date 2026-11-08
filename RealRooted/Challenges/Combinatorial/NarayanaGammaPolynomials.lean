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
headline = true

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

For real $\theta>-1$ the continuous Narayana interpolation is
$P_n^{(\theta)}(t)=\sum_{k\le n}\binom nk\frac{(\theta+1)_n}{(\theta+1)_k(\theta+1)_{n-k}}\,t^k$
(see the [Narayana polynomials](/RealRooted/families/narayana/) page), interpolating between
the type B Narayana polynomials at $\theta=0$ and the shifted type A Narayana polynomials at
$\theta=1$ [@Zeng2026x]; the normalization follows [@MaoWang2026x].

**The $\gamma$-polynomials.** Let $\gamma_n^{(\theta)}(t)=\sum_{j\le
n/2}\frac{n!}{j!\,(n-2j)!\,(\theta+1)_j}\,t^j$,
so that $P_n^{(\theta)}$ is the $\gamma$-transform of $\gamma_n^{(\theta)}$. For $\theta>-1$ the
polynomial $\gamma_n^{(\theta)}$ has constant term $1$, positive coefficients, degree $\lfloor
n/2\rfloor$,
and only real, simple, negative roots, and consecutive $\gamma$-polynomials interlace and share
no root. They satisfy the first-order recurrence
$$
(n+2\theta+1)\gamma_{n+1}=(n+2\theta+1+4nt)\gamma_n+2t(1-4t)\gamma_n'
$$
and a three-term recurrence
$$
(n+2\theta+2)\gamma_{n+2}=(2n+2\theta+3)\gamma_{n+1}-(n+1)(1-4t)\gamma_n .
$$
Consequently the interpolations $P_n^{(\theta)}$ themselves have simple roots, and
consecutive $P_n^{(\theta)}$ and $P_{n+1}^{(\theta)}$ interlace without common roots. The
reflected polynomials $t^{\,n-\lfloor n/2\rfloor}\gamma_n^{(\theta)}(1/t)$ are monic of degree $n$,
real-rooted with
nonnegative coefficients, have the root zero with multiplicity $\lceil n/2\rceil$ and otherwise
simple negative roots, and consecutive ones interlace.

## References

See [@Zeng2026x] and [@MaoWang2026x].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.NarayanaTransformation.ContinuousNarayanaGamma` and
`RealRooted.NarayanaTransformation.ReflectedNarayanaGamma`.
-/
