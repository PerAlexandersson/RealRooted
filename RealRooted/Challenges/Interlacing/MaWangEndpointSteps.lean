module

import RealRooted.MaWang.EndpointMultiplicity
import RealRooted.MaWang.EndpointTwoSided
import RealRooted.MaWang.EndpointClassification
import RealRooted.MaWang.GrowingZeroMultiplicity

/-!
# Ma–Wang endpoint steps and their multiplicities

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "ma-wang-endpoint-steps"
formalized = "2026-11-01"
tags = []
references = [
  "MaWang2008",
]
authors = ["Ma", "Wang"]
years = [2008]

[[definitions]]
name = "RealRooted.MaWang.endpointStep"
module = "RealRooted.MaWang.EndpointMultiplicity"
label = "The step p ↦ (aX + b) p + X (X + c) p'"

[[definitions]]
name = "RealRooted.MaWang.affineEndpointMultiplicity"
module = "RealRooted.MaWang.EndpointMultiplicity"
label = "The ceiling-division multiplicity at the endpoint"

[[definitions]]
name = "RealRooted.growingZeroStep"
module = "RealRooted.MaWang.GrowingZeroMultiplicity"
label = "The step f ↦ (a + bX) f + X (u - vX) f'"

[[theorems]]
name = "RealRooted.MaWang.endpointStep_rootMultiplicity"
module = "RealRooted.MaWang.EndpointMultiplicity"
label = "The multiplicity of the endpoint -c after one step"

[[theorems]]
name = "RealRooted.MaWang.endpointStep_roots_mem_Ico_iff"
module = "RealRooted.MaWang.EndpointMultiplicity"
label = "The roots stay in [-c, 0) exactly when b ≤ c (a + multiplicity of -c)"

[[theorems]]
name = "RealRooted.MaWang.endpointStep_strictInterl"
module = "RealRooted.MaWang.EndpointMultiplicity"
label = "The step interlaces its input"

[[theorems]]
name = "RealRooted.MaWang.affineEndpointSequence"
module = "RealRooted.MaWang.EndpointMultiplicity"
label = "Slope 1/L, intercept r/L: roots in [-c, 0), interlacing, multiplicity ⌈(n - r)/L⌉"

[[theorems]]
name = "RealRooted.MaWang.affineEndpointParameters_of_roots_mem_Ico"
module = "RealRooted.MaWang.EndpointClassification"
label = "Converse: confinement of all rows forces slope 1/L and intercept r/L"

[[theorems]]
name = "RealRooted.MaWang.affineEndpointSequence_roots_mem_Ico_iff"
module = "RealRooted.MaWang.EndpointClassification"
label = "Classification of the affine endpoint sequences with confined roots"
headline = true

[[theorems]]
name = "RealRooted.MaWang.halfSlopeEndpointSequence"
module = "RealRooted.MaWang.EndpointClassification"
label = "The slope-one-half case"

[[theorems]]
name = "RealRooted.affineEndpointStep_closed"
module = "RealRooted.MaWang.EndpointTwoSided"
label = "The closed two-endpoint step (aX + c) f + X (X + 1) f' on [-1, 0]"

[[theorems]]
name = "RealRooted.affineEndpointStep_roots_mem_Icc_iff"
module = "RealRooted.MaWang.EndpointTwoSided"
label = "Roots stay in [-1, 0] iff 0 ≤ c + m₀ and 0 ≤ a + m₋₁ - c"

[[theorems]]
name = "RealRooted.growingZeroStep_isPFPolynomial_iff"
module = "RealRooted.MaWang.GrowingZeroMultiplicity"
label = "The PF threshold depends on the multiplicity of the root zero: 0 ≤ a + u m₀"

[[theorems]]
name = "RealRooted.growingZeroFamily_pf_degree_multiplicity_interlacing"
module = "RealRooted.MaWang.GrowingZeroMultiplicity"
label = "The integer growing-zero family is PF and interlacing, with endpoint multiplicity at zero"

[[theorems]]
name = "RealRooted.growingZeroFamily_all_isPFPolynomial_iff"
module = "RealRooted.MaWang.GrowingZeroMultiplicity"
label = "All rows of the growing-zero family are PF exactly for integer parameters"
-->

<!-- realrooted-catalog-content -->
# Ma–Wang endpoint steps and their multiplicities

Ma and Wang [@MaWang2008, Theorem 2 and Corollary 3] study sequences of real-rooted
polynomials obtained by differential steps whose roots stay in a window. We
formalize the endpoint version.

## Confinement at the left endpoint

For $c,a,b\in\mathbb R$ let
$$
E_{c,a,b}(p)=(ax+b)\,p+x(x+c)\,p' .
$$
Let $a>0$ and let $p$ have positive leading coefficient, split, and have all roots in
$[-c,0)$. Then $E_{c,a,b}(p)$ has degree $\deg p+1$, positive leading coefficient, and
interlaces $p$. If $m$ is the multiplicity of $-c$ as a root of $p$, then the
multiplicity of $-c$ in $E_{c,a,b}(p)$ is $m+1$ when $b=c(a+m)$ and $m$ otherwise.
If $b>0$, the roots of $E_{c,a,b}(p)$ again lie in $[-c,0)$ if and only if
$$
b\le c\,(a+m).
$$

For iterated steps with slope $1/L$ and intercept $r/L$,
$P_{n+1}=\rho_nE_{c,a,\,c(a+n/L-r/L)}(P_n)$ with $\rho_n>0$, $a>r/L$ and a starting row
with roots in $(-c,0)$, every row is real-rooted with roots in $[-c,0)$, consecutive
rows interlace, and the multiplicity of $-c$ in $P_n$ is $\lceil(n-r)/L\rceil$ (the
number of thresholds $r+jL$ below $n$). Conversely, if every row of an affine sequence
with slope $\lambda>0$ and intercept $\mu\ge0$, $\mu<a$, has its roots in $[-c,0)$,
then $\lambda=1/L$ and $\mu=r/L$ for natural numbers $L>0$ and $r$. Together these
classify the affine endpoint sequences.

## Closed window

For $a>0$ and $c\in\mathbb R$ the step $(ax+c)f+x(x+1)f'$ maps a split polynomial with
positive leading coefficient and roots in $[-1,0]$ to a polynomial of one higher
degree that interlaces it. Its roots stay in $[-1,0]$ if and only if
$0\le c+m_0$ and $0\le a+m_{-1}-c$, where $m_0$ and $m_{-1}$ are the multiplicities
of $0$ and $-1$ in $f$, and the multiplicities at both endpoints are determined
explicitly.

## Growing zero multiplicity

For the step $f\mapsto(a+bx)f+x(u-vx)f'$ with $u,v\ge0$ on a nonzero PF polynomial
$f$ of degree $d$ with $vd<b$, the image has degree $d+1$, interlaces $f$, and is PF
if and only if
$$
0\le a+u\cdot\operatorname{mult}_0(f),
$$
so the threshold depends on the multiplicity of the root $0$ rather than on the
constant coefficient. Consider the family $P_0=1$ and
$$
P_{n+1}=\bigl((a-n)+(bn+c)x\bigr)P_n+r\,x(1-x)P_n' .
$$
For natural numbers $a=A$ and $r=R>0$, with $b\ge R$ and $c>0$, every row is PF of degree
$n$, consecutive rows interlace, and the multiplicity of the root $0$ of $P_n$ is the
endpoint multiplicity $\lceil(n-A)/R\rceil$. Conversely, with $0<r\le b$ and $c>0$, all
rows are PF if and only if $a$ and $r$ are natural numbers.

## References

See [@MaWang2008]. The closed-window step is an instance of the interval
differential steps in the basis-transform page on
[basis transforms preserving real-rootedness and
PF](/RealRooted/theorems/basis-transform-preservers/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.MaWang` modules
named in the metadata.
-/
