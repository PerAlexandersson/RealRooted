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

A differential step keeps all roots in a window exactly when a threshold on the multiplicity of
the endpoint root holds, and the affine step sequences with confined roots are classified.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
Ma and Wang [@MaWang2008, Theorem 2 and Corollary 3] study sequences of real-rooted
polynomials obtained by differential steps whose roots stay in a window. For $c,a,b\in\mathbb R$
let
$$
E_{c,a,b}(p)=(ax+b)\,p+x(x+c)\,p'.
$$

**Theorem (step at the left endpoint).** Let $a>0$, and let $p$ be real-rooted with positive
leading coefficient and all roots in $[-c,0)$. Then $E_{c,a,b}(p)$ has degree $\deg p+1$,
positive leading coefficient, and $p\ll E_{c,a,b}(p)$. Let $m$ be the multiplicity of $-c$ as a
root of $p$. The multiplicity of $-c$ in $E_{c,a,b}(p)$ is $m+1$ if $b=c(a+m)$ and $m$
otherwise. If also $b>0$, all roots of $E_{c,a,b}(p)$ lie in $[-c,0)$ if and only if
$$
b\le c\,(a+m).
$$

**Theorem (affine sequences).** Let $c>0$ and let $L\ge1$ and $r\ge0$ be integers with
$a>r/L$. Let $P_0$ be real-rooted with positive leading coefficient and roots in $(-c,0)$, and
$$
P_{n+1}=\rho_n\,E_{c,a,\,c(a+n/L-r/L)}(P_n)\qquad(\rho_n>0).
$$
Then every $P_n$ is real-rooted with positive leading coefficient and roots in $[-c,0)$,
$P_n\ll P_{n+1}$, and the multiplicity of $-c$ in $P_n$ is $\lceil\max(n-r,0)/L\rceil$. For
$L=2$ and $r=1$ this is $\lceil(n-1)/2\rceil$.

**Theorem (classification).** Let $c>0$, $\lambda>0$ and $0\le\mu<a$, let $P_0$ be as above, and
$P_{n+1}=\rho_n\,E_{c,a,\,c(a+\lambda n-\mu)}(P_n)$ with $\rho_n>0$. Then all rows have their
roots in $[-c,0)$ if and only if $\lambda=1/L$ and $\mu=r/L$ for integers $L\ge1$ and $r\ge0$.

**Theorem (closed window).** Let $a>0$, $c\in\mathbb R$, and let $f$ be real-rooted with positive
leading coefficient and roots in $[-1,0]$. Then $g=(ax+c)f+x(x+1)f'$ has degree $\deg f+1$,
positive leading coefficient, and $f\ll g$. Let $m_0$ and $m_{-1}$ be the multiplicities of $0$
and $-1$ in $f$. All roots of $g$ lie in $[-1,0]$ if and only if $0\le c+m_0$ and
$0\le a+m_{-1}-c$. The multiplicity of $0$ in $g$ is $m_0+1$ if $c+m_0=0$ and $m_0$ otherwise;
that of $-1$ is $m_{-1}+1$ if $c=a+m_{-1}$ and $m_{-1}$ otherwise.

**Theorem (growing zero multiplicity).** Let $u,v\ge0$ and let $f\ne0$ be a Pólya frequency
polynomial with $v\deg f<b$. Then $(a+bx)f+x(u-vx)f'$ has degree $\deg f+1$, interlaces $f$,
and is a Pólya frequency polynomial if and only if
$$
0\le a+u\cdot\operatorname{mult}_0(f).
$$
Consider $P_0=1$ and
$$
P_{n+1}=\bigl((a-n)+(bn+c)x\bigr)P_n+r\,x(1-x)P_n'.
$$
If $a=A$ and $r=R$ are natural numbers with $R>0$, and $b\ge R$ and $c>0$, then every $P_n$ is
a Pólya frequency polynomial of degree $n$, $P_n\ll P_{n+1}$, and the multiplicity of the root
$0$ of $P_n$ is $\lceil\max(n-A,0)/R\rceil$. Conversely, if $0<r\le b$ and $c>0$, all rows are
Pólya frequency polynomials if and only if $a$ and $r$ are natural numbers.

## References

[@MaWang2008]. The closed-window step is an instance of the interval differential steps on the
page on [basis transforms preserving real-rootedness and
PF](/RealRooted/theorems/basis-transform-preservers/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.MaWang` modules
named in the metadata.
-/
