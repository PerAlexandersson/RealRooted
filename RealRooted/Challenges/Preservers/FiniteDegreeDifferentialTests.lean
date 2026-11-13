module

import RealRooted.FiniteFreeAdditive.FiniteDegreeTests
import RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests
import RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions
import RealRooted.FiniteFreeAdditive.FiniteDegreeCompanionCone

/-!
# Finite-degree tests for constant-coefficient differential operators

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "finite-degree-differential-tests"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "The degree-N test h(D) X^N"

[[definitions]]
name = "RealRooted.PreservesOrderedPFUpTo"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "Two symbols give ordered PF images through degree N"

[[definitions]]
name = "RealRooted.HasKreinCompanionExpansion"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "A nonnegative combination of h and quotients h/(x − u)"

[[theorems]]
name = "RealRooted.PreservesPFUpTo.iff_finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "h(D) preserves PF polynomials of degree at most N exactly when h(D) X^N is PF"

[[theorems]]
name = "RealRooted.finiteFreeAdditiveConvolution_finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "The finite free additive convolution with the test is the differential operator"

[[theorems]]
name = "RealRooted.PreservesOrderedPFUpTo.iff_differentialTests"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "Ordered PF images through degree N are detected by the two degree-N tests"

[[theorems]]
name = "RealRooted.PreservesOrderedPFUpTo.iff_jensenDifferentialTests"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "The same criterion through the reversed (Jensen) tests"

[[theorems]]
name = "RealRooted.PreservesOrderedPFUpTo.binomialDifferentialSymbol"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "Binomial symbols with Jensen tests (sX + 1)^r, (sX + 1)^(r-1): ordered PF images"

[[theorems]]
name = "RealRooted.FiniteDegreeOrdered.binomialDifferentialRecurrence_pf_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "A binomial differential recurrence row is PF and preceded by the leading image"

[[theorems]]
name = "RealRooted.differentialRecurrence_pf_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "An ordered PF pair of images gives a PF row X h(D)p + a k(D)p preceded by h(D)p"

[[theorems]]
name = "RealRooted.multishiftDifferentialRecurrence_pf_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "Multishift recurrence rows are PF and preceded by the full-symbol image"

[[theorems]]
name = "RealRooted.multishiftDifferentialRecurrence_induction"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "Induction along a multishift recurrence from a PF seed"

[[theorems]]
name = "RealRooted.isPFPolynomial_and_interl_iff_hasKreinCompanionExpansion"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "For PF h ≠ 0: k is PF with k ≪ h iff k is a nonnegative sum of h and h/(x − u)"

[[theorems]]
name = "RealRooted.forall_differential_images_iff_isPFPolynomial_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanionCone"
label = "All-degree ordered PF preservation by (h, k) is equivalent to k being PF and k ≪ h"
headline = true
-->

<!-- realrooted-catalog-content -->
# Finite-degree tests for constant-coefficient differential operators

An operator $h(D)$ with $D=d/dx$ preserves PF polynomials of degree at most $N$ if and only if
the single polynomial $h(D)\,x^N$ is PF, and the same holds for pairs of operators with
interlacing images.

## Results

A polynomial is *PF* (Pólya frequency) if it is zero or has nonnegative coefficients and only
real, nonpositive roots. We use the [zero-aware interlacing convention](rr:about). For a real
polynomial $h=\sum_jh_jx^j$ let $h(D)=\sum_jh_jD^j$. The *degree-$N$
test* of $h$ and its reversal, the *Jensen test*, are
$$
T_N(h)=h(D)\,x^N=\sum_{j\le N}\frac{N!}{(N-j)!}\,h_j\,x^{N-j},\qquad
J_N(h)=\sum_{j\le N}\frac{N!}{(N-j)!}\,h_j\,x^{j}.
$$
For $\deg p\le N$, the finite free additive convolution of the test with $p$ is
$T_N(h)\boxplus_Np=h(D)p$.

**Theorem (scalar test).** $h(D)$ maps every PF polynomial of degree at most $N$ to a PF
polynomial if and only if $T_N(h)$ is PF.

**Theorem (ordered tests).** For real polynomials $h,k$ the following are equivalent.

1. For every PF polynomial $p$ of degree at most $N$, the polynomials $h(D)p$ and $k(D)p$ are
   PF and $h(D)p\ll k(D)p$.
2. $T_N(h)$ and $T_N(k)$ are PF and $T_N(h)\ll T_N(k)$.
3. $J_N(h)$ and $J_N(k)$ are PF and $J_N(k)\ll J_N(h)$.

**Theorem (binomial symbols).** Let $s\ge0$ and $1\le r\le N$. Let $h$ and $k$ be the symbols
with $J_N(h)=(sx+1)^r$ and $J_N(k)=(sx+1)^{r-1}$. Then (1) holds for $h,k$.

**Theorem (recurrence rows).** Let $p$ be PF with $\deg p\le N$ and let $a\ge0$.

- If $h(D)p$ and $k(D)p$ are PF with $h(D)p\ll k(D)p$, then
  $x\,h(D)p+a\,k(D)p$ is PF and $h(D)p\ll x\,h(D)p+a\,k(D)p$.
- For $h,k$ as in the binomial theorem, the same holds with these $h$ and $k$.
- Let $s_0,\dots,s_r\ge0$ with $r+1\le N$ and $a_0,\dots,a_r\ge0$. Let $h_s$ be the symbol with
  $J_N(h_s)=\prod_i(1+s_ix)$, and $h_{s\setminus i}$ the symbol with the factor $1+s_ix$
  removed. Then
  $$
  x\,h_s(D)p+\sum_ia_i\,h_{s\setminus i}(D)p
  $$
  is PF and is preceded by $h_s(D)p$.

**Theorem (iteration).** Let $P_m$ be PF with $\deg P_m\le m$. For $n\ge m$ let $r_n+1\le n$,
let $s^{(n)}_i,a^{(n)}_i\ge0$ for $0\le i\le r_n$, and let $P_{n+1}$ be the row of the previous
theorem for $p=P_n$, $N=n$, $s=s^{(n)}$ and $a=a^{(n)}$. Then $P_n$ is PF with $\deg P_n\le n$ for
all $n\ge m$.

**Theorem (companion cone).** Let $h\ne0$ be PF. Then $k$ is PF with $k\ll h$ if and only if
$k$ is a nonnegative combination of $h$ and of quotients $h/(x-u)$ with $h(u)=0$. Moreover, the
following are equivalent:

1. for every PF polynomial $p$, the polynomials $h(D)p$ and $k(D)p$ are PF and
   $h(D)p\ll k(D)p$;
2. $k$ is PF and $k\ll h$.

## References

The finite free additive convolution is treated on the
[finite free convolutions](rr:finite-free-convolutions) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.FiniteFreeAdditive`
modules named in the metadata.
-/
