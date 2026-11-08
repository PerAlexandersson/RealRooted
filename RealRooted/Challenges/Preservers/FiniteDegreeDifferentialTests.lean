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
label = "A nonnegative expansion in one-root-deleted summands of the parent"

[[theorems]]
name = "RealRooted.preservesPFUpTo_iff_finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "h(D) preserves PF polynomials of degree at most N exactly when h(D) X^N is PF"
headline = true

[[theorems]]
name = "RealRooted.finiteFreeAdditiveConvolution_finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "The finite free additive convolution with the test is the differential operator"

[[theorems]]
name = "RealRooted.FiniteDegreeOrdered.preservesOrderedPFUpTo_iff_differentialTests"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "Ordered PF images through degree N are detected by the two degree-N tests"
headline = true

[[theorems]]
name = "RealRooted.FiniteDegreeOrdered.preservesOrderedPFUpTo_iff_jensenDifferentialTests"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "The same criterion through the reversed (Jensen) tests"

[[theorems]]
name = "RealRooted.FiniteDegreeOrdered.preservesOrderedPFUpTo_binomialDifferentialSymbol"
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
headline = true

[[theorems]]
name = "RealRooted.multishiftDifferentialRecurrence_induction"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "Induction along a multishift recurrence from a PF seed"

[[theorems]]
name = "RealRooted.isPFPolynomial_and_interl_iff_hasKreinCompanionExpansion"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "For a PF parent h, the pairs (k PF, k ≪ h) are exactly the Krein companion expansions"

[[theorems]]
name = "RealRooted.forall_differential_images_iff_isPFPolynomial_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanionCone"
label = "All-degree ordered PF preservation by (h, k) is equivalent to k being PF and k ≪ h"
headline = true
-->

<!-- realrooted-catalog-content -->
# Finite-degree tests for constant-coefficient differential operators

For a real polynomial $h=\sum_jh_jx^j$ let $h(D)=\sum_jh_jD^j$ with $D=d/dx$. The
degree-$N$ test of $h$ is the polynomial
$$
T_N(h)=h(D)\,x^N=\sum_{j\le N}N(N-1)\cdots(N-j+1)\,h_j\,x^{N-j}.
$$
For $\deg p\le N$ the finite free additive convolution of the test with $p$ is
$T_N(h)\boxplus_Np=h(D)p$.

## Scalar and ordered tests

**Theorem.** The operator $h(D)$ maps every PF polynomial of degree at most $N$ to a
PF polynomial if and only if $T_N(h)$ is a PF polynomial.

For two symbols $h,k$, the operators $h(D),k(D)$ give PF images with $h(D)p\ll k(D)p$
for every PF polynomial $p$ of degree at most $N$ if and only if $T_N(h)$ and $T_N(k)$ are
PF and $T_N(h)\ll T_N(k)$. Equivalently, in terms of the reversed (Jensen) tests with
coefficients $N(N-1)\cdots(N-j+1)h_j$ in degree $j$, the Jensen tests are PF and
interlace in the reverse order. For the binomial symbols with Jensen tests
$(sx+1)^r$ and $(sx+1)^{r-1}$, $s\ge0$, $1\le r\le N$, the ordered preservation holds.

As a consequence, whenever $h(D)p$ and $k(D)p$ are PF with $h(D)p\ll k(D)p$ and
$a\ge0$, the row
$$
x\,h(D)p+a\,k(D)p
$$
is PF and is preceded by $h(D)p$. The same holds for the binomial symbols of degree
$r\le N$ and for the multishift symbols: for shifts $s_0,\dots,s_r\ge0$ with
$r+1\le N$, let $h_s$ be the symbol whose Jensen test is $\prod_i(1+s_ix)$ and
$h_{s\setminus i}$ the one with the $i$-th shift deleted. Then for every PF polynomial
$p$ of degree at most $N$ and all $a_i\ge0$,
$$
x\,h_s(D)p+\sum_ia_i\,h_{s\setminus i}(D)p
$$
is PF and is preceded by $h_s(D)p$, and such rows can be iterated from a PF seed.

## Companion cones

For a nonzero PF polynomial $h$, a polynomial $k$ is PF with $k\ll h$ if and only if
it is a nonnegative combination of the one-root-deleted Krein summands of $h$. Passing
to coefficientwise limits of the finite-degree tests, the all-degree statement
follows: for PF $h\ne0$,
$$
\bigl(\forall p\text{ PF}:\;h(D)p,\;k(D)p\text{ PF and }h(D)p\ll k(D)p\bigr)
\iff k\text{ is PF and }k\ll h .
$$

## What is new

These finite-degree tests were developed in this library; no published source is
cited, and we attribute none. The finite free additive convolution is discussed on the
[finite free convolutions](/RealRooted/theorems/finite-free-convolutions/) page.

## References

No published source is cited for these results in the formalization.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.FiniteFreeAdditive`
modules named in the metadata.
-/
