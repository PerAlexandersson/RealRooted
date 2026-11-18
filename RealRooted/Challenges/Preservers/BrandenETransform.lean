module

import RealRooted.PolyaFrequency.EventuallyPolynomial.CausalClosure.ZeroPrefix
import RealRooted.PolynomialValueEulerNumerator
import RealRooted.PolynomialValueEulerNumerator.Interlacing
import RealRooted.PolynomialValueEulerNumerator.PF
import RealRooted.PolynomialValueEulerNumerator.PF.Causal
import RealRooted.Transforms.BrandenE.Basic
import RealRooted.Transforms.BrandenE.Interlacing
import RealRooted.Transforms.BrandenE.IntervalPreserver
import RealRooted.Transforms.BrandenE.Inverse
import RealRooted.Transforms.BrandenE.OrderedBell
import RealRooted.Transforms.BrandenE.ProperPosition

/-!
# Brändén's E transform and Euler numerators

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "branden-e-transform"
formalized = "2026-09-14"
references = [
  "Branden2006",
  "Brenti1989",
]
authors = ["Brenti", "Brändén"]
years = [1989, 2006]

[[definitions]]
name = "RealRooted.brandenE"
module = "RealRooted.Transforms.BrandenE.Basic"
label = "The E transform, $x^n ↦$ ordered Bell polynomial"

[[definitions]]
name = "RealRooted.orderedBellPolynomial"
module = "RealRooted.Transforms.BrandenE.OrderedBell"
label = "Ordered Bell polynomials $F_n$"

[[definitions]]
name = "RealRooted.polynomialValueEulerNumerator"
module = "RealRooted.PolynomialValueEulerNumerator"
label = "Euler numerator $W_p$ of the values $p(0), p(1), p(2), …$"

[[theorems]]
name = "RealRooted.brandenE_strictInterl_of_rootwiseLE"
module = "RealRooted.Transforms.BrandenE.Interlacing"
label = "Brändén: rootwise order of polynomials with roots in [−1, 0] gives interlacing E-images"
headline = true

[[theorems]]
name = "RealRooted.brandenE_isPFPolynomial_of_roots_mem_Icc"
module = "RealRooted.Transforms.BrandenE.IntervalPreserver"
label = "Brändén: positive leading coefficient and roots in [−1, 0] give a PF image"

[[theorems]]
name = "RealRooted.brandenBasisImage_strictInterl"
module = "RealRooted.Transforms.BrandenE.ProperPosition"
label = "The images of the basis xᵏ(x + 1)ⁿ⁻ᵏ form an interlacing sequence"

[[theorems]]
objects = ["Ordered Bell polynomials"]
property = "pf"
name = "RealRooted.orderedBellPolynomial_isPFPolynomial"
module = "RealRooted.Transforms.BrandenE.ProperPosition"
label = "Ordered Bell polynomials are PF polynomials"

[[theorems]]
name = "RealRooted.brandenE_descPochhammer"
module = "RealRooted.Transforms.BrandenE.Inverse"
label = "E sends x(x − 1)⋯(x − n + 1) to n! xⁿ"

[[theorems]]
name = "RealRooted.polynomialValueEulerNumerator_strictInterl_of_rootwiseLE"
module = "RealRooted.PolynomialValueEulerNumerator.Interlacing"
label = "Rootwise-ordered polynomials with roots in [−1, 0] have interlacing Euler numerators"

[[theorems]]
name = "RealRooted.isPFPolynomial_polynomialValueEulerNumerator_of_polyaFreqSeq"
module = "RealRooted.PolynomialValueEulerNumerator.PF.Causal"
label = "A Pólya frequency value sequence has a PF Euler numerator"

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_polynomialValueSeq_of_eulerNumerator"
module = "RealRooted.PolynomialValueEulerNumerator.PF"
label = "Brenti: a PF Euler numerator makes the value sequence Pólya frequency"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.causalFwdDiff_of_eventually_polynomial"
module = "RealRooted.PolyaFrequency.EventuallyPolynomial.CausalClosure.ZeroPrefix"
label = "A Pólya frequency sequence with a polynomial tail has a PF causal difference"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Brändén's E transform and Euler numerators

The E transform sends $x^n$ to the $n$th ordered Bell polynomial. Brändén proved that it maps
polynomials with all roots in $[-1,0]$ to PF polynomials and turns their rootwise order into
interlacing. Through the Euler numerator of $\sum_np(n)x^n$, this decides when the values
$p(0),p(1),\dotsc$ form a Pólya frequency sequence.

## Results

A polynomial is *PF* if it has nonnegative coefficients and is zero or has only real,
nonpositive roots. The ordered Bell polynomials are $F_0=1$, $F_{n+1}=xF_n+x(1+x)F_n'$, so
$F_n=\sum_kk!\,S(n,k)\,x^k$. The *E transform* is the linear map with $E(x^n)=F_n$; it sends
$x(x-1)\dotsm(x-n+1)$ to $n!\,x^n$. For a real polynomial $p$ of degree $d$, the *Euler
numerator* $W_p$ is defined by
$$
\sum_{n\ge0}p(n)\,x^n=\frac{W_p(x)}{(1-x)^{d+1}},\qquad
W_p(x)=(1-x)^d\,E(p)\Bigl(\frac x{1-x}\Bigr).
$$

**Theorem (Brändén).** [@Branden2006, Thm. 4.6] If $p$ has positive leading coefficient and
all roots in $[-1,0]$, then $E(p)$ is PF. If $f,g$ are monic of the same degree with all roots
in $[-1,0]$, and the roots of $f$, sorted increasingly, are coordinatewise at most those of $g$,
then $E(f)\ll E(g)$ and $W_f\ll W_g$.

**Corollary (basis).** For $0\le i\le j\le n$,
$E\bigl(x^i(x+1)^{n-i}\bigr)\ll E\bigl(x^j(x+1)^{n-j}\bigr)$. In particular the ordered Bell
polynomial $F_n$ is PF.

**Theorem (Euler numerators; Brenti).** [@Brenti1989, Thm. 4.4.4] The values $p(0),p(1),\dotsc$
form a Pólya frequency sequence if and only if $W_p$ is PF.

**Theorem (polynomial tails).** If $a$ is a Pólya frequency sequence with $a_n=p(n)$ for all
large $n$ and some polynomial $p\ne0$, then $(a_0,a_1-a_0,a_2-a_1,\dotsc)$ is again a Pólya
frequency sequence.

## Use

With Wagner's product theorem for value sequences on the
[Hadamard products](rr:hadamard-products) page, the Euler numerator criterion controls Euler
numerators of products. The [Touchard transform](rr:touchard-transform) page determines the
exact sets $J$ for which the E transform maps polynomials with roots in $J$ to real-rooted
polynomials.

## Proof

A polynomial with all roots in $[-1,0]$ is a nonnegative combination of the polynomials
$x^k(x+1)^{n-k}$. Their images arise by steps $f\mapsto(x+r)f+x(1+x)f'$, which preserve
interlacing, so they form an interlacing sequence and nonnegative combinations stay real-rooted.
The rootwise statement follows by moving one root at a time. The Euler numerator criterion
comes from the polynomial-tail theorem, applied $d+1$ times.

## References

[@Branden2006, Thm. 4.6]; [@Brenti1989, Thm. 4.4.4].
<!-- /realrooted-catalog-content -->
-/
