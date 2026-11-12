module

import RealRooted.Transforms.BrandenE
import RealRooted.Transforms.BrandenE.IntervalPreserver
import RealRooted.Transforms.BrandenE.Interlacing

/-!
# Brändén's E transform on polynomials with roots in $[-1,0]$

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-e-transform"
formalized = "2026-09-14"
tags = []
references = [
  "Branden2006",
]
authors = ["Brändén"]
years = [2006]

[[definitions]]
name = "RealRooted.orderedBellPolynomial"
module = "RealRooted.Transforms.BrandenE.OrderedBell"
label = "Ordered Bell polynomials F_n"

[[definitions]]
name = "RealRooted.brandenE"
module = "RealRooted.Transforms.BrandenE.Basic"
label = "The E transform x^n ↦ ordered Bell polynomial"

[[definitions]]
name = "RealRooted.brandenBasisImage"
module = "RealRooted.Transforms.BrandenE.BasisImage"
label = "Images E(x^k (x + 1)^(n − k))"

[[theorems]]
name = "RealRooted.brandenE_isPFPolynomial_of_roots_mem_Icc"
module = "RealRooted.Transforms.BrandenE.IntervalPreserver"
label = "Positive leading coefficient and roots in [−1, 0] give a PF image"

[[theorems]]
name = "RealRooted.brandenE_eq_zero_or_splits_and_roots_nonpos"
module = "RealRooted.Transforms.BrandenE.IntervalPreserver"
label = "Roots in [−1, 0] give zero or a real-rooted image with nonpositive roots"

[[theorems]]
name = "RealRooted.brandenBasisImage_strictInterl"
module = "RealRooted.Transforms.BrandenE.ProperPosition"
label = "The images of the binomial basis form an interlacing sequence"

[[theorems]]
name = "RealRooted.orderedBellPolynomial_isPFPolynomial"
module = "RealRooted.Transforms.BrandenE.ProperPosition"
label = "Ordered Bell polynomials are PF polynomials"

[[theorems]]
name = "RealRooted.brandenE_descPochhammer"
module = "RealRooted.Transforms.BrandenE.Inverse"
label = "E sends x(x − 1)⋯(x − n + 1) to n! xⁿ"

[[theorems]]
name = "RealRooted.brandenE_strictInterl_of_rootwiseLE"
module = "RealRooted.Transforms.BrandenE.Interlacing"
label = "Rootwise order of polynomials with roots in [-1, 0] gives interlacing E-images"
headline = true

[[theorems]]
name = "RealRooted.brandenE_strictInterl_one_root_replacement"
module = "RealRooted.Transforms.BrandenE.Interlacing"
label = "Moving one root to the right gives interlacing images"
-->

<!-- realrooted-catalog-content -->
# Brändén's E transform on polynomials with roots in $[-1,0]$

The E transform sends a real-rooted polynomial with all roots in $[-1,0]$ and positive leading
coefficient to a PF polynomial, and respects the rootwise order on such polynomials.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
A polynomial is *PF* (Pólya frequency) if it is zero or has nonnegative coefficients and only
real, nonpositive roots. The ordered Bell polynomials are
$$
F_0=1,\qquad F_{n+1}=x\,F_n+x(1+x)\,F_n',
$$
so that $F_n=\sum_k k!\,S(n,k)\,x^k$ with $S(n,k)$ the Stirling numbers of the second kind. The
*E transform* is the linear map with $E(x^n)=F_n$. It satisfies
$E\bigl(x(x-1)\cdots(x-n+1)\bigr)=n!\,x^n$.

**Theorem (Brändén [@Branden2006]).** Let $p$ be a real polynomial with only real roots, all in
$[-1,0]$.

- If $p$ has positive leading coefficient, then $E(p)$ is PF.
- In general, $E(p)=0$, or $E(p)\ne0$ is real-rooted with only nonpositive roots.

**Theorem (interlacing basis).** For $0\le k\le n$ let $b_{n,k}=E\bigl(x^k(x+1)^{n-k}\bigr)$.
Then $b_{n,i}\ll b_{n,j}$ for all $0\le i\le j\le n$. In particular $F_n=b_{n,n}$ is PF.

**Theorem (rootwise order).** Let $f,g$ be monic, real-rooted of the same degree $n\ge1$ with
all roots in $[-1,0]$, and suppose that their roots, sorted increasingly, satisfy $f\le g$
coordinatewise. Then $E(f)\ll E(g)$, as in Theorem 4.6 of [@Branden2006]. More precisely, for
$u\le v$ and monic real-rooted $h$ with roots in $[-1,0]$,
$$
E\bigl((x-u)h\bigr)\ll E\bigl((x-v)h\bigr),
$$
with no condition on $u,v$ beyond $u\le v$.

## Use

The ordered Bell numbers are [OEIS A000670](https://oeis.org/A000670).

## Proof

A polynomial with all roots in $[-1,0]$ is a nonnegative combination of the polynomials
$x^k(x+1)^{n-k}$. The images $b_{n,k}$ arise by Euler steps $f\mapsto(x+r)f+x(1+x)f'$, which
preserve interlacing, and a nonnegative combination of an interlacing sequence is real-rooted.
The rootwise statement follows by moving one root at a time, from all roots $-1$ through $f$
and $g$ to all roots $0$.

## References

The results are from [@Branden2006].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Transforms.BrandenE`.
-/
