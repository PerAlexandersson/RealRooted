module

import RealRooted.CoefficientShape.Liggett

/-!
# Liggett's theorem challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "liggett-ultra-log-concavity"
formalized = "2026-10-07"
tags = []
references = [
  "Gurvits2009",
]
authors = ["Liggett"]
years = [1997]

[[definitions]]
name = "RealRooted.CoeffUltraLogConcaveUpTo"
module = "RealRooted.CoefficientShape"
label = "Ultra-log-concavity of order d"

[[theorems]]
name = "RealRooted.coeffUltraLogConcaveUpTo_mul"
module = "RealRooted.CoefficientShape.Liggett"
label = "Liggett: ultra-log-concavity is closed under products"
headline = true

[[theorems]]
name = "RealRooted.coeffUltraLogConcaveUpTo_conv"
module = "RealRooted.CoefficientShape.Liggett"
label = "Convolution of ULC(m) and ULC(n) sequences is ULC(m + n)"
-->

<!-- realrooted-catalog-content -->
# Liggett's theorem

We call a nonnegative sequence $a_0,\dotsc,a_d$ *ultra-log-concave of order $d$*,
written ULC($d$), if $a_k/\binom{d}{k}$ is log-concave:
$$
k(d-k)\, a_k^2 \geq (k+1)(d-k+1)\, a_{k-1} a_{k+1} \qquad (0 < k < d).
$$
Convolution of ultra-log-concave sequences without internal zeros is again ultra-log-concave.

## Results

**Theorem (Liggett).** Let $a$ be ULC($m$) and $b$ be ULC($n$), both nonnegative, vanishing
beyond their order and without internal zeros. Then the convolution
$c_k=\sum_i a_ib_{k-i}$ is ULC($m+n$) and has no internal zeros. Equivalently, for polynomials
with nonnegative, ultra-log-concave coefficients without internal zeros, the product has
ultra-log-concave coefficients of order its degree.

By Newton's inequalities, the coefficients of a real-rooted polynomial of degree $d$ with
nonnegative coefficients are ULC($d$).

## Use

This is the ultra-log-concave analogue of
[Hoggar's theorem](rr:hoggar-log-concavity). The hypothesis on internal
zeros cannot be dropped: the sequence $1,0,0,1$ satisfies the displayed inequalities for
$d=3$, but its product with $1+x$ does not satisfy them for $d=4$.

## Proof

We argue by induction on $n$, splitting $(n+1)b_j=(n+1-j)b_j+jb_j$ into two ULC($n$)
sequences. These are likelihood-ratio ordered, which follows from log-concavity of
$b_j\,j!\,(n+1-j)!$. Convolution with the log-concave sequence $a$ preserves the ordering,
by a $2\times2$ Cauchy–Binet argument as for Hoggar's theorem, and a real-number inequality
combines the two induction hypotheses. This is not Liggett's original proof; others use mixed
volumes [@Gurvits2009], the Johnson scheme (Kahn–Neiman) and Lorentzian polynomials
(Brändén–Huh).

## References

T. M. Liggett, “Ultra logconcave sequences and negative dependence,” *Journal of
Combinatorial Theory, Series A* 79 (1997), 315–325. See also [@Gurvits2009].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CoefficientShape.Liggett`.
-/
