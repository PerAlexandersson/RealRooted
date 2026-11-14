module

import RealRooted.Hypergeometric.ThreeFTwo

/-!
<!-- realrooted-catalog
version = 1
section = "families"
slug = "terminating-three-f-two"
formalized = "2026-11-14"
authors = ["Hélder Lima"]
years = [2023]
tags = []

[[definitions]]
name = "RealRooted.Hypergeometric.threeFTwo"
module = "RealRooted.Hypergeometric.ThreeFTwo"
label = "Terminating three-over-two hypergeometric series"

[[theorems]]
name = "RealRooted.Hypergeometric.threeFTwo_strictInterlaces"
module = "RealRooted.Hypergeometric.ThreeFTwo"
label = "Strict interlacing and simple positive zeros in Lima's strict range"
headline = true
objects = ["Terminating ₃F₂ polynomials"]
property = "interlacing"

[[theorems]]
name = "RealRooted.Hypergeometric.threeFTwo_splits"
module = "RealRooted.Hypergeometric.ThreeFTwo"
label = "Real-rootedness at the weak parameter boundary"
objects = ["Terminating ₃F₂ polynomials"]

[[theorems]]
name = "RealRooted.Hypergeometric.isRoot_threeFTwo_pos"
module = "RealRooted.Hypergeometric.ThreeFTwo"
label = "Every real zero is positive for positive parameters"

[[theorems]]
name = "RealRooted.Hypergeometric.monicThreeFTwo_eq_charpoly"
module = "RealRooted.Hypergeometric.ThreeFTwo"
label = "All-degree identity with a three-bidiagonal production matrix"
-->

<!-- realrooted-catalog-content -->
# Terminating ₃F₂ polynomials

## Results

We consider the finite series
$$H_n(z)={}_3F_2(-n,B_{1,n},B_{2,n};a_1,a_2;z),$$
where the upper parameters are $(b_1+m,b_2+m-1)$ for $n=2m>0$ and
$(b_1+m,b_2+m)$ for $n=2m+1$, with $H_0=1$.

For positive parameters satisfying $b_1>\max(a_1,a_2-1)$ and
$b_2>\max(a_1,a_2)$, consecutive polynomials strictly interlace and all zeros
are simple and positive. With weak inequalities, the polynomials remain
real-rooted and all zeros are positive.

## Proof

We identify the monic series with the characteristic polynomial of a product
of three bidiagonal matrices. The strict result follows from total
nonnegativity and oscillation. We obtain the weak boundary by a coefficientwise
limit; alternating coefficients exclude nonpositive real zeros.

## References

- H. Lima, [Multiple orthogonal polynomials associated with branched continued
  fractions for ratios of hypergeometric series](https://arxiv.org/abs/2208.03539v2),
  equations (6.6), (8.1), (8.9), and Theorem 8.4.
<!-- /realrooted-catalog-content -->
-/

public section
