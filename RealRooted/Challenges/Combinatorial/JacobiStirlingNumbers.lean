module

import RealRooted.CombinatorialExamples.JacobiStirling.FirstKindPF
import RealRooted.CombinatorialExamples.JacobiStirling.Inverse
import RealRooted.CombinatorialExamples.JacobiStirling.TotallyNonnegative

/-!
# Jacobi–Stirling numbers challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "jacobi-stirling-numbers"
formalized = "2026-09-13"
tags = []
references = [
  "GelineauZeng2010",
  "Mongelli2012",
  "AndrewsEggeGawronskiLittlejohn2013",
]
authors = ["Gelineau", "Zeng", "Mongelli"]
years = [2010, 2012]

[[definitions]]
name = "RealRooted.JacobiStirling.firstKind"
module = "RealRooted.CombinatorialExamples.JacobiStirling.FirstKind"
label = "Jacobi–Stirling numbers of the first kind"

[[definitions]]
name = "RealRooted.JacobiStirling.secondKind"
module = "RealRooted.CombinatorialExamples.JacobiStirling.SecondKind"
label = "Jacobi–Stirling numbers of the second kind"

[[theorems]]
name = "RealRooted.JacobiStirling.firstKindMatrix_isTotallyNonneg"
module = "RealRooted.CombinatorialExamples.JacobiStirling.TotallyNonnegative"
label = "Mongelli: the first-kind triangle is totally nonnegative for z ≥ −1"
headline = true

[[theorems]]
name = "RealRooted.JacobiStirling.firstKindRow_isPFPolynomial"
module = "RealRooted.CombinatorialExamples.JacobiStirling.FirstKindPF"
label = "First-kind rows are Pólya-frequency polynomials for z ≥ −1"

[[theorems]]
name = "RealRooted.JacobiStirling.legendreStirlingFirstMatrix_isTotallyNonneg"
module = "RealRooted.CombinatorialExamples.JacobiStirling.TotallyNonnegative"
label = "The Legendre–Stirling first-kind triangle is totally nonnegative"

[[theorems]]
name = "RealRooted.JacobiStirling.secondKind_eq_aeval_hsymm_of_le"
module = "RealRooted.CombinatorialExamples.JacobiStirling.SecondKind"
label = "Second-kind numbers as complete homogeneous symmetric functions"

[[theorems]]
name = "RealRooted.JacobiStirling.signedFirstKind_mul_secondKind_sum"
module = "RealRooted.CombinatorialExamples.JacobiStirling.Inverse"
label = "The signed first-kind and second-kind triangles are mutually inverse"
-->

<!-- realrooted-catalog-content -->
# Jacobi–Stirling numbers

The first-kind Jacobi–Stirling triangle is totally nonnegative for $z\ge-1$, and its rows are
Pólya-frequency polynomials with an explicit linear factorization.

## Results

The Jacobi–Stirling numbers of the first and second kind, $\mathrm{Jc}(n,k;z)$ and
$\mathrm{JS}(n,k;z)$, satisfy $\mathrm{Jc}(0,0)=\mathrm{JS}(0,0)=1$; both vanish if exactly
one index is $0$; and, for $n,k\ge1$,
$$
\mathrm{Jc}(n,k) = \mathrm{Jc}(n-1,k-1) + (n-1)(n-1+z)\,\mathrm{Jc}(n-1,k),
$$
$$
\mathrm{JS}(n,k) = \mathrm{JS}(n-1,k-1) + k(k+z)\,\mathrm{JS}(n-1,k).
$$
The case $z=1$ gives the Legendre–Stirling numbers. For $k\le n$, $\mathrm{Jc}(n,k)$ is the
elementary symmetric function $e_{n-k}$ in the weights $w_i=i(i+z)$, $1\le i\le n-1$, and
$\mathrm{JS}(n,k)$ is the complete homogeneous symmetric function $h_{n-k}$ in
$w_1,\dots,w_k$.

**Theorem (Mongelli).** [@Mongelli2012] For $z\ge-1$ the triangle
$(\mathrm{Jc}(n,k;z))_{n,k\ge0}$ is totally nonnegative, including the Legendre–Stirling
case $z=1$. For $n\ge1$ and $z\ge-1$,
$$
\sum_k \mathrm{Jc}(n,k;z)\,x^k = x\prod_{i=1}^{n-1}\bigl(x+i(i+z)\bigr),
$$
so every row is a Pólya-frequency polynomial.

**Proposition (inversion).** For all $n,j\ge0$ and every $z$,
$$
\sum_{k=0}^{n}(-1)^{n+k}\,\mathrm{Jc}(n,k;z)\,\mathrm{JS}(k,j;z)=\delta_{n,j}.
$$

## Proof

The triangle is the elementary-symmetric triangle of the weights $w_i$, which are nonnegative
for $z\ge-1$. Such a triangle is a product of nonnegative bidiagonal matrices, hence totally
nonnegative.

## References

[@GelineauZeng2010; @AndrewsEggeGawronskiLittlejohn2013]. The descent polynomials of
Jacobi–Stirling permutations are on the
[Jacobi–Stirling descent page](rr:jacobi-stirling-descent).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.JacobiStirling`.
-/
