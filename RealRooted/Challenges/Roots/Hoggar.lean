module

import RealRooted.CoefficientShape.Hoggar

/-!
# Hoggar's theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hoggar-log-concavity"
formalized = "2026-10-07"
references = []
tags = []
authors = ["Hoggar"]
years = [1974]

[[theorems]]
name = "RealRooted.coeffLogConcaveUpTo_mul"
module = "RealRooted.CoefficientShape.Hoggar"
label = "Hoggar: log-concavity without internal zeros is closed under products"
headline = true

[[theorems]]
name = "RealRooted.coeffNoInternalZerosUpTo_mul"
module = "RealRooted.CoefficientShape.Hoggar"
label = "Products have no internal zeros"
-->

<!-- realrooted-catalog-content -->
# Hoggar's theorem

Products of polynomials with nonnegative, log-concave coefficients without internal zeros again
have these properties.

## Results

A sequence $a_0,\dots,a_n$ of nonnegative reals is *log-concave* if $a_{k-1}a_{k+1}\le a_k^2$ for
$0<k<n$, and has *no internal zeros* if $a_ia_k\ne0$ and $i<j<k$ imply $a_j\ne0$.

**Theorem (Hoggar).** Let $p$ and $q$ be polynomials with nonnegative coefficients whose
coefficient sequences are log-concave and have no internal zeros. Then the coefficient sequence of
$pq$ is log-concave and has no internal zeros.

The hypothesis on internal zeros is needed: $1+x^3$ and $1+x$ have log-concave coefficient
sequences, but $(1+x^3)(1+x)=1+x+x^3+x^4$ does not, since $a_1a_3=1>0=a_2^2$.

## Use

Real-rooted polynomials with nonnegative coefficients satisfy the hypotheses by Newton's
inequalities.

## Proof

A nonnegative log-concave sequence without internal zeros satisfies $a_ia_{j+1}\le a_{i+1}a_j$
for $i\le j$. The $2\times2$ Cauchy–Binet identity for the product of two Toeplitz matrices then
gives log-concavity of the product. The product has no internal zeros because the supports of
both factors are intervals.

## References

S. G. Hoggar, *Chromatic polynomials and logarithmic concavity*, J. Combin.
Theory Ser. B 16 (1974), 248–254.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CoefficientShape.Hoggar`.
-/
