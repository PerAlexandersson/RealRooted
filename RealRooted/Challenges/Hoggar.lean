import RealRooted.CoefficientShape.Hoggar

/-!
# Hoggar's theorem challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hoggar-log-concavity"
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

A sequence $a_0, a_1, \dotsc, a_n$ of nonnegative reals is *log-concave* if
$a_{k-1} a_{k+1} \leq a_k^2$ for $0 < k < n$, and has *no internal zeros* if
$a_i a_k \neq 0$ and $i < j < k$ imply $a_j \neq 0$.

**Theorem** (Hoggar). If two polynomials with nonnegative coefficients have
log-concave coefficient sequences without internal zeros, then so does their
product.

Real-rooted polynomials with nonnegative coefficients have this property by
Newton's inequalities, but the class is much larger.  The hypothesis on
internal zeros cannot be dropped: $1 + x^3$ (coefficients $1, 0, 0, 1$) and
$1 + x$ are log-concave, but their product $1 + x + x^3 + x^4$ is not, since
$a_1 a_3 = 1 > 0 = a_2^2$.

## Proof idea

A nonnegative log-concave sequence without internal zeros is a Pólya
frequency sequence of order two: $a_i a_{j+1} \leq a_{i+1} a_j$ for
$i \leq j$.  The coefficients of the product are given by a product of two
Toeplitz matrices, and the Cauchy–Binet formula writes each $2 \times 2$
minor of the product as a sum of products of nonnegative minors of the
factors.

## References

S. G. Hoggar, *Chromatic polynomials and logarithmic concavity*, J. Combin.
Theory Ser. B 16 (1974), 248–254.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CoefficientShape.Hoggar`.
-/
