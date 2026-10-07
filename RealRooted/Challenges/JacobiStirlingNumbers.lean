import RealRooted.CombinatorialExamples.JacobiStirling.FirstKindPF
import RealRooted.CombinatorialExamples.JacobiStirling.Inverse
import RealRooted.CombinatorialExamples.JacobiStirling.TotallyNonnegative

/-!
# Jacobi–Stirling numbers challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "jacobi-stirling-numbers"
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

The Jacobi–Stirling numbers of the first and second kind,
$\mathrm{Jc}(n,k;z)$ and $\mathrm{JS}(n,k;z)$, satisfy
$$
\mathrm{Jc}(n,k) = \mathrm{Jc}(n-1,k-1) + (n-1)(n-1+z)\,\mathrm{Jc}(n-1,k),
\qquad
\mathrm{JS}(n,k) = \mathrm{JS}(n-1,k-1) + k(k+z)\,\mathrm{JS}(n-1,k),
$$
with $\mathrm{Jc}(0,0) = \mathrm{JS}(0,0) = 1$. The case $z = 1$ gives the
Legendre–Stirling numbers. Equivalently, $\mathrm{Jc}(n,k)$ is an elementary
symmetric function and $\mathrm{JS}(n,k)$ a complete homogeneous symmetric
function of the weights $i(i+z)$. The signed first-kind triangle and the
second-kind triangle are mutually inverse.

**Theorem** (Mongelli). For $z \geq -1$ the first-kind triangle
$(\mathrm{Jc}(n,k;z))_{n,k}$ is totally nonnegative, and every row is a
Pólya-frequency sequence: the row polynomial $\sum_k \mathrm{Jc}(n,k;z)\,x^k$
factors into linear terms $x + i(i+z)$ with nonnegative constants.

## Proof idea

The first-kind triangle is the elementary-symmetric triangle of the weights
$i(i+z)$, which are nonnegative for $z \geq -1$. Such a triangle factors into
nonnegative bidiagonal matrices, so it is totally nonnegative; no planar
network is needed.

## References

Y. Gelineau and J. Zeng, “Combinatorial interpretations of the Jacobi–Stirling
numbers,” *Electronic Journal of Combinatorics* 17 (2010), #R70; P. Mongelli,
“Total positivity properties of Jacobi–Stirling numbers,” *Advances in Applied
Mathematics* 48 (2012), 354–364; G. E. Andrews, E. S. Egge, W. Gawronski and
L. L. Littlejohn, “The Jacobi–Stirling numbers,” *Journal of Combinatorial
Theory, Series A* 120 (2013), 288–303.

The descent polynomials of Jacobi–Stirling permutations are on the
[Jacobi–Stirling descent page](/RealRooted/families/jacobi-stirling-descent/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.JacobiStirling`.
-/
