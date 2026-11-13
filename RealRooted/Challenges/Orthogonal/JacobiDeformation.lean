module

public import RealRooted.JacobiDeformation
public import RealRooted.JacobiDeformation.Basic
public import RealRooted.JacobiDeformation.Strict
public import RealRooted.SimpleRoots
public import RealRooted.SpectralProduct

/-!
# Jacobi deformation

<!-- realrooted-catalog
version = 1
section = "families"
slug = "jacobi-deformation"
formalized = "2026-10-06"
tags = ["realrooted-original"]
references = [
  "MicchelliWilloughby1979",
]
authors = ["Micchelli", "Willoughby", "Alexandersson"]
years = [1979, 2026]

[[definitions]]
name = "RealRooted.JacobiDeformation.polynomial"
module = "RealRooted.JacobiDeformation.Basic"
label = "The Jacobi deformation J_{m,δ}"

[[definitions]]
name = "RealRooted.increasingEigenvalues"
module = "RealRooted.SpectralProduct"
label = "Eigenvalues of a symmetric matrix in increasing order"

[[theorems]]
objects = ["Jacobi deformation polynomials"]
name = "RealRooted.JacobiDeformation.polynomial_all_rank_nonneg_parameter"
module = "RealRooted.JacobiDeformation.Strict"
label = "For every δ ≥ 0 all roots are real and negative"
headline = true

[[theorems]]
name = "RealRooted.JacobiDeformation.interlaces_derivative_polynomial_zero"
module = "RealRooted.JacobiDeformation.Strict"
label = "For 0 < δ < 1 the roots are simple, interlace J′_{m,0} and share no root with it"

[[theorems]]
objects = ["Jacobi deformation polynomials"]
property = "pf"
name = "RealRooted.JacobiDeformation.isPFPolynomial_polynomial"
module = "RealRooted.JacobiDeformation.Strict"
label = "For every δ ≥ 0 the deformation is a PF polynomial"

[[theorems]]
name = "RealRooted.aeval_prod_sub_increasingEigenvalues_nonneg"
module = "RealRooted.SpectralProduct"
label = "Micchelli–Willoughby: initial spectral products are entrywise nonnegative"
-->

<!-- realrooted-catalog-content -->
# Jacobi deformation

The Jacobi deformation $J_{m,\delta}$ has only negative real roots for every $\delta\ge0$, and for
$0<\delta<1$ its roots are simple and interlace the roots of $J_{m,0}'$.

## Results

For $m\in\mathbb N$ and real $\delta,c,d,U,V$, the Jacobi deformation is the monic polynomial of
degree $m$
$$
J_{m,\delta}^{c,d}(x;U,V)=\sum_{i+j\le m}
  \frac{m!}{(m-i-j)!\,i!\,j!}
  \frac{(m+c+d-1+\delta)_{i+j}}{(c)_i\,(d)_j}\,
  U^iV^j x^{m-i-j},
$$
where $(a)_n=a(a+1)\cdots(a+n-1)$ is the rising factorial.

**Theorem.** Let $c,d,U,V>0$.

- For every $\delta\ge0$, all roots of $J_{m,\delta}^{c,d}$ are real and negative, and
  $J_{m,\delta}^{c,d}$ is a Pólya frequency polynomial.
- If $m\ge1$ and $0<\delta<1$, then $J_{m,\delta}^{c,d}$ has simple roots,
  $(J_{m,0}^{c,d})'\ll J_{m,\delta}^{c,d}$, and the two polynomials have no common root.

**Theorem (Micchelli–Willoughby).** [@MicchelliWilloughby1979] Let $A$ be a real symmetric
matrix with nonnegative entries and simple spectrum $\mu_1<\dots<\mu_N$. Then
$(A-\mu_1)\cdots(A-\mu_k)$ is entrywise nonnegative for every $k<N$.

## Proof

Let $s=c+d$. A finite Appell kernel is diagonal, with positive weights, in the basis of monic
shifted Jacobi polynomials orthogonal for $\ell(t^k)=(c)_k/(s)_k$, and evaluating it at suitable
points recovers $J_{m,\delta}$. The Micchelli–Willoughby theorem, applied to the collocation
matrix of the Jacobi operator at the roots of a quasi-Jacobi polynomial, gives strict signs of
the kernel there; this settles $0<\delta<1$. The shift
$bJ_{m,\delta+1}=(b+m)J_{m,\delta}-xJ_{m,\delta}'$ with $b=m+s-1+\delta$ extends negative real
roots to all $\delta\ge0$.

## References

[@MicchelliWilloughby1979]. The shifted Jacobi polynomials used in the proof are on the
[Jacobi polynomials](rr:jacobi-polynomials) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.JacobiDeformation` and `RealRooted.SpectralProduct`.
-/
