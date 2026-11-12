module

import RealRooted.Toeplitz.AffineVector
import RealRooted.Toeplitz.RunExamples
import RealRooted.Toeplitz.SiteWeightedRunRoots
import RealRooted.Toeplitz.SiteWeightedRuns

/-!
# Site-weighted run polynomials of a TP2 kernel

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "site-weighted-run-polynomials"
formalized = "2026-11-09"
references = [
  "Branden2015",
]
authors = ["Brändén"]
years = [2015]
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.siteWeightedRuns"
module = "RealRooted.Toeplitz.SiteWeightedRuns"
label = "The site-weighted run sum Z_N(z), a sum over subsets of products of run weights"

[[definitions]]
name = "RealRooted.runKernel"
module = "RealRooted.Toeplitz.SiteWeightedRuns"
label = "The run kernel u_k = e_1^T A^k 1"

[[definitions]]
name = "RealRooted.siteWeightedRunPolynomial"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "B_N(t) = Z_N(a_0 t, ..., a_{N-1} t)"

[[theorems]]
name = "RealRooted.siteWeightedRuns_runKernel"
module = "RealRooted.Toeplitz.SiteWeightedRuns"
label = "Transfer identity: Z_N = e_1^T (J + z A) ... (J + z A) 1"

[[theorems]]
name = "RealRooted.siteWeightedRuns_one_by_one"
module = "RealRooted.Toeplitz.RunExamples"
label = "For the kernel u = 1 the run sum is the product of (1 + z_i)"

[[theorems]]
name = "RealRooted.runVector_eq_reflect_affineVector"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "The transfer vector is the reflection of the affine vector for the matrices a_k A"

[[theorems]]
name = "RealRooted.isRealRootedIn_Iio_siteWeightedRunPolynomial"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "B_N is real-rooted with all roots negative"

[[theorems]]
name = "RealRooted.strictInterl_siteWeightedRunPolynomial"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "Consecutive B_N, B_{N+1} are in oriented weak interlacing position"

[[theorems]]
name = "RealRooted.siteWeightedRunPolynomial_certificate"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "B_N(0) = 1, nonnegative coefficients, negative real roots, B_N interlaces B_{N+1}"
headline = true
-->

<!-- realrooted-catalog-content -->
# Site-weighted run polynomials of a TP2 kernel

Run polynomials built from a finite TP2 kernel and nonnegative site weights have negative real
roots, and consecutive ones interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
For run weights $u_k$ and site weights $z_1,\dots,z_N$ put
$$Z_N(z_1,\dots,z_N)=\sum_{S\subseteq[N]}
\Bigl(\prod_{R\in\mathrm{Runs}(S)}u_{|R|}\Bigr)\prod_{i\in S}z_i,$$
where $\mathrm{Runs}(S)$ are the maximal intervals of consecutive elements of $S$. For site
weights $a_i$ let $B_N(t)=Z_N(a_1t,\dots,a_Nt)$. For $u_k=1$ one gets $B_N(t)=\prod_i(1+a_it)$.

**Proposition (transfer identity).** Let $A$ be a square matrix with
$u_k=e_1^{\mathsf T}A^k\mathbf 1$ and $J=\mathbf 1e_1^{\mathsf T}$. Then
$$Z_N(z_1,\dots,z_N)=e_1^{\mathsf T}(J+z_NA)\cdots(J+z_1A)\mathbf 1.$$

**Theorem.** Let $A$ be TP2 (nonnegative entries and nonnegative ordered $2\times2$ minors) with
weakly decreasing columns, let $u_k=e_1^{\mathsf T}A^k\mathbf 1$, and let $a_i\ge0$, with zeros
allowed. Then $B_N(0)=1$, $B_N$ has nonnegative coefficients and degree at most $N$, and all
roots of $B_N$ are real and negative. Moreover $B_N\ll B_{N+1}$: the roots of $B_{N+1}$ are
separated by, and enclose, those of $B_N$. Roots may coincide, and the degrees agree when a site
weight vanishes.

## Proof

With $\mathbf h_0=\mathbf 1$ and $\mathbf h_{N+1}=(a_NA+xJ)\mathbf h_N$, the polynomial $B_N$ is
the reversal of $h_{N,1}$. The matrices $a_kA$ are TP2 with decreasing columns, so Brändén's
constant-matrix theorem [@Branden2015, Corollary 8.6] gives $h_{N,1}\ll h_{N+1,1}$ with
nonpositive roots. Reversal reverses interlacing of such polynomials, and $f\ll g\iff g\ll xf$
gives $B_N\ll B_{N+1}$. Zero site weights need no limiting argument.

## References

[@Branden2015]. Related page: the [finite TP2 Hessenberg
certificate](/RealRooted/theorems/tp2-hessenberg-certificate/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Toeplitz` modules named in
the metadata.
-/
