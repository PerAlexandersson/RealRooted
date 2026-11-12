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

Let $u_0=1$, $u_k\ge 0$, and for site weights $z_1,\dots,z_N$ put
$$Z_N(z_1,\dots,z_N)=\sum_{S\subseteq[N]}
\Bigl(\prod_{R\in\mathrm{Runs}(S)}u_{|R|}\Bigr)\prod_{i\in S}z_i,$$
where $\mathrm{Runs}(S)$ are the maximal nonempty intervals of consecutive selected sites. For
fixed nonnegative site weights $a_i$ let $B_N(t)=Z_N(a_1t,\dots,a_Nt)$. With all
$u_k=1$ one gets $B_N(t)=\prod_i(1+a_it)$.

**Transfer identity.** If $u_k=e_1^{\mathsf T}A^k\mathbf 1$ for a finite nonempty matrix $A$ and
$J=\mathbf 1e_1^{\mathsf T}$, then
$$Z_N(z_1,\dots,z_N)=e_1^{\mathsf T}(J+z_NA)\cdots(J+z_1A)\mathbf 1,$$
because $J^2=J$, $J\mathbf 1=\mathbf 1$ and $e_1^{\mathsf T}J=e_1^{\mathsf T}$; each maximal run of
$A$'s contributes $u_k$. (In the formalization the run sum is the sum over indicator functions
$S\colon\mathrm{Fin}\,N\to\mathrm{Bool}$ of a run weight read from the last site, and the
identity is proved by recursion on the last site.)

**Theorem.** Let $A$ have nonnegative entries and nonnegative ordered $2\times2$ minors (TP2),
with weakly decreasing columns, let $u_k=e_1^{\mathsf T}A^k\mathbf 1$, and let $a_i\ge 0$ be
arbitrary (zero weights allowed). Then every $B_N$ has $B_N(0)=1$, nonnegative coefficients and
degree at most $N$; all its roots are real and negative; and consecutive polynomials
$B_N,B_{N+1}$ are in oriented weak interlacing position (`StrictInterl`: the roots of $B_{N+1}$
are separated by, and enclose, those of $B_N$; roots may coincide, and degrees may agree when a
weight vanishes).

**Proof idea.** Reflect the transfer vector: with $\mathbf h_0=\mathbf 1$ and
$\mathbf h_{N+1}=(a_NA+xJ)\mathbf h_N$ one has $Y_N=\mathrm{reflect}_N\mathbf h_N$ for the
transfer vector $Y_N$ in the variable $t$, so
$B_N=\mathrm{reflect}_N h_{N,1}=h_{N,1}^{\mathrm{rev}}$.
The matrices $a_kA$ are again TP2 with decreasing columns, and the vector recursion with
these matrices is an interlacing sequence with nonnegative coefficients by the affine-step form of
Brändén's constant-matrix theorem. Hence $h_{N,1}$ has only real nonpositive roots, and
$h_{N,1}\ll h_{N+1,1}$. Reversal of polynomials with nonpositive roots reverses the interlacing
(`reciprocalShift_reverses_strictInterl`), and Wagner's $x$-multiplication equivalence
($f\ll g\iff g\ll xf$) turns the reversed relation into $B_N\ll B_{N+1}$. Absorbing $a_N$ into the
matrix instead of dividing by it means that zero site weights need no limiting argument.

**Classical input.** The constant-matrix theorem of Brändén [@Branden2015, Corollary 8.6,
arXiv:1410.6601] is used only as the preservation input (through the TP2 affine step); the
reversal and the transfer identity are specific to this page.

**Not covered.** The second sufficient hypothesis of the weighted-run problem, that the sequence
$u$ is PF-infinity, is not formalized here: it reduces to the matrix case for finite
Edrei–Thoma products and then needs a limiting argument.

## What is new

The proof is new, developed for RealRooted, and is of independent research
interest: the transfer identity for site-weighted run sums and the reflection of the Hessenberg
vector recursion are not taken from the literature, and the classical constant-matrix theorem is
used only as the preservation input.

## References

See [@Branden2015]. See also the [finite TP2 Hessenberg
certificate](/RealRooted/theorems/tp2-hessenberg-certificate/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Toeplitz` modules named in
the metadata.
-/
