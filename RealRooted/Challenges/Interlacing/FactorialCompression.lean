module

import RealRooted.FactorialCompression.DegreeChanging
import RealRooted.Hadamard.SchurSzegoStrict

/-!
# Strict interlacing of factorial compressions of real-rooted polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "factorial-compression"
formalized = "2026-10-09"
tags = []
references = [
  "Zhang2026SeparableInterlacing",
]
authors = ["Zhanhe Zhang"]
years = [2026]

[[definitions]]
name = "RealRooted.FactorialCompression.compression"
module = "RealRooted.FactorialCompression.Basic"
label = "Factorial-compression operator"

[[definitions]]
name = "RealRooted.FactorialCompression.nextPolynomial"
module = "RealRooted.FactorialCompression.Basic"
label = "Degree-raising differential step"

[[definitions]]
name = "RealRooted.FactorialCompression.kernel"
module = "RealRooted.FactorialCompression.Basic"
label = "Degree-changing kernel"

[[theorems]]
name = "RealRooted.FactorialCompression.compression_nextPolynomial_strictInterl"
module = "RealRooted.FactorialCompression.DegreeChanging"
label = "Compressions of p and (x + a)p + xp' strictly interlace and have simple negative roots"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_schurSzegoComp_of_roots_neg"
module = "RealRooted.Hadamard.SchurSzegoStrict"
label = "Schur–Szegő composition with a negative-rooted multiplier preserves strict interlacing"

[[theorems]]
name = "RealRooted.FactorialCompression.compression_one_nextPolynomial_strictInterl"
module = "RealRooted.FactorialCompression.DegreeChanging"
label = "Level one with a = (N + 2)/2: the compressions strictly interlace"

[[theorems]]
name = "RealRooted.FactorialCompression.compression_eq_schurSzegoComp"
module = "RealRooted.FactorialCompression.Compression"
label = "Compression is a Schur–Szegő composition"

[[theorems]]
name = "RealRooted.FactorialCompression.strictInterl_commonKernel_kernel"
module = "RealRooted.FactorialCompression.Kernel"
label = "The common kernel strictly interlaces the degree-changing kernel"
-->

<!-- realrooted-catalog-content -->
# Strict interlacing of factorial compressions of real-rooted polynomials

Factorial compression and the adjacent differential step $p\mapsto(x+a)p+xp'$ map a polynomial
with negative roots to two polynomials with simple negative roots that strictly interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; common roots are allowed unless stated. For integers
$N\ge1$ and $0\le\ell\le N$, the *level-$\ell$ factorial compression* of a polynomial $p$ is
$$
T_{N,\ell}\,p=\sum_{k\le N,\ 2k\le N+\ell}\frac{(N-k)!}{(N+\ell-2k)!}\,p_k\,x^k,
$$
where $p_k$ is the coefficient of $x^k$ in $p$. For $a\in\mathbb R$, put $S_ap=(x+a)p+xp'$.

**Theorem (factorial compression).** Let $N\ge1$, $0\le\ell\le N$ and $a>0$. Let $p$ be a
real-rooted polynomial of degree $N$ with positive leading coefficient and only negative roots,
which may be repeated. Then $T_{N,\ell}\,p$ and $T_{N+1,\ell}\,S_ap$ have degrees
$\lfloor(N+\ell)/2\rfloor$ and $\lfloor(N+\ell+1)/2\rfloor$, positive leading coefficients and
simple negative roots, and
$$
T_{N,\ell}\,p\ll T_{N+1,\ell}\,S_ap
$$
with no common root.

**Corollary (level one).** For $N\ge1$ and $p$ as above, let $q=S_{(N+2)/2}\,p$. Then
$T_{N,1}\,p$ and $T_{N+1,1}\,q$ have the properties of the theorem; in particular
$T_{N,1}\,p\ll T_{N+1,1}\,q$ with no common root.

**Proposition (Schur–Szegő).** Let $n\ge1$ and let $Q$ be real-rooted of degree $n$ with positive
leading coefficient and only negative roots. Let $f\ll g$ have positive leading coefficients,
degrees at most $n$ and no common root. Then $f*_nQ\ll g*_nQ$ with no common root, where
$*_n$ is the Schur–Szegő composition of degree $n$.

**Proposition (kernel).** For every polynomial $p$,
$$
T_{N,\ell}\,p=\frac{N!}{(N+\ell)!}\;h_{N+\ell}*_Np,\qquad
h_r=\sum_{j\le r/2}\frac{r!}{j!\,(r-2j)!}\,x^j.
$$
Let $m=N+\ell\ge2$, $N\ge1$, $\ell\le N$ and $a>0$, and put
$$
K_{N,\ell,a}=\alpha\,h_m+\bigl(\beta x-\tfrac14\bigr)h_{m-1},\quad
\alpha=\tfrac14+\tfrac{a(N+1)}{m(m+1)},\quad
\beta=(N-\ell+1)\Bigl(\tfrac12+\tfrac{a}{m+1}\Bigr).
$$
Then $h_m\ll K_{N,\ell,a}$ with no common root, and all roots of $K_{N,\ell,a}$ are negative.

## Proof

Put $m=N+\ell$ and $U=h_m*_Np$, a positive multiple of $T_{N,\ell}\,p$. The compression
$T_{N+1,\ell}\,S_ap$ is a positive multiple of $W+xV$ with $W=K_{N,\ell,a}*_Np$ and
$V=h_{m-1}*_Np$. The kernel proposition and the Schur–Szegő proposition give $U\ll W$ with
no common root. Since $V=U-\tfrac2m\,xU'$, the polynomial $W+xV$ has the sign required by a
root-sign criterion at every root of $U$, and the criterion gives $U\ll W+xV$.

## References

See [@Zhang2026SeparableInterlacing]. The case $\ell=1$ is the normalization used there for
separable permutations. The Lean development follows a formalization by yyou59548-design.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.FactorialCompression` and
`RealRooted.Hadamard.SchurSzegoStrict`.
-/
