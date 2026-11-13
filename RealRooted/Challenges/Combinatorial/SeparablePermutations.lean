module

import RealRooted.FactorialCompression.DegreeChanging
import RealRooted.Hadamard.SchurSzegoStrict
import RealRooted.SeparablePermutations.Gamma
import RealRooted.SeparablePermutations.Identification
import RealRooted.SeparablePermutations.Interlacing

/-!
# Descent polynomials of separable permutations

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "separable-permutations"
formalized = "2026-10-09"
tags = []
references = [
  "Zhang2026SeparableInterlacing",
  "FuLinZeng2018",
]
authors = ["Zhanhe Zhang", "Fu", "Lin", "Zeng"]
years = [2018, 2026]
symcat = ["separableDescentRealRooted"]

[[definitions]]
name = "RealRooted.SeparablePermutations.compressionSourcePolynomial"
module = "RealRooted.SeparablePermutations.Basic"
label = "Auxiliary polynomials B_N with B_{N+1} = (x + (N+2)/2) B_N + x B_N'"

[[definitions]]
name = "RealRooted.SeparablePermutations.gammaPolynomial"
module = "RealRooted.SeparablePermutations.Gamma"
label = "Gamma-polynomials Γ_n through the factorial-compression representation"

[[definitions]]
name = "RealRooted.SeparablePermutations.descentPolynomial"
module = "RealRooted.SeparablePermutations.Gamma"
label = "Descent polynomials S_n = (1 + t)^{n-1} Γ_n(t/(1+t)^2)"

[[definitions]]
name = "Equiv.Perm.IsSeparable"
module = "RealRooted.Mathlib.Combinatorics.Enumerative.Separable"
label = "Separable permutations: direct and skew sums, equivalently avoiders of 2413 and 3142"

[[definitions]]
name = "RealRooted.SeparablePermutations.descentEnumerator"
module = "RealRooted.SeparablePermutations.Enumerator"
label = "Descent enumerator of the separable permutations"

[[theorems]]
name = "RealRooted.SeparablePermutations.strictInterl_descentPolynomial"
module = "RealRooted.SeparablePermutations.Interlacing"
label = "Consecutive descent polynomials S_n, S_{n+1} interlace without common root"

[[theorems]]
name = "RealRooted.SeparablePermutations.strictInterl_gammaPolynomial"
module = "RealRooted.SeparablePermutations.Interlacing"
label = "Consecutive gamma-polynomials Γ_n, Γ_{n+1} interlace without common root"

[[theorems]]
name = "RealRooted.SeparablePermutations.strictInterl_compressionSourcePolynomial"
module = "RealRooted.SeparablePermutations.Basic"
label = "Consecutive auxiliary polynomials B_N, B_{N+1} interlace without a common root"

[[theorems]]
name = "RealRooted.SeparablePermutations.hasSimpleRoots_descentPolynomial"
module = "RealRooted.SeparablePermutations.Interlacing"
label = "The descent polynomials S_n have simple roots"

[[theorems]]
name = "RealRooted.SeparablePermutations.roots_descentPolynomial_neg"
module = "RealRooted.SeparablePermutations.Interlacing"
label = "All roots of S_n are negative for n ≥ 2"

[[theorems]]
name = "RealRooted.SeparablePermutations.natDegree_descentPolynomial"
module = "RealRooted.SeparablePermutations.Gamma"
label = "S_n has degree n − 1 for n ≥ 1"

[[theorems]]
name = "RealRooted.SeparablePermutations.strictInterl_descentEnumerator"
module = "RealRooted.SeparablePermutations.Identification"
label = "Zhang: descent polynomials of separable permutations interlace"
headline = true

[[theorems]]
name = "RealRooted.SeparablePermutations.descentEnumerator_eq_descentPolynomial"
module = "RealRooted.SeparablePermutations.Identification"
label = "Fu–Lin–Zeng / Zhang: the descent enumerator equals S_{n+1}"

[[theorems]]
name = "RealRooted.SeparablePermutations.gammaPolynomial_cubic"
module = "RealRooted.SeparablePermutations.GammaCubic"
label = "Fu–Lin–Zeng's cubic for the gamma-polynomials (via Lagrange inversion)"

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
# Descent polynomials of separable permutations

For $n\ge2$ the descent polynomials of the separable permutations of $[n]$ and $[n+1]$ interlace
and have no common root; the same holds for their gamma-polynomials. The proof transfers
interlacing through factorial compression, which maps polynomials with negative roots to
strictly interlacing pairs.

## Results

A permutation is *separable* if it avoids $2413$ and
$3142$. Let $S_n(t)=\sum_\pi t^{\operatorname{des}\pi}$ over the separable permutations $\pi$
of $[n]$. Fu, Lin and Zeng [@FuLinZeng2018] give the gamma-polynomials $\Gamma_n$ of $S_n$:
$$
S_n(t)=(1+t)^{n-1}\,\Gamma_n\bigl(t/(1+t)^2\bigr).
$$
For integers $N\ge1$ and $0\le\ell\le N$, the *level-$\ell$ factorial compression* of
$p=\sum_kp_kx^k$ is
$$
C_{N,\ell}\,p=\sum_{k\le N,\ 2k\le N+\ell}\frac{(N-k)!}{(N+\ell-2k)!}\,p_k\,x^k ,
$$
and for $a\in\mathbb R$ we put $E_ap=(x+a)p+xp'$. Zhang [@Zhang2026SeparableInterlacing]
represents $\Gamma_{N+2}$ as the level-one factorial compression of $B_N$, where $B_0=1$ and
$B_{N+1}=E_{(N+2)/2}B_N$; here $\Gamma_0=0$, $\Gamma_1=1$, $\Gamma_2=1$ and $\Gamma_3=1+2x$.

**Theorem (Zhang).** For $n\ge2$:

- $S_n\ll S_{n+1}$ without a common root;
- $\Gamma_n\ll\Gamma_{n+1}$ without a common root;
- $S_n$ has only simple negative roots, and $\deg S_n=n-1$.

Also $B_N\ll B_{N+1}$ without a common root, for $N\ge0$.

**Theorem (identification).** The descent enumerator of the separable permutations of $[n+1]$
equals $S_{n+1}$ as defined through $\Gamma_{n+1}$, for $n\ge0$. Hence $S_n\ll S_{n+1}$ for the
permutation statistic. The gamma-polynomials satisfy, for $n\ge2$ and $\Gamma_0=0$,
$$
\Gamma_n=\Gamma_{n-1}+x\sum_{i+j=n-1}\Gamma_i\Gamma_j+x\sum_{i+j+l=n}\Gamma_i\Gamma_j\Gamma_l ,
$$
that is, $G=\sum_n\Gamma_nw^n$ satisfies $G=w+wG+xwG^2+xG^3$ [@FuLinZeng2018].

**Theorem (factorial compression).** [@Zhang2026SeparableInterlacing] Let $N\ge1$,
$0\le\ell\le N$ and $a>0$, and let $p$ be a real-rooted polynomial of degree $N$ with positive
leading coefficient and only negative roots, which may be repeated. Then $C_{N,\ell}\,p$ and
$C_{N+1,\ell}\,E_ap$ have degrees $\lfloor(N+\ell)/2\rfloor$ and $\lfloor(N+\ell+1)/2\rfloor$
and simple negative roots, and $C_{N,\ell}\,p\ll C_{N+1,\ell}\,E_ap$ with no common root.

The compression is a Schur–Szegő composition with an explicit kernel,
$C_{N,\ell}\,p=\frac{N!}{(N+\ell)!}\,h_{N+\ell}*_Np$ with
$h_r=\sum_{j\le r/2}\frac{r!}{j!\,(r-2j)!}x^j$, and Schur–Szegő composition with a polynomial
with only negative roots preserves interlacing without common roots.

## Proof

The enumerators $S_n$ satisfy the cubic recurrence
$S_n=(1+t)S_{n-1}+t\sum_{i+j=n-1}S_iS_j+t\sum_{i+j+l=n}S_iS_jS_l$, from the decomposition of a
separable permutation into direct and skew sums, and the gamma substitution carries the cubic
for $\Gamma_n$, proved by Lagrange inversion, to this one. Interlacing holds for $B_N$ by the
derivative-lag recurrence, and the factorial compression theorem with $\ell=1$ and
$a=(N+2)/2$ transfers it to $\Gamma_{N+2}$ and $\Gamma_{N+3}$. The gamma substitution then
transfers it to $S_n$ and $S_{n+1}$: the two branches of $\rho\mapsto\rho/(1+\rho)^2$ carry a
common root of the descent polynomials to a common root of the gamma-polynomials, and the root
$-1$ is excluded by evaluating the gamma transform there.

## References

- [@Zhang2026SeparableInterlacing]
- [@FuLinZeng2018]
<!-- /realrooted-catalog-content -->
-/
