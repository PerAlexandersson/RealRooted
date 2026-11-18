module

import RealRooted.FactorialCompression.Basic
import RealRooted.FactorialCompression.Compression
import RealRooted.FactorialCompression.DegreeChanging
import RealRooted.Mathlib.Combinatorics.Enumerative.Separable
import RealRooted.SeparablePermutations.Enumerator
import RealRooted.SeparablePermutations.Gamma
import RealRooted.SeparablePermutations.GammaCubic
import RealRooted.SeparablePermutations.Identification
import RealRooted.SeparablePermutations.Interlacing

/-!
# Descent polynomials of separable permutations

<!-- realrooted-catalog
version = 1
kind = "conjecture"
conjecture = "Fu–Lin–Zeng (2018), Conjecture 5.2, separable permutations"
section = "theorems"
slug = "separable-permutations"
formalized = "2026-10-09"
references = [
  "Zhang2026SeparableInterlacing",
  "FuLinZeng2018",
]
authors = ["Fu", "Lin", "Zeng", "Zhanhe Zhang"]
years = [2018, 2026]
symcat = ["separableDescentRealRooted"]

[[definitions]]
name = "Equiv.Perm.IsSeparable"
module = "RealRooted.Mathlib.Combinatorics.Enumerative.Separable"
label = "Separable permutations: direct and skew sums, equivalently avoiders of 2413 and 3142"

[[definitions]]
name = "RealRooted.SeparablePermutations.descentEnumerator"
module = "RealRooted.SeparablePermutations.Enumerator"
label = "Descent enumerator of the separable permutations"

[[definitions]]
name = "RealRooted.SeparablePermutations.gammaPolynomial"
module = "RealRooted.SeparablePermutations.Gamma"
label = "Gamma-polynomials $Γ_n$ through the factorial-compression representation"

[[definitions]]
name = "RealRooted.SeparablePermutations.descentPolynomial"
module = "RealRooted.SeparablePermutations.Gamma"
label = "Descent polynomials $S_n = (1 + t)^{n-1} Γ_n(t/(1 + t)^2)$"

[[definitions]]
name = "RealRooted.FactorialCompression.compression"
module = "RealRooted.FactorialCompression.Basic"
label = "Factorial-compression operator"

[[theorems]]
objects = ["Descent polynomials of separable permutations"]
property = "interlacing"
name = "RealRooted.SeparablePermutations.strictInterl_descentEnumerator"
module = "RealRooted.SeparablePermutations.Identification"
label = "Zhang: consecutive descent polynomials of separable permutations strictly interlace"
headline = true

[[theorems]]
name = "RealRooted.SeparablePermutations.hasSimpleRoots_descentPolynomial"
module = "RealRooted.SeparablePermutations.Interlacing"
label = "The descent polynomials $S_n$ have simple roots"

[[theorems]]
name = "RealRooted.SeparablePermutations.roots_descentPolynomial_neg"
module = "RealRooted.SeparablePermutations.Interlacing"
label = "All roots of $S_n$ are negative for $n ≥ 2$"

[[theorems]]
objects = ["Gamma polynomials of separable permutations"]
property = "interlacing"
name = "RealRooted.SeparablePermutations.strictInterl_gammaPolynomial"
module = "RealRooted.SeparablePermutations.Interlacing"
label = "Consecutive gamma-polynomials $Γ_n$, $Γ_{n+1}$ interlace without common root"

[[theorems]]
name = "RealRooted.SeparablePermutations.descentEnumerator_eq_descentPolynomial"
module = "RealRooted.SeparablePermutations.Identification"
label = "Fu–Lin–Zeng / Zhang: the descent enumerator equals $S_{n+1}$"

[[theorems]]
name = "RealRooted.SeparablePermutations.gammaPolynomial_cubic"
module = "RealRooted.SeparablePermutations.GammaCubic"
label = "Fu–Lin–Zeng's cubic for the gamma-polynomials"

[[theorems]]
name = "RealRooted.FactorialCompression.compression_nextPolynomial_strictInterl"
module = "RealRooted.FactorialCompression.DegreeChanging"
label = "Compressions of p and (x + a)p + xp′ strictly interlace and have simple negative roots"

[[theorems]]
name = "RealRooted.FactorialCompression.compression_eq_schurSzegoComp"
module = "RealRooted.FactorialCompression.Compression"
label = "Factorial compression is a Schur–Szegő composition"
-->

<!-- realrooted-catalog-content -->
# Descent polynomials of separable permutations

Fu, Lin and Zeng conjectured that the descent polynomials of separable permutations are
real-rooted. Zhang proved more: for $n\ge2$, the descent polynomials for $n$ and $n+1$ have
simple negative roots and strictly interlace, and so do their gamma-polynomials.

## Results

A permutation is *separable* if it avoids $2413$ and $3142$. Let
$S_n(t)=\sum_\pi t^{\operatorname{des}\pi}$ over the separable permutations $\pi$ of $[n]$. Fu,
Lin and Zeng [@FuLinZeng2018] showed that $S_n$ is gamma-positive,
$$
S_n(t)=(1+t)^{n-1}\,\Gamma_n\bigl(t/(1+t)^2\bigr),
$$
and that $G=\sum_n\Gamma_nw^n$, with $\Gamma_0=0$, satisfies $G=w+wG+xwG^2+xG^3$.

**Theorem (Zhang).** [@Zhang2026SeparableInterlacing, Thms. 1.1–1.2] For $n\ge2$, $S_n$ has
$n-1$ simple negative roots, $S_n\ll S_{n+1}$, and the two polynomials have no common root. The
same holds for $\Gamma_n$ and $\Gamma_{n+1}$. This proves the separable part of
[@FuLinZeng2018, Conj. 5.2].

For integers $N\ge1$ and $0\le\ell\le N$, the *level-$\ell$ factorial compression* of
$p=\sum_kp_kx^k$ is
$$
C_{N,\ell}\,p=\sum_{k\le N,\ 2k\le N+\ell}\frac{(N-k)!}{(N+\ell-2k)!}\,p_k\,x^k .
$$

**Theorem (factorial compression).** Let $N\ge1$, $0\le\ell\le N$ and $a>0$, and let $p$ have
degree $N$, positive leading coefficient and only negative roots, possibly repeated. Then
$C_{N,\ell}\,p$ and $C_{N+1,\ell}\bigl((x+a)p+xp'\bigr)$ have simple negative roots, strictly
interlace and have no common root. Zhang's case is $\ell=1$, $a=(N+2)/2$
[@Zhang2026SeparableInterlacing, Thm. 4.1].

## Proof

Zhang writes $\Gamma_{N+2}=C_{N,1}B_N$, where $B_0=1$ and
$B_{N+1}=\bigl(x+\tfrac{N+2}2\bigr)B_N+xB_N'$, so the compression theorem gives
$\Gamma_n\ll\Gamma_{n+1}$. The compression is a Schur–Szegő composition with an explicit kernel,
and Schur–Szegő composition with a negative-rooted polynomial preserves strict interlacing. The
substitution $t\mapsto t/(1+t)^2$ carries the interlacing to $S_n\ll S_{n+1}$.

## References

[@Zhang2026SeparableInterlacing, Thms. 1.1, 1.2 and 4.1]; [@FuLinZeng2018, Conj. 5.2].
<!-- /realrooted-catalog-content -->
-/
