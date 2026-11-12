module

import RealRooted.SeparablePermutations.Gamma
import RealRooted.SeparablePermutations.Identification
import RealRooted.SeparablePermutations.Interlacing

/-!
# Descent polynomials of separable permutations: strict interlacing

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
-->

<!-- realrooted-catalog-content -->
# Descent polynomials of separable permutations

For $n\ge2$ the descent polynomials of the separable permutations of $[n]$ and $[n+1]$ interlace
and have no common root; the same holds for their gamma-polynomials.

## Results

We write $f\ll g$ if $f$ interlaces $g$. A permutation is *separable* if it avoids $2413$ and
$3142$. Let $S_n(t)=\sum_\pi t^{\operatorname{des}\pi}$ over the separable permutations $\pi$
of $[n]$. Fu, Lin and Zeng [@FuLinZeng2018] give the gamma-polynomials $\Gamma_n$ of $S_n$:
$$
S_n(t)=(1+t)^{n-1}\,\Gamma_n\bigl(t/(1+t)^2\bigr).
$$
Zhang [@Zhang2026SeparableInterlacing] represents $\Gamma_{N+2}$ as a factorial compression of
$B_N$, where $B_0=1$ and $B_{N+1}=(x+\tfrac{N+2}{2})B_N+xB_N'$; here $\Gamma_0=0$, $\Gamma_1=1$,
$\Gamma_2=1$ and $\Gamma_3=1+2x$.

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

## Proof

The enumerators $S_n$ satisfy the analogous cubic recurrence
$S_n=(1+t)S_{n-1}+t\sum_{i+j=n-1}S_iS_j+t\sum_{i+j+l=n}S_iS_jS_l$, from the decomposition of a
separable permutation into direct and skew sums. The gamma substitution carries the cubic for
$\Gamma_n$ to this one, and the cubic determines the sequence from $S_1=1$. The cubic for
$\Gamma_n$ is proved by Lagrange inversion.

Interlacing is proved first for $B_N$, from the derivative-lag recurrence. The factorial
compression transfers it to $\Gamma_{N+2},\Gamma_{N+3}$, and the gamma lifting to $S_n,S_{n+1}$:
the two branches of $\rho\mapsto\rho/(1+\rho)^2$ carry a common root of the descent polynomials
to a common root of the gamma-polynomials, and the root $-1$ is excluded by the evaluation
formula of the gamma transform.

## References

[@Zhang2026SeparableInterlacing; @FuLinZeng2018]. The Lean development follows a formalization
by yyou59548-design. See also the
[separable-descent example on symmetricfunctions.com](sf:separableDescentRealRooted).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.SeparablePermutations` and
`RealRooted.FactorialCompression`.
-/
