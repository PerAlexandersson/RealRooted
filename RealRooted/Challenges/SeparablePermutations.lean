import RealRooted.SeparablePermutations.Identification
import RealRooted.SeparablePermutations.Interlacing

/-!
# Descent polynomials of separable permutations: strict interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "separable-permutations"
authors = ["Zhanhe Zhang", "Fu", "Lin", "Zeng"]
years = [2016, 2026]

[[definitions]]
name = "RealRooted.SeparablePermutations.auxPolynomial"
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
label = "Consecutive descent polynomials S_n, S_{n+1} strictly interlace without common root"
headline = true

[[theorems]]
name = "RealRooted.SeparablePermutations.strictInterl_gammaPolynomial"
module = "RealRooted.SeparablePermutations.Interlacing"
label = "Consecutive gamma-polynomials Γ_n, Γ_{n+1} strictly interlace without common root"

[[theorems]]
name = "RealRooted.SeparablePermutations.strictInterl_auxPolynomial"
module = "RealRooted.SeparablePermutations.Basic"
label = "Consecutive auxiliary polynomials B_N, B_{N+1} strictly interlace"

[[theorems]]
name = "RealRooted.SeparablePermutations.hasSimpleRoots_descentPolynomial"
module = "RealRooted.SeparablePermutations.Interlacing"
label = "The descent polynomials S_n have simple roots"

[[theorems]]
name = "RealRooted.SeparablePermutations.strictInterl_descentEnumerator"
module = "RealRooted.SeparablePermutations.Identification"
label = "Zhang: descent polynomials of separable permutations strictly interlace"
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

A permutation is *separable* if it avoids the patterns $2413$ and $3142$.  Let
$S_n(t) = \sum_\pi t^{\operatorname{des}\pi}$ be the descent enumerator of the separable
permutations of $[n]$.  Its gamma-vector is given by a convolution recurrence of Fu, Lin
and Zeng, and $S_n(t) = (1+t)^{n-1}\,\Gamma_n\bigl(t/(1+t)^2\bigr)$ for the gamma-polynomial
$\Gamma_n$.  Zhang represents $\Gamma_{N+2}$ as a factorial compression of the polynomial
$B_N$, where $B_0 = 1$ and $B_{N+1} = (x + \tfrac{N+2}{2})B_N + x B_N'$.

**Theorem.** For $n \ge 2$, the polynomials $\Gamma_n$ and $\Gamma_{n+1}$ strictly interlace
and have no common root, and so do $S_n$ and $S_{n+1}$.  All roots of $S_n$ are simple and
negative, and $S_n$ has degree $n-1$.

**What is formalized.**  Everything, for the permutation statistic itself.  The identification
of $S_n$ with the descent enumerator of the separable permutations
(`descentEnumerator_eq_descentPolynomial`) is proved: the separable permutations decompose
uniquely into direct and skew sums, which gives the cubic recurrence
$S = z + (1+t)zS + tzS^2 + tS^3$ for the enumerator, while Zhang's closed form satisfies Fu, Lin
and Zeng's cubic $G = w + wG + xwG^2 + xG^3$ for the gamma-polynomials (proved with a general
Lagrange–Bürmann inversion theorem), which the gamma substitution carries to the same recurrence.
Hence Theorem 1.1 of Zhang's preprint holds for separable permutations
(`strictInterl_descentEnumerator`).

## Proof idea

The polynomials $B_N$ form a strict interlacing family by the strict derivative-lag recurrence.
The level-one factorial compression theorem applies to the pair $B_N$, $B_{N+1}$ and gives
strict interlacing of $\Gamma_{N+2}$ and $\Gamma_{N+3}$ (the pair $\Gamma_2 = 1$,
$\Gamma_3 = 1 + 2x$ is explicit).  The adjacent-degree gamma lifting then transfers strict
interlacing to $S_n$ and $S_{n+1}$: the two inverse branches of $\rho \mapsto \rho/(1+\rho)^2$
carry a common root of the descent polynomials to a common root of the gamma-polynomials, and
the central root $-1$ is excluded by the evaluation formula for the gamma transform.

## References

Z. Zhang, *A Factorial Compression Theorem for Strict Interlacing* (2026),
[SSRN preprint](https://ssrn.com/abstract=7510941); S. Fu, Z. Lin and J. Zeng, “On two
unimodal descent polynomials,” [arXiv:1507.05184](https://arxiv.org/abs/1507.05184).  The Lean
development follows the draft formalization of PR #1132 by yyou59548-design.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.SeparablePermutations` and
`RealRooted.FactorialCompression`.
-/
