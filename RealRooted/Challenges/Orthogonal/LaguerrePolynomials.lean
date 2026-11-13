module

import RealRooted.Laguerre.Favard
import RealRooted.Laguerre.Orthogonality.Integral
import RealRooted.Laguerre.Roots
import RealRooted.Laguerre.FiniteCombinations
import RealRooted.Laguerre.GeneralizedBell

/-!
# Generalized Laguerre polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "laguerre-polynomials"
formalized = "2026-09-07"
authors = ["Szegő", "Durán"]
tags = []
references = [
  "Szego1939",
]

[[definitions]]
name = "Polynomial.generalizedLaguerre"
module = "RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic"
label = "Generalized Laguerre polynomials"

[[theorems]]
name = "RealRooted.generalizedLaguerre_splits"
module = "RealRooted.Laguerre.Roots"
label = "Generalized Laguerre polynomials are real-rooted"

[[theorems]]
name = "RealRooted.generalizedLaguerre_roots_neg"
module = "RealRooted.Laguerre.Roots"
label = "Roots are negative for α > -1"

[[theorems]]
name = "RealRooted.generalizedLaguerre_hasSimpleRoots"
module = "RealRooted.Laguerre.Roots"
label = "Generalized Laguerre polynomials have simple roots"

[[theorems]]
name = "RealRooted.generalizedLaguerre_strictInterl_succ"
module = "RealRooted.Laguerre.Roots"
label = "Consecutive generalized Laguerre polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.generalizedLaguerre_satisfiesFavardRecurrence"
module = "RealRooted.Laguerre.Favard"
label = "Monic Laguerre polynomials satisfy a Favard recurrence"

[[theorems]]
name = "RealRooted.generalizedLaguerre_integral_orthogonal"
module = "RealRooted.Laguerre.Orthogonality.Integral"
label = "Generalized Laguerre polynomials are orthogonal on the half-line"

[[definitions]]
name = "RealRooted.laguerreCombination"
module = "RealRooted.Laguerre.GeneralizedBell"
label = "A fixed bandwidth-K combination of consecutive monic Laguerre polynomials"

[[definitions]]
name = "RealRooted.laguerrePochhammerSum"
module = "RealRooted.Laguerre.GeneralizedBell"
label = "The auxiliary polynomial Σ (-1)^j γ_j (X)_{K-j}"

[[theorems]]
name = "RealRooted.laguerreCombination_splits_simple_roots_pos"
module = "RealRooted.Laguerre.GeneralizedBell"
label = "Auxiliary roots below α + 1 give a combination with simple positive roots"

[[theorems]]
name = "RealRooted.laguerreRaisingSteps_splits_simple_roots_neg"
module = "RealRooted.Laguerre.GeneralizedBell"
label = "Iterated Laguerre raising steps preserve simple negative roots"

[[theorems]]
name = "RealRooted.strictInterl_and_hasSimpleRoots_laguerreRaisingStep"
module = "RealRooted.Laguerre.GeneralizedBell"
label = "A raising step interlaces its input and has simple roots"

[[theorems]]
name = "RealRooted.laguerreCombinationOne_splits_simple_roots_pos"
module = "RealRooted.Laguerre.FiniteCombinations"
label = "For γ < α + 1, L_n + γ L_{n-1} has simple positive roots"

[[theorems]]
name = "RealRooted.laguerreCombinationOne_one_splits_simple_roots_pos"
module = "RealRooted.Laguerre.FiniteCombinations"
label = "The case γ = 1 for α > 0"
-->

<!-- realrooted-catalog-content -->
# Generalized Laguerre polynomials

The generalized Laguerre polynomials are real-rooted with simple roots, and consecutive ones
interlace. Suitable finite combinations of consecutive Laguerre polynomials keep simple
positive roots.

## Results

We use the monic, sign-reversed normalization
$$
P_n^{(\alpha)}(x) = n!\, L_n^{(\alpha)}(-x)
= \sum_k \binom{n}{k} (\alpha+k+1)_{n-k}\, x^k ,
$$
with $(y)_m$ the rising factorial, so that the roots are nonpositive.

**Theorem (roots and interlacing).** For $\alpha \ge -1$ and $n\ge0$, $P_n^{(\alpha)}$ is
real-rooted with simple roots and $P_n^{(\alpha)} \ll P_{n+1}^{(\alpha)}$. For $\alpha > -1$ all
roots are strictly negative.

For every real $\alpha$ the family satisfies a [Favard](rr:favard) three-term recurrence. For
$\alpha > -1$ and $m \neq n$,
$$
\int_0^\infty P_m^{(\alpha)}(-x)\, P_n^{(\alpha)}(-x)\, x^\alpha e^{-x}\, dx = 0.
$$

**Theorem (finite combinations).** Let $\ell_n^{(\alpha)}=(-1)^nn!\,L_n^{(\alpha)}$ be the
classical monic Laguerre polynomial, with positive roots. Let $K\le n$, $\gamma_0=1$,
$\gamma_1,\dots,\gamma_K$ real, and
$$
Q(x)=\sum_{j=0}^K(-1)^j\gamma_j\,(x)_{K-j}.
$$
If $\alpha>-1$, $Q$ is real-rooted and all its roots are below $\alpha+1$, then
$\sum_{j=0}^K\gamma_j\,\ell_{n-j}^{(\alpha)}$ is real-rooted with simple positive roots.

For $K=1$ and $n\ge1$: if $\alpha>-1$ and $\gamma<\alpha+1$, then
$\ell_n^{(\alpha)}+\gamma\,\ell_{n-1}^{(\alpha)}$ has simple positive roots. This includes
$\gamma=-1$ and, for $\alpha>0$, $\gamma=1$.

**Proposition (raising step).** For $a>0$ let $p\mapsto(x+a)p+xp'$. Applied to a monic
real-rooted polynomial $p$ of degree at least $1$ with simple roots, nonnegative coefficients
and $p(0)\ne0$, it gives a polynomial with simple roots that $p$ interlaces. Iterating steps
with positive parameters preserves simple negative roots.

## References

- [@Szego1939, Ch. V].
- See also A. J. Durán, *Zeros of linear combinations of Laguerre polynomials*,
  [arXiv:2507.22425](https://arxiv.org/abs/2507.22425), Theorem 1.3.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.Laguerre`.
-/
