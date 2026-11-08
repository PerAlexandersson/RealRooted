module

import RealRooted.Laguerre.Favard
import RealRooted.Laguerre.Orthogonality.Integral
import RealRooted.Laguerre.Roots
import RealRooted.Laguerre.FiniteCombinations
import RealRooted.Laguerre.GeneralizedBell

/-!
# Generalized Laguerre polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "laguerre-polynomials"
formalized = "2026-09-07"
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
headline = true

[[theorems]]
name = "RealRooted.generalizedLaguerre_roots_neg"
module = "RealRooted.Laguerre.Roots"
label = "Generalized Laguerre polynomials have negative roots for α > -1"

[[theorems]]
name = "RealRooted.generalizedLaguerre_hasSimpleRoots"
module = "RealRooted.Laguerre.Roots"
label = "Generalized Laguerre polynomials have simple roots"

[[theorems]]
name = "RealRooted.generalizedLaguerre_strictInterl_succ"
module = "RealRooted.Laguerre.Roots"
label = "Consecutive generalized Laguerre polynomials interlace"

[[theorems]]
name = "RealRooted.generalizedLaguerre_satisfiesFavardRecurrence"
module = "RealRooted.Laguerre.Favard"
label = "Generalized Laguerre polynomials satisfy a Favard recurrence"

[[theorems]]
name = "RealRooted.generalizedLaguerre_integral_orthogonal"
module = "RealRooted.Laguerre.Orthogonality.Integral"
label = "Generalized Laguerre polynomials are orthogonal on the half-line"

[[definitions]]
name = "RealRooted.laguerreCombination"
module = "RealRooted.Laguerre.GeneralizedBell"
label = "A fixed bandwidth-K combination of consecutive monic Laguerre polynomials"

[[definitions]]
name = "RealRooted.laguerreAuxiliary"
module = "RealRooted.Laguerre.GeneralizedBell"
label = "The auxiliary polynomial Σ (-1)^j γ_j (X)_{K-j}"

[[theorems]]
name = "RealRooted.laguerreCombination_splits_simple_roots_pos_of_auxiliary"
module = "RealRooted.Laguerre.GeneralizedBell"
label = "Auxiliary roots below α + 1 give a combination with simple positive roots"
headline = true

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
headline = true

[[theorems]]
name = "RealRooted.laguerreCombinationOne_one_splits_simple_roots_pos"
module = "RealRooted.Laguerre.FiniteCombinations"
label = "The case γ = 1 for α > 0"
-->

<!-- realrooted-catalog-content -->
# Generalized Laguerre polynomials

The library uses the monic, sign-reversed normalization

$$
P_n^{(\alpha)}(x) = n!\, L_n^{(\alpha)}(-x)
= \sum_k \binom{n}{k} (\alpha+k+1)_{n-k}\, x^k,
$$

so that the zeros are nonpositive. For $\alpha \geq -1$:

- every $P_n^{(\alpha)}$ has only real, simple zeros, and they are strictly negative
  when $\alpha > -1$;
- consecutive polynomials interlace;
- the family satisfies a Favard three-term recurrence.

For $\alpha > -1$ the family is also orthogonal on the positive half-line:

$$
\int_0^\infty P_m^{(\alpha)}(-x)\, P_n^{(\alpha)}(-x)\, x^\alpha e^{-x}\, dx = 0
  \qquad (m \neq n).
$$

## Finite combinations of monic Laguerre polynomials

Let $\ell_n^{(\alpha)}$ denote the classical monic Laguerre polynomial,
$(-1)^nn!\,L_n^{(\alpha)}$, whose roots are positive. For a fixed bandwidth $K$ and
coefficients $\gamma_0=1,\gamma_1,\dots,\gamma_K$, consider the combination
$$
\sum_{j=0}^K\gamma_j\,\ell_{n-j}^{(\alpha)} \qquad(K\le n)
$$
and the auxiliary polynomial $\sum_{j=0}^K(-1)^j\gamma_j\,(x)_{K-j}$, with $(x)_m$ the rising
factorial. If $\alpha>-1$, the auxiliary polynomial splits and all its roots are below
$\alpha+1$, then the combination has only simple, positive roots. The proof iterates the
first-order Laguerre raising step $p\mapsto(x+a)p+xp'$, which preserves simple real roots and
interlaces its input (a generalized Bell iteration).

In bandwidth one, $\ell_n^{(\alpha)}+\gamma\,\ell_{n-1}^{(\alpha)}$ has simple positive
roots whenever $\alpha>-1$ and $\gamma<\alpha+1$, which includes $\gamma=-1$ and, for
$\alpha>0$, $\gamma=1$. This is the bandwidth-one case of Theorem 1.3 of A. J. Durán, *Zeros
of linear combinations of Laguerre polynomials* (arXiv:2507.22425).

## References

See [@Szego1939, Ch. V]. The general three-term theory is on the
[Favard page](/RealRooted/theorems/favard/). The combination theorem is
A. J. Durán, *Zeros of linear combinations of Laguerre polynomials*, Theorem 1.3,
[arXiv:2507.22425](https://arxiv.org/abs/2507.22425).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.Laguerre`.
-/
