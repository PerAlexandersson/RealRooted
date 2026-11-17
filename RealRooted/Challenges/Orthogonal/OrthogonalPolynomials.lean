module

import RealRooted.Chebyshev.Levels
import RealRooted.Favard
import RealRooted.Favard.Orthogonality
import RealRooted.Favard.Recurrence
import RealRooted.Hermite.Orthogonality.Integral
import RealRooted.Hermite.Roots
import RealRooted.Hypergeometric.ThreeFTwo
import RealRooted.Jacobi
import RealRooted.Jacobi.CoefficientFamily
import RealRooted.Jacobi.Markoff
import RealRooted.Jacobi.Orthogonality.Integral
import RealRooted.Laguerre.GeneralizedBell
import RealRooted.Laguerre.Orthogonality.Integral
import RealRooted.Laguerre.Roots
import RealRooted.Legendre.Roots
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi

/-!
# Orthogonal polynomials and Favard's theorem

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "orthogonal-polynomials"
formalized = "2026-09-07"
references = [
  "Favard1935",
  {key = "Szego1939", at = "Chs. III–VI"},
  {key = "Duran2025x", at = "Thm. 1.3"},
]
authors = ["Jacobi", "Markoff", "Favard", "Szegő", "Lima", "Durán"]
years = [1859, 1886, 1935, 1939, 2023, 2025]

[[definitions]]
name = "RealRooted.SatisfiesFavardRecurrence"
module = "RealRooted.Favard.Recurrence"
label = "Favard three-term recurrence"

[[definitions]]
name = "RealRooted.SatisfiesFavardRecurrence.pairing"
module = "RealRooted.Favard.Orthogonality"
label = "The pairing ⟨p, q⟩ = L(pq) for the normalized moment functional L"

[[theorems]]
name = "RealRooted.SatisfiesFavardRecurrence.pairing_iIsOrtho"
module = "RealRooted.Favard.Orthogonality"
label = "Favard: a three-term recurrence family is orthogonal for a moment functional"
headline = true

[[theorems]]
name = "RealRooted.SatisfiesFavardRecurrence.pairing_posDef"
module = "RealRooted.Favard.Orthogonality"
label = "For positive β, the pairing is positive definite"

[[theorems]]
objects = ["Orthogonal polynomials"]
property = "interlacing"
name = "RealRooted.favardInterlacing"
module = "RealRooted.Favard"
label = "For positive β, consecutive Favard polynomials are real-rooted and interlace"
symcat = "favardInterlacing"

[[theorems]]
objects = ["Hermite polynomials"]
name = "RealRooted.hermiteReal_isRealRooted"
module = "RealRooted.Hermite.Roots"
label = "Hermite polynomials are real-rooted"

[[theorems]]
objects = ["Hermite polynomials"]
property = "interlacing"
name = "RealRooted.hermiteReal_strictInterl_succ"
module = "RealRooted.Hermite.Roots"
label = "Consecutive Hermite polynomials interlace"

[[theorems]]
objects = ["Hermite polynomials"]
property = "orthogonal"
name = "RealRooted.hermiteReal_integral_orthogonal"
module = "RealRooted.Hermite.Orthogonality.Integral"
label = "Hermite polynomials are orthogonal for the Gaussian weight"

[[theorems]]
objects = ["Generalized Laguerre polynomials"]
name = "RealRooted.generalizedLaguerre_splits"
module = "RealRooted.Laguerre.Roots"
label = "Generalized Laguerre polynomials are real-rooted"

[[theorems]]
objects = ["Generalized Laguerre polynomials"]
property = "interlacing"
name = "RealRooted.generalizedLaguerre_strictInterl_succ"
module = "RealRooted.Laguerre.Roots"
label = "Consecutive generalized Laguerre polynomials interlace"

[[theorems]]
objects = ["Generalized Laguerre polynomials"]
property = "orthogonal"
name = "RealRooted.generalizedLaguerre_integral_orthogonal"
module = "RealRooted.Laguerre.Orthogonality.Integral"
label = "Generalized Laguerre polynomials are orthogonal on the half-line"

[[theorems]]
name = "RealRooted.LaguerreCombination.isRealRootedIn_Ioi_and_hasSimpleRoots"
module = "RealRooted.Laguerre.GeneralizedBell"
label = "Durán: suitable combinations of consecutive Laguerre polynomials keep positive roots"

[[definitions]]
name = "Polynomial.shiftedJacobi"
module = "RealRooted.Mathlib.RingTheory.Polynomial.Jacobi"
label = "Shifted Jacobi polynomials"

[[theorems]]
objects = ["Jacobi polynomials"]
name = "RealRooted.shiftedJacobi_splits"
module = "RealRooted.Jacobi"
label = "Shifted Jacobi polynomials are real-rooted"

[[theorems]]
objects = ["Jacobi polynomials"]
property = "interlacing"
name = "RealRooted.shiftedJacobi_interlaces_succ"
module = "RealRooted.Jacobi"
label = "Consecutive shifted Jacobi polynomials interlace"

[[theorems]]
objects = ["Jacobi polynomials"]
property = "orthogonal"
name = "RealRooted.shiftedJacobi_integral_orthogonal"
module = "RealRooted.Jacobi.Orthogonality.Integral"
label = "Orthogonality on (0, 1) for the weight x^α (1 - x)^β"

[[theorems]]
name = "RealRooted.shiftedJacobi_isRoot_mem_Ioo"
module = "RealRooted.Jacobi"
label = "Every root of a shifted Jacobi polynomial lies in (0, 1)"

[[theorems]]
name = "RealRooted.strictMonoOn_shiftedJacobiMonicRoot_alpha"
module = "RealRooted.Jacobi.Markoff"
label = "Markoff: for β = 1 the roots increase strictly with α"

[[theorems]]
objects = ["Legendre polynomials"]
name = "RealRooted.shiftedLegendreReal_splits"
module = "RealRooted.Legendre.Roots"
label = "Shifted Legendre polynomials are real-rooted"

[[theorems]]
objects = ["Legendre polynomials"]
property = "interlacing"
name = "RealRooted.shiftedLegendreReal_strictInterl_succ"
module = "RealRooted.Legendre.Roots"
label = "Consecutive shifted Legendre polynomials interlace"

[[theorems]]
objects = ["Chebyshev polynomials"]
name = "RealRooted.Chebyshev.T_sub_C_splits"
module = "RealRooted.Chebyshev.Levels"
label = "For n ≥ 1 and |h| ≤ 1, T_n − h is real-rooted; h = 0 gives T_n"

[[definitions]]
name = "RealRooted.jacobiCoefficientPolynomial"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "The positive-coefficient Jacobi family Σ C(n,k) C(n+b,k) / C(a+k,k) X^k"

[[theorems]]
objects = ["Jacobi coefficient polynomials"]
property = "pf"
name = "RealRooted.jacobiCoefficientPolynomial_isPFPolynomial"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "For a, b > -1 the positive-coefficient family is Pólya frequency"

[[theorems]]
objects = ["Jacobi coefficient polynomials"]
property = "interlacing"
name = "RealRooted.jacobiCoefficientPolynomial_strictInterl_succ"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "Consecutive polynomials of the positive-coefficient family interlace"

[[theorems]]
name = "RealRooted.jacobiCoefficientPolynomial_nat_diagonal"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "On the diagonal a = b = m the family is the Narayana polynomial"

[[definitions]]
name = "RealRooted.Hypergeometric.threeFTwo"
module = "RealRooted.Hypergeometric.ThreeFTwo"
label = "Terminating three-over-two hypergeometric series"

[[theorems]]
objects = ["Terminating ₃F₂ polynomials"]
property = "interlacing"
name = "RealRooted.Hypergeometric.threeFTwo_interlaces_and_isCoprime"
module = "RealRooted.Hypergeometric.ThreeFTwo"
label = "Lima: strict interlacing and simple positive zeros in the strict parameter range"

[[theorems]]
objects = ["Terminating ₃F₂ polynomials"]
name = "RealRooted.Hypergeometric.threeFTwo_splits"
module = "RealRooted.Hypergeometric.ThreeFTwo"
label = "Terminating ₃F₂ polynomials are real-rooted at the weak parameter boundary"
-->

<!-- realrooted-catalog-content -->
# Orthogonal polynomials and Favard's theorem

A family of polynomials orthogonal for a positive weight satisfies a three-term recurrence, and
Favard's theorem gives the converse. Such families are real-rooted and consecutive members
interlace. This covers the classical Hermite, Laguerre, Jacobi, Legendre and Chebyshev
polynomials and the multiple orthogonal ₃F₂ polynomials of H. Lima.

## Results

Let $P_0=1$, $P_1=x-\alpha_0$ and
$$
P_{n+2}=(x-\alpha_{n+1})P_{n+1}-\beta_{n+1}P_n .
$$
Let $L$ be the linear functional that extracts the coefficient of $P_0$ in the basis $(P_n)$,
and $\langle p,q\rangle=L(pq)$.

**Theorem (Favard).** [@Favard1935] The family $(P_n)$ is orthogonal for
$\langle\cdot,\cdot\rangle$, with $\langle P_n,P_n\rangle=\beta_1\cdots\beta_n$, and $L$ is the
only such functional up to scaling. If $\beta_{n+1}>0$ for all $n$, the pairing is positive
definite, every $P_n$ is real-rooted and $P_n\ll P_{n+1}$.

**Corollary (classical families).** [@Szego1939] Each of the following is real-rooted with
simple roots, consecutive members interlace, and it is orthogonal for the stated weight:

- the probabilists' Hermite polynomials, $H_{n+2}=xH_{n+1}-(n+1)H_n$, for $e^{-x^2/2}$ on
  $\mathbb R$;
- the generalized Laguerre polynomials $n!\,L_n^{(\alpha)}(-x)$, for $\alpha>-1$, with
  negative roots, for $x^\alpha e^{-x}$ on $(0,\infty)$ after $x\mapsto-x$;
- the shifted Jacobi polynomials $P_n^{(\alpha,\beta)}$, for $\alpha,\beta>-1$, with roots in
  $(0,1)$, for $x^\alpha(1-x)^\beta$ on $(0,1)$; the shifted Legendre polynomials are the case
  $\alpha=\beta=0$.

The Chebyshev polynomials $T_n$ are real-rooted; more generally $T_n-h$ is real-rooted for
$n\ge1$ and $|h|\le1$.

**Theorem (Markoff).** For $\beta=1$ the $i$-th smallest root of the monic shifted Jacobi
polynomial of degree $n$ is strictly increasing in $\alpha\in(-1,\infty)$.

**Theorem (Durán).** [@Duran2025x, Thm. 1.3] Let $\ell_n^{(\alpha)}$ be the monic Laguerre
polynomial with positive roots, $\alpha>-1$, $K\le n$ and $\gamma_0=1$. If
$Q(x)=\sum_{j=0}^K(-1)^j\gamma_j\,x(x+1)\cdots(x+K-j-1)$ is real-rooted with all roots below
$\alpha+1$, then $\sum_{j=0}^K\gamma_j\ell_{n-j}^{(\alpha)}$ has only simple positive roots.

**Theorem (Lima).** Let $H_0=1$ and $H_n(z)={}_3F_2(-n,B_1,B_2;a_1,a_2;z)$, where
$(B_1,B_2)=(b_1+m,b_2+m-1)$ for $n=2m>0$ and $(b_1+m,b_2+m)$ for $n=2m+1$. If all parameters
are positive, $b_1>\max(a_1,a_2-1)$ and $b_2>\max(a_1,a_2)$, then the $H_n$ have simple
positive zeros and consecutive ones interlace. With weak inequalities they stay real-rooted
with positive zeros.

**Proposition (a non-orthogonal relative).** For $a,b>-1$ the polynomials
$\sum_k\binom nk\binom{n+b}k\binom{a+k}k^{-1}x^k$ are Pólya frequency polynomials with simple
negative roots, and consecutive ones interlace. For $a=b=m$ they are the
[Narayana polynomials](rr:narayana).

## Use

Favard's theorem is the standard route to real-rootedness of a polynomial sequence: exhibit a
three-term recurrence with positive $\beta_n$. The roots of $P_n$ are the eigenvalues of the
tridiagonal matrix with diagonal $\alpha_0,\dots,\alpha_{n-1}$ and off-diagonal entries
$\sqrt{\beta_1},\dots,\sqrt{\beta_{n-1}}$, so [Cauchy interlacing](rr:cauchy-interlacing)
gives a second proof of $P_n\ll P_{n+1}$.

## Proof

The roots of $P_{n+1}$ and $P_n$ interlace by induction on $n$, since $P_{n+2}$ and $P_n$ have
opposite signs at the roots of $P_{n+1}$. Orthogonality follows from the recurrence by
expanding $xP_n$ in the basis. Lima identifies the monic ₃F₂ polynomials with characteristic
polynomials of products of three bidiagonal matrices, which are totally nonnegative.

## References

[@Favard1935]; [@Szego1939, Chs. III–VI]; A. Markoff, “Sur les racines de certaines équations
(seconde note),” *Math. Ann.* 27 (1886), 177–182; [@Duran2025x, Thm. 1.3]; H. Lima,
[Multiple orthogonal polynomials associated with branched continued fractions for ratios of
hypergeometric series](https://arxiv.org/abs/2208.03539v2), Thm. 8.4. See also the
[interlacing overview on symmetricfunctions.com](sf:favardInterlacing).
<!-- /realrooted-catalog-content -->
-/
