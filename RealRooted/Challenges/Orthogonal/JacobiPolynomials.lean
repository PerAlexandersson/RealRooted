module

import RealRooted.Jacobi
import RealRooted.Jacobi.Favard
import RealRooted.Jacobi.Markoff
import RealRooted.Jacobi.Orthogonality.Integral
import RealRooted.Jacobi.ParameterInterlacing
import RealRooted.Legendre.Basic
import RealRooted.Legendre.Roots
import RealRooted.Jacobi.CoefficientFamily
import RealRooted.Jacobi.NegativeIntegerEndpoint
import RealRooted.Jacobi.ParameterShifts

/-!
# Shifted Jacobi polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "jacobi-polynomials"
formalized = "2026-09-07"
tags = []
references = [
  "Szego1939",
]
authors = ["Jacobi", "Markoff", "Szegő"]
years = [1859, 1886, 1939]

[[definitions]]
name = "Polynomial.shiftedJacobi"
module = "RealRooted.Mathlib.RingTheory.Polynomial.Jacobi"
label = "Shifted Jacobi polynomials"

[[definitions]]
name = "Polynomial.shiftedJacobiMonic"
module = "RealRooted.Mathlib.RingTheory.Polynomial.Jacobi"
label = "Monic shifted Jacobi polynomials"

[[definitions]]
name = "RealRooted.shiftedJacobiWeight"
module = "RealRooted.Jacobi.Orthogonality.Integral"
label = "The weight x^α (1 - x)^β"

[[definitions]]
name = "RealRooted.shiftedJacobiMonicRoot"
module = "RealRooted.Jacobi.Markoff"
label = "The i-th smallest root"

[[theorems]]
name = "RealRooted.shiftedJacobi_interlaces_succ"
module = "RealRooted.Jacobi"
label = "Consecutive shifted Jacobi polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.shiftedJacobi_splits"
module = "RealRooted.Jacobi"
label = "Shifted Jacobi polynomials are real-rooted"

[[theorems]]
name = "RealRooted.shiftedJacobi_hasSimpleRoots"
module = "RealRooted.Jacobi"
label = "Shifted Jacobi polynomials have simple roots"

[[theorems]]
name = "RealRooted.shiftedJacobi_isRoot_mem_Ioo"
module = "RealRooted.Jacobi"
label = "Every root lies in (0, 1)"

[[theorems]]
name = "RealRooted.shiftedJacobiMonic_satisfiesFavardRecurrence"
module = "RealRooted.Jacobi.Favard"
label = "Monic shifted Jacobi polynomials satisfy a Favard recurrence"

[[theorems]]
name = "RealRooted.shiftedJacobi_integral_orthogonal"
module = "RealRooted.Jacobi.Orthogonality.Integral"
label = "Orthogonality on (0, 1) for the weight x^α (1 - x)^β"

[[theorems]]
name = "RealRooted.shiftedJacobi_interlaces_shift_both"
module = "RealRooted.Jacobi.ParameterInterlacing"
label = "P_n^(α+1,β+1) interlaces P_{n+1}^(α,β)"

[[theorems]]
name = "RealRooted.shiftedJacobiMonic_strictInterl_alpha_add_one"
module = "RealRooted.Jacobi.ParameterInterlacing"
label = "Raising α by one moves the roots to the right, interlacing"

[[theorems]]
name = "RealRooted.strictMonoOn_shiftedJacobiMonicRoot_alpha"
module = "RealRooted.Jacobi.Markoff"
label = "Markoff monotonicity in α, proved for β = 1"

[[theorems]]
name = "RealRooted.shiftedLegendreReal_eq_shiftedJacobi"
module = "RealRooted.Legendre.Basic"
label = "Shifted Legendre polynomials are the case α = β = 0"

[[theorems]]
name = "RealRooted.shiftedLegendreReal_splits"
module = "RealRooted.Legendre.Roots"
label = "Shifted Legendre polynomials are real-rooted"

[[theorems]]
name = "RealRooted.shiftedLegendreReal_strictInterl_succ"
module = "RealRooted.Legendre.Roots"
label = "Consecutive shifted Legendre polynomials interlace"

[[definitions]]
name = "RealRooted.jacobiCoefficientPolynomial"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "The positive-coefficient Jacobi family Σ C(n,k) C(n+b,k) / C(a+k,k) X^k"

[[definitions]]
name = "RealRooted.reflectedJacobiOperator"
module = "RealRooted.Jacobi.NegativeIntegerEndpoint"
label = "The reflected shifted-Jacobi differential operator"

[[theorems]]
name = "RealRooted.jacobiCoefficientPolynomial_isPFPolynomial"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "For a, b > -1 the positive-coefficient Jacobi polynomials are PF"

[[theorems]]
name = "RealRooted.jacobiCoefficientPolynomial_strictInterl_succ"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "Consecutive polynomials of the family interlace"

[[theorems]]
name = "RealRooted.jacobiCoefficientPolynomial_hasSimpleRoots"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "The family has simple, negative roots"

[[theorems]]
name = "RealRooted.jacobiCoefficientPolynomial_nat_diagonal"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "On the diagonal a = b = m the family is the Narayana polynomial"

[[theorems]]
name = "RealRooted.derivative_jacobiCoefficientPolynomial"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "Differentiation shifts the parameter a to a + 1"

[[theorems]]
name = "RealRooted.jacobiCoefficientPolynomial_derivative_recurrence"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "A first-order derivative recurrence in the degree"

[[theorems]]
name = "RealRooted.eq_jacobiCoefficientPolynomial_of_derivative_recurrence"
module = "RealRooted.Jacobi.CoefficientFamily"
label = "The derivative recurrence with two initial values determines the family"

[[theorems]]
name = "RealRooted.eq_C_mul_endpoint_factor_of_reflectedJacobiOperator_eq_zero"
module = "RealRooted.Jacobi.NegativeIntegerEndpoint"
label = "For β = -m the polynomial solutions are multiples of (1 + X)^m times a Jacobi polynomial"

[[theorems]]
name = "RealRooted.eq_of_reflectedJacobiOperator_eq_zero"
module = "RealRooted.Jacobi.NegativeIntegerEndpoint"
label = "Degree-free uniqueness of polynomial solutions with given constant term"

[[theorems]]
name = "RealRooted.splits_of_reflectedJacobiOperator_eq_zero"
module = "RealRooted.Jacobi.NegativeIntegerEndpoint"
label = "Polynomial solutions at a negative integer endpoint are real-rooted"

[[theorems]]
name = "RealRooted.rootMultiplicity_neg_one_of_reflectedJacobiOperator_eq_zero"
module = "RealRooted.Jacobi.NegativeIntegerEndpoint"
label = "The root -1 has multiplicity exactly m"

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_coeff_of_reflectedJacobiOperator_eq_zero"
module = "RealRooted.Jacobi.NegativeIntegerEndpoint"
label = "The coefficients of a solution with p(0) ≥ 0 form a Pólya frequency sequence"

[[theorems]]
name = "RealRooted.jacobiCoefficientPolynomial_eq_C_mul_eulerShiftRange"
module = "RealRooted.Jacobi.ParameterShifts"
label = "Shifting b = a to b = a + r is a product of r consecutive Euler operators"

[[theorems]]
name = "RealRooted.iterate_derivative_jacobiCoefficientPolynomial"
module = "RealRooted.Jacobi.ParameterShifts"
label = "The r-th derivative shifts the parameter a to a + r"

[[theorems]]
name = "RealRooted.exists_diagonalOperator_jacobiCoefficientPolynomial_iff"
module = "RealRooted.Jacobi.ParameterShifts"
label = "A polynomial Euler multiplier maps the diagonal family to (a, b) iff b - a is natural"

[[theorems]]
name = "RealRooted.IsPFPolynomial.eulerShiftRange"
module = "RealRooted.Jacobi.ParameterShifts"
label = "Consecutive Euler operators preserve PF polynomials"
-->

<!-- realrooted-catalog-content -->
# Shifted Jacobi polynomials

The library works on the interval $(0, 1)$. For real $\alpha, \beta$, the
shifted Jacobi polynomial is
$$
P_n^{(\alpha,\beta)}(x) = \sum_{k=0}^{n} (-1)^k
  \binom{n + \alpha}{n - k} \binom{n + \alpha + \beta + k}{k} x^k,
$$
with generalized binomial coefficients. It is the classical Jacobi polynomial
evaluated at $1 - 2x$. The monic shifted Jacobi polynomial is $P_n^{(\alpha,\beta)}$
divided by its leading coefficient $(-1)^n \binom{2n + \alpha + \beta}{n}$.

**Theorem.** Let $\alpha, \beta > -1$ and $n \ge 0$.

- $P_n^{(\alpha,\beta)}$ is real-rooted with simple roots, and every root lies
  in the open interval $(0, 1)$.
- Consecutive polynomials interlace: $P_n^{(\alpha,\beta)} \ll P_{n+1}^{(\alpha,\beta)}$.
- For every real polynomial $q$ with $\deg q < n$,
  $$\int_0^1 P_n^{(\alpha,\beta)}(x)\, q(x)\, x^\alpha (1 - x)^\beta \, dx = 0.$$
- The monic polynomials satisfy a Favard three-term recurrence with explicit
  coefficients.
- Raising both parameters gives the derivative family:
  $P_n^{(\alpha+1,\beta+1)} \ll P_{n+1}^{(\alpha,\beta)}$.
- Raising $\alpha$ alone moves the roots to the right while keeping them
  interlaced: the monic polynomial with parameters $(\alpha, \beta)$ is
  interlaced by the one with parameters $(\alpha + 1, \beta)$, both of degree $n$.

**Markoff monotonicity, for $\beta = 1$.** For each $i < n$, the $i$-th
smallest root of the monic shifted Jacobi polynomial with parameters
$(\alpha, 1)$ is strictly increasing in $\alpha$ on $(-1, \infty)$. The root
is read off the sorted root list; outside the admissible range the default
value $0$ of that lookup is irrelevant. The case of general $\beta$ is not
formalized.

The shifted Legendre polynomials of Mathlib, mapped to $\mathbb{R}$, are the
case $\alpha=\beta=0$; for them real-rootedness and interlacing of consecutive
polynomials are also proved directly.

## A positive-coefficient Jacobi family

For $n\ge0$ and real $a,b$ put
$$
H_n^{(a,b)}(x)=\sum_{k=0}^n\frac{\binom nk\binom{n+b}{k}}{\binom{a+k}{k}}\,x^k .
$$
For $a,b>-1$ all coefficients are positive, $H_n^{(a,b)}$ has degree $n$ and
constant term $1$, it is a PF polynomial with simple negative roots, and
consecutive polynomials interlace (and share no root). Differentiation shifts the
parameter: $\bigl(H_{n+1}^{(a,b)}\bigr)'=\frac{(n+1)(n+b+1)}{a+1}H_n^{(a+1,b)}$,
and iterating gives the $r$-th derivative shifting $a$ to $a+r$. A first-order
derivative recurrence in $n$, together with $H_0$ and $H_1$, determines the family.
On the diagonal $a=b=m$ the polynomial $H_n^{(m,m)}$ is the Narayana polynomial
(see the [Narayana polynomials](/RealRooted/families/narayana/) page).

## Integral parameter shifts

Let $\theta=x\,d/dx$. The product $\prod_{j<r}(\theta+a+j)$ multiplies the coefficient of
$x^k$ by $(k+a)(k+a+1)\cdots(k+a+r-1)$; it preserves PF polynomials for
$a\ge0$. For $a>-1$ and $r\in\mathbb N$, the off-diagonal polynomial
$H_n^{(a,a+r)}$ is a constant multiple of this operator with parameter $a+1$
applied to the diagonal polynomial $H_n^{(a+r,a+r)}$. Conversely, there is a
polynomial $p$ with $H_n^{(a,b)}=\sum_kp(k)\,[x^k]H_n^{(b,b)}\,x^k$ for all $n$
if and only if $b=a+r$ for some natural number $r$, and then $p$ is the
explicit multiplier $x\mapsto(x+a+1)_r/(a+1)_r$.

## The reflected equation at a negative integer parameter

Let $L_{n,\alpha,\beta}$ be the differential operator whose coefficient recurrence is
$$
(k+1)(k+\alpha+1)\,p_{k+1}+\bigl(k(k+\alpha+\beta+1)-n(n+\alpha+\beta+1)\bigr)p_k=0 ,
$$
the equation satisfied by $P_n^{(\alpha,\beta)}(-x)$. For $\alpha>-1$ its polynomial
solutions are determined by the constant term. If $\beta=-m$ with $m\le n$, then every
polynomial solution is a multiple of
$$
(1+x)^m\,P_{n-m}^{(\alpha,m)}(-x),
$$
which has degree $n$, only real roots lying in $\{-1\}\cup(-1,0)$, the root $-1$
with multiplicity exactly $m$ and all other roots simple. A solution with
nonnegative constant term has a Pólya frequency sequence of coefficients.

## References

C. G. J. Jacobi, “Untersuchungen über die Differentialgleichung der
hypergeometrischen Reihe,” *Journal für die reine und angewandte Mathematik* 56
(1859), 149–165; A. Markoff, “Sur les racines de certaines équations (seconde
note),” *Mathematische Annalen* 27 (1886), 177–182. See also [@Szego1939,
Chs. IV and VI]. The general three-term theory is on the
[Favard page](/RealRooted/theorems/favard/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Jacobi` and
`RealRooted.Legendre`.
-/
