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
# Jacobi polynomials

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
label = "The i-th smallest root of the monic polynomial"

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
label = "Raising α by one: roots alternate and move right"

[[theorems]]
name = "RealRooted.strictMonoOn_shiftedJacobiMonicRoot_alpha"
module = "RealRooted.Jacobi.Markoff"
label = "Roots increase strictly with α for β = 1"

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
label = "For a, b > -1 the family is Pólya frequency"

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
label = "Polynomial solutions are determined by their constant term"

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
label = "Consecutive Euler operators preserve Pólya frequency polynomials"
-->

<!-- realrooted-catalog-content -->
# Jacobi polynomials

The shifted Jacobi polynomials are orthogonal on $(0,1)$, so they have simple roots in $(0,1)$
and consecutive ones interlace. A related family with positive coefficients contains the
Narayana polynomials and changes its parameters under differentiation and Euler operators.

## Results

For real $\alpha,\beta$ the *shifted Jacobi polynomial* is
$$
P_n^{(\alpha,\beta)}(x) = \sum_{k=0}^{n} (-1)^k
  \binom{n + \alpha}{n - k} \binom{n + \alpha + \beta + k}{k} x^k,
$$
with generalized binomial coefficients; it is the classical Jacobi polynomial at $1 - 2x$.
The monic version divides by the leading coefficient $(-1)^n \binom{2n + \alpha + \beta}{n}$.

**Theorem (roots and interlacing).** Let $\alpha, \beta > -1$ and $n \ge 0$.

- $P_n^{(\alpha,\beta)}$ is real-rooted with simple roots, all in $(0, 1)$.
- $P_n^{(\alpha,\beta)} \ll P_{n+1}^{(\alpha,\beta)}$.
- $P_n^{(\alpha+1,\beta+1)} \ll P_{n+1}^{(\alpha,\beta)}$.
- For the monic polynomials of degree $n$, the roots with parameters $(\alpha,\beta)$ and
  $(\alpha+1,\beta)$ alternate, each root for $(\alpha,\beta)$ lying at most as far right as the
  corresponding one for $(\alpha+1,\beta)$.

For $\alpha,\beta>-1$ and every real polynomial $q$ with $\deg q < n$,
$$\int_0^1 P_n^{(\alpha,\beta)}(x)\, q(x)\, x^\alpha (1 - x)^\beta \, dx = 0,$$
and the monic polynomials satisfy a [Favard](rr:favard) three-term recurrence with explicit
coefficients. The shifted Legendre polynomials are the case $\alpha=\beta=0$.

**Theorem (Markoff).** For $i<n$, the $i$-th smallest root of the monic polynomial with
parameters $(\alpha, 1)$ is strictly increasing in $\alpha\in(-1,\infty)$.

For $n\ge0$ and real $a,b$ let
$$
H_n^{(a,b)}(x)=\sum_{k=0}^n\frac{\binom nk\binom{n+b}{k}}{\binom{a+k}{k}}\,x^k .
$$
On the diagonal $a=b=m$ this is the [Narayana polynomial](rr:narayana).

**Theorem (positive-coefficient family).** Let $a,b>-1$. Then $H_n^{(a,b)}$ has positive
coefficients, degree $n$ and constant term $1$. It is a Pólya frequency polynomial with simple
negative roots, and $H_n^{(a,b)}\ll H_{n+1}^{(a,b)}$ with no common root.

Differentiation shifts the first parameter:
$\bigl(H_{n+1}^{(a,b)}\bigr)'=\frac{(n+1)(n+b+1)}{a+1}H_n^{(a+1,b)}$, and the $r$-th derivative
shifts $a$ to $a+r$. A first-order derivative recurrence in $n$, together with $H_0$ and $H_1$,
determines the family. With $\theta=x\,d/dx$, the operator $\prod_{j<r}(\theta+a+j)$ multiplies
the coefficient of $x^k$ by $(k+a)_r$ and preserves Pólya frequency polynomials for $a\ge0$; for
$a>-1$, $H_n^{(a,a+r)}$ is a constant multiple of this operator with parameter $a+1$ applied to
$H_n^{(a+r,a+r)}$. Conversely, for $a,b>-1$ there is a polynomial $p$ with
$H_n^{(a,b)}=\sum_kp(k)\,[x^k]H_n^{(b,b)}\,x^k$ for all $n$ if and only if $b=a+r$ with
$r\in\mathbb N$, and then $p(x)=(x+a+1)_r/(a+1)_r$. Here $(y)_r$ is the rising factorial.

Finally, let $L_{n,\alpha,\beta}$ be the differential operator whose coefficient recurrence is
$$
(k+1)(k+\alpha+1)\,p_{k+1}+\bigl(k(k+\alpha+\beta+1)-n(n+\alpha+\beta+1)\bigr)p_k=0,
$$
so that $L_{n,\alpha,\beta}\,P_n^{(\alpha,\beta)}(-x)=0$. For $\alpha>-1$ a polynomial solution
is determined by its constant term. If $\beta=-m$ with $m\le n$, every polynomial solution is a
multiple of $(1+x)^m\,P_{n-m}^{(\alpha,m)}(-x)$. A nonzero solution therefore has degree $n$,
real roots, and the root $-1$ with multiplicity exactly $m$; if its constant term is
nonnegative, its coefficients form a Pólya frequency sequence.

## References

- C. G. J. Jacobi, “Untersuchungen über die Differentialgleichung der hypergeometrischen
  Reihe,” *Journal für die reine und angewandte Mathematik* 56 (1859), 149–165.
- A. Markoff, “Sur les racines de certaines équations (seconde note),” *Mathematische Annalen*
  27 (1886), 177–182.
- [@Szego1939, Chs. IV and VI].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Jacobi` and
`RealRooted.Legendre`.
-/
