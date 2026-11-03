module

import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin

/-!
# Sonin envelopes and root exclusion for second-order polynomial ODEs

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "sonin-envelope"
formalized = "2026-11-03"
authors = ["Sonin", "Krasikov"]
years = [1880, 2014]

[[definitions]]
name = "Polynomial.Sonin.residual"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Residual of the second-order operator"

[[definitions]]
name = "Polynomial.Sonin.disc"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Discriminant of the normal form"

[[definitions]]
name = "Polynomial.Sonin.lin"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "First-order form 2ay' + by"

[[definitions]]
name = "Polynomial.Sonin.envelope"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Sonin envelope"

[[definitions]]
name = "Polynomial.Sonin.cross"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Cross product y W"

[[definitions]]
name = "Polynomial.Sonin.weightDefect"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Weight defect of a rational weight"

[[theorems]]
name = "Polynomial.Sonin.envelope_identity"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Sonin identity for the envelope"

[[theorems]]
name = "Polynomial.Sonin.cross_identity"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Sonin identity for the cross product"

[[theorems]]
name = "Polynomial.Sonin.hasDerivAt_envelope_div"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Derivative of the weighted envelope quotient"

[[theorems]]
name = "Polynomial.Sonin.hasDerivAt_cross_div"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "Derivative of the weighted cross-product quotient"

[[theorems]]
name = "Polynomial.Sonin.eval_ne_zero_of_tendsto_atBot"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "No roots on a left half-line"
headline = true

[[theorems]]
name = "Polynomial.Sonin.eval_ne_zero_of_mem_Ioc"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "No roots on a finite interval from a sign condition at the left end"
headline = true
-->

<!-- realrooted-catalog-content -->
# Sonin envelopes and root exclusion

Let $a, b, c$ be real polynomials and consider the second-order equation
$$
a\,y'' + b\,y' + c\,y = 0 .
$$
Put
$$
\Delta = 4ac - 2ab' + 2a'b - b^2, \qquad W = 2a\,y' + b\,y .
$$
Away from the zeros of $a$, the substitution $y = e^{-\frac12\int b/a}\, w$ brings the equation
to the normal form $w'' + Q\,w = 0$ with $Q = \Delta / (4a^2)$, and $W / (2a)$ is, up to the
same exponential factor, $w'$; this is the classical normal form of a second-order linear
equation.  The **Sonin envelope** is the polynomial
$$
F = \Delta\, y^2 + W^2 ,
$$
so that $F / \Delta$ is, up to a positive factor, the Sonin function $w^2 + (w')^2 / Q$ of the
normal form.  Sonin's idea is that the monotonicity of such a function, divided by a suitable
weight, controls the size of the oscillations of $w$ and the location of its zeros.

**Identities.** Let $g, h$ be polynomials, and write $R = a y'' + b y' + c y$ for the residual of
$y$, $P = 2a'\Delta - a\Delta'$ for the sign polynomial of the envelope, and
$T = a\,(g'h - g h') - b\,g h$ for the defect of the rational weight $g / h$.
Then, over any commutative ring and with no hypothesis on $a$,
$$
a\bigl((gF)' h \Delta - gF\,(h\Delta)'\bigr) - g h\, W^2 P
  = \Delta F\, T + 4 a g h \Delta W R .
$$
For the cross product $K = y W$ there is a companion identity in which the weight defect is taken
with $b - a'$ in place of $b$.  For a solution of the equation ($R = 0$) and a weight with
vanishing defect, the right-hand sides vanish.  If moreover $g h = a j$ with $a \neq 0$, the
real functions $g F / (h \Delta)$ and $g K / h$ are differentiable with the explicit derivatives
$$
\frac{j\,W^2 P}{(h\Delta)^2}, \qquad \frac{j\,(W^2 - \Delta y^2)}{2 h^2},
$$
valid wherever the denominators do not vanish.

**Theorem** (root exclusion). Let $y \neq 0$ be a polynomial solution of
$a y'' + b y' + c y = 0$, and let $g, h, j$ be polynomials with $g h = a j$ and
$a (g'h - g h') = (b - a')\, g h$.  Suppose $a$, $h$ do not vanish, $j > 0$ and $\Delta \le 0$
on $(-\infty, L]$, and that $g\,y\,W / h \to 0$ at $-\infty$.  Then $y$ has no root in
$(-\infty, L]$.  Similarly, with the same sign hypotheses on a finite interval $[L, U]$, if
$g\,y\,W / h \ge 0$ at $L$, then $y$ has no root in $(L, U]$; the mirror statements for
$[L, \infty)$ and for $[L, U]$ with strict positivity at $L$ are also formalized
(`Polynomial.Sonin.eval_ne_zero_of_tendsto_atTop`, `Polynomial.Sonin.eval_ne_zero_of_mem_Icc`).

## Proof idea

Under these hypotheses the function $E = g\,y\,W / h$ is nondecreasing, because its derivative
$j(W^2 - \Delta y^2)/(2h^2)$ is nonnegative when $\Delta \le 0$.  At a root $r$ of $y$ with
$a(r) \neq 0$ we have $E(r) = 0$, and $y'(r) \neq 0$ since a nonzero solution has only simple
roots at ordinary points; hence $E'(r) = j(r)\,W(r)^2 / (2 h(r)^2) > 0$, so $E$ is negative
immediately to the left of $r$.  This contradicts $E \ge 0$ on the left, which follows from
monotonicity and the limit at $-\infty$ (or from the sign at $L$).

## References

The Sonin function and its monotonicity are due to N. Sonin, *Math. Ann.* 16 (1880), 1–80.  For
Sonin functions in the study of zeros of orthogonal polynomials see I. Krasikov, LMS J. Comput.
Math. 17 (2014), 209–225, Section 2; the normal form of a second-order linear equation is
DLMF 1.13.13–15.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin`.
-/
