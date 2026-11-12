module

import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin

/-!
# Sonin envelopes and root exclusion for second-order polynomial ODEs

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "sonin-envelope"
formalized = "2026-11-03"
references = []
tags = []
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

[[theorems]]
name = "Polynomial.Sonin.eval_ne_zero_of_mem_Ioc"
module = "RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin"
label = "No roots on a finite interval from a sign condition at the left end"
headline = true
-->

<!-- realrooted-catalog-content -->
# Sonin envelopes and root exclusion

For a polynomial solution of a second-order linear equation, monotonicity of a weighted Sonin
envelope excludes roots on half-lines and intervals where the normal-form discriminant is
nonpositive.

## Results

Let $a,b,c$ be polynomials and consider
$$a\,y''+b\,y'+c\,y=0.$$
Put
$$\Delta=4ac-2ab'+2a'b-b^2,\qquad W=2a\,y'+b\,y.$$
Away from the zeros of $a$, the substitution $y=e^{-\frac12\int b/a}\,w$ gives the normal form
$w''+Q\,w=0$ with $Q=\Delta/(4a^2)$, and $W/(2a)$ equals $w'$ up to the same exponential factor.
The *Sonin envelope* is the polynomial
$$F=\Delta\,y^2+W^2,$$
so that $F/\Delta$ is, up to a positive factor, the Sonin function $w^2+(w')^2/Q$.

**Identities.** Let $g,h$ be polynomials and write $R=a\,y''+b\,y'+c\,y$ for the residual of $y$,
$P=2a'\Delta-a\Delta'$ for the sign polynomial of the envelope, and $T=a\,(g'h-gh')-b\,gh$ for
the defect of the weight $g/h$. Then, over any commutative ring and with no hypothesis on $a$,
$$a\bigl((gF)'h\Delta-gF\,(h\Delta)'\bigr)-gh\,W^2P=\Delta F\,T+4agh\Delta W R.$$
For the cross product $K=yW$ and $\tilde T=a\,(g'h-gh')-(b-a')\,gh$ there is the companion identity
$$2a\bigl((gK)'h-gKh'\bigr)-gh\,(W^2-\Delta y^2)=2K\,\tilde T+4aghyR.$$

**Theorem (derivatives).** Let $a\ne0$, $gh=aj$ and $R=0$, and let $x$ be real.
If $T=0$ and $(h\Delta)(x)\ne0$, then $gF/(h\Delta)$ has derivative
$$\frac{j\,W^2P}{(h\Delta)^2}$$
at $x$. If $\tilde T=0$ and $h(x)\ne0$, then $gK/h$ has derivative
$$\frac{j\,(W^2-\Delta y^2)}{2h^2}$$
at $x$.

**Theorem (root exclusion).** Let $y\ne0$ be a polynomial solution of $a\,y''+b\,y'+c\,y=0$, and
let $g,h,j$ be polynomials with $gh=aj$ and $a\,(g'h-gh')=(b-a')\,gh$. Suppose $a$ and $h$ do
not vanish, $j>0$ and $\Delta\le0$ on $(-\infty,L]$, and $g\,y\,W/h\to0$ at $-\infty$. Then $y$
has no root in $(-\infty,L]$. The same hypotheses on $[L,\infty)$ with $g\,y\,W/h\to0$ at
$+\infty$ give no root in $[L,\infty)$. On a finite interval $[L,U]$ with the same sign
hypotheses, $y$ has no root in $(L,U]$ if $g\,y\,W/h\ge0$ at $L$, and no root in $[L,U]$ if
$g\,y\,W/h>0$ at $L$.

## Proof

On the region considered, $E=g\,y\,W/h$ is nondecreasing, since its derivative
$j(W^2-\Delta y^2)/(2h^2)$ is nonnegative when $\Delta\le0$. At a root $r$ of $y$ we have
$E(r)=0$ and $y'(r)\ne0$, hence $E'(r)=j(r)W(r)^2/(2h(r)^2)>0$ and $E$ is negative immediately to
the left of $r$. This contradicts $E\ge0$ on the left, which follows from monotonicity and the
limit at $-\infty$, or from the sign at $L$.

## References

The Sonin function and its monotonicity are due to N. Sonin, *Math. Ann.* 16 (1880), 1–80. For
Sonin functions in the study of zeros of orthogonal polynomials see I. Krasikov, LMS J. Comput.
Math. 17 (2014), 209–225, Section 2; the normal form of a second-order linear equation is
DLMF 1.13.13–15.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Sonin`.
-/
