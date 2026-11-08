module

import RealRooted.Interlacing.QuadraticPFPreservers
import RealRooted.Interlacing.SecondOrderClassification
import RealRooted.Interlacing.SecondOrderNecessity
import RealRooted.Interlacing.SecondOrderIff
import RealRooted.Interlacing.QuadraticDifferentialOrbit

/-!
# Second-order differential operators preserving PF polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "second-order-ray-operators"
formalized = "2026-11-01"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.secondOrderRayOperator"
module = "RealRooted.Interlacing.QuadraticPFPreservers"
label = "The operator (a + bX) + (c + dX) D + f X D²"

[[definitions]]
name = "RealRooted.SecondOrderRayPreserving"
module = "RealRooted.Interlacing.SecondOrderClassification"
label = "The operator maps every PF polynomial to a PF polynomial"

[[definitions]]
name = "RealRooted.secondOrderGapThreshold"
module = "RealRooted.Interlacing.SecondOrderIff"
label = "The optimized upper bound on c in the gap with j roots to its right"

[[definitions]]
name = "RealRooted.IsQuadraticDifferentialOrbit"
module = "RealRooted.Interlacing.QuadraticDifferentialOrbit"
label = "The orbit of 1 under X D² + ρ X D + X + γ"

[[theorems]]
name = "RealRooted.secondOrderRayPreserving_iff_three_branch_at_index"
module = "RealRooted.Interlacing.SecondOrderNecessity"
label = "PF preservation is equivalent to an explicit bound on c in three regimes"
headline = true

[[theorems]]
name = "RealRooted.not_secondOrderRayPreserving_of_discrim_neg"
module = "RealRooted.Interlacing.SecondOrderClassification"
label = "A negative residual discriminant d² - 4bf rules out PF preservation"

[[theorems]]
name = "RealRooted.secondOrderRayPreserving_of_forall_le_gapThreshold"
module = "RealRooted.Interlacing.SecondOrderIff"
label = "Sufficiency: c below every gap threshold implies PF preservation"

[[theorems]]
name = "RealRooted.secondOrderRayPreserving_iff_lower_bound_at_index"
module = "RealRooted.Interlacing.SecondOrderNecessity"
label = "The lower regime: exact bound on c at the minimizing index"

[[theorems]]
name = "RealRooted.secondOrderRayPreserving_iff_middle_discrim_at_index"
module = "RealRooted.Interlacing.SecondOrderNecessity"
label = "The middle regime: preservation iff a discriminant is nonnegative"

[[theorems]]
name = "RealRooted.secondOrderRayPreserving_iff_upper_bound_at_index"
module = "RealRooted.Interlacing.SecondOrderNecessity"
label = "The upper regime: exact bound on c at the minimizing index"

[[theorems]]
name = "RealRooted.secondOrderGapThreshold_minimized_at_index"
module = "RealRooted.Interlacing.SecondOrderIff"
label = "The gap threshold is minimized at the index m with δm(m-1) ≤ a² ≤ δm(m+1)"

[[theorems]]
name = "RealRooted.IsPFPolynomial.secondOrderRayOperator_of_constDerivative_eq_zero"
module = "RealRooted.Interlacing.SecondOrderClassification"
label = "With c = 0 and 4bf ≤ d², the operator preserves PF polynomials"

[[theorems]]
name = "RealRooted.IsPFPolynomial.quadraticPFOperator_of_pos"
module = "RealRooted.Interlacing.QuadraticPFPreservers"
label = "X (D + b)(D + a) + c preserves PF polynomials for a, b > 0 and c ≥ 0"

[[theorems]]
name = "RealRooted.IsPFPolynomial.secondOrderPFOperator_of_discrim_nonneg"
module = "RealRooted.Interlacing.QuadraticPFPreservers"
label = "X (A D² + B D + C) + E preserves PF polynomials when 4AC ≤ B²"

[[theorems]]
name = "RealRooted.IsPFPolynomial.rhoGammaOperator_of_two_le"
module = "RealRooted.Interlacing.QuadraticPFPreservers"
label = "X D² + ρ X D + X + γ preserves PF polynomials for ρ ≥ 2 and γ ≥ 0"

[[theorems]]
name = "RealRooted.rhoGammaOperator_zero_one_counterexample"
module = "RealRooted.Interlacing.QuadraticPFPreservers"
label = "Counterexample: the operator with ρ = 0, γ = 1 does not preserve PF polynomials"

[[theorems]]
name = "RealRooted.IsQuadraticDifferentialOrbit.exists_forall_exists_nonreal_root"
module = "RealRooted.Interlacing.QuadraticDifferentialOrbit"
label = "For 5ρ² < 8 the orbit has non-real roots in all large ranks"
-->

<!-- realrooted-catalog-content -->
# Second-order differential operators preserving PF polynomials

A polynomial is *Pólya frequency* (PF) if it is zero or has nonnegative
coefficients and only real, nonpositive roots. We ask for which real parameters
the second-order operator
$$
L=(a+bx)+(c+dx)\,\frac{d}{dx}+f\,x\,\frac{d^2}{dx^2}
$$
sends every PF polynomial to a PF polynomial.

## Necessary and sufficient conditions

Assume $a\ge0$, $b>0$, $c\ge0$, $d\ge0$ and $f>0$. If the residual discriminant
$d^2-4bf$ is negative, then $L$ does not preserve PF polynomials: some monomial
$x^m$ is mapped to a polynomial with a non-real root.

Now put $\delta=d^2-4bf>0$. For $j\ge1$ the *gap threshold*
$\tau_j$ is an explicit upper bound for $c$ obtained by optimizing over the gap
with $j$ roots to its right. It is given by one of three formulas (lower,
middle and upper regime) according to the size of $a^2$ compared with
$j^2\delta+4bfj$. If $c\le\tau_j$ for all $j\ge1$, then $L$ preserves PF
polynomials. The threshold is minimized at the index $m$ with
$\delta m(m-1)\le a^2\le\delta m(m+1)$, and for this index we have the exact
classification: $L$ preserves PF polynomials if and only if one of the
following holds.

1. (Lower) $a^2>m^2\delta+4bfm$ and
   $c\le a\bigl(d+\sqrt{\delta+4bf/m}\bigr)/(2b)$.
2. (Middle) $\lvert m^2\delta-a^2\rvert\le4bfm$ and
   $c\le f+\dfrac{ad}{2b}+\dfrac{m\delta}{4b}+\dfrac{a^2}{4bm}$. In this
   regime the condition is equivalent to $(a+dm)^2-4bm\bigl(c+f(m-1)\bigr)\ge0$.
3. (Upper) neither of the above and
   $c\le\bigl(ad+\sqrt{\delta(a^2+4bfm)}\bigr)/(2b)$.

The necessity direction uses explicit test polynomials: the shifted powers
$x^m(1+tx/(n+2))^{n+2}$, whose images factor with a quartic residual that
converges to an explicit limit, and for the lower regime a perturbed cubic with
negative discriminant. The sufficiency direction compares the sign of
$Lp/p$ at the points of each root gap, using the Laguerre identity
$p'^2-pp''=p^2\sum_r(x-r)^{-2}$.

## Special cases

If $c=0$ and $4bf\le d^2$, the operator preserves PF polynomials. In the
coefficient form $X(AD^2+BD+C)+E$ with $A,C>0$ and $B,E\ge0$, the condition
$4AC\le B^2$ suffices. For $a,b>0$ and $c\ge0$, the operator
$X(D+b)(D+a)+c$ preserves PF polynomials, which we prove by a common-interlacer
argument. The normalized operator
$$
p\mapsto xp''+\rho\,xp'+xp+\gamma p
$$
preserves PF polynomials for $\rho\ge2$ and $\gamma\ge0$, and the case
$\rho=0$, $\gamma=1$ fails already for $(x+1)^2$.

## Orbits of the normalized operator

Let $P_0=1$ and let $P_{n+1}$ be the image of $P_n$ under the normalized
operator. Each $P_n$ is monic of degree $n$. Comparing the first two signed root
moments (Newton sums) with the Cauchy–Schwarz inequality gives an explicit
obstruction: if $\rho,\gamma\ge0$ and $5\rho^2<8$, then $P_n$ has a non-real root
for every sufficiently large $n$.

## What is new

The statements on this page were developed in this library; the quadratic
case is tracked in RealRooted issue #2108. No published source is cited, and we
attribute none.

## References

No published source is cited for these results in the formalization. For
background on PF polynomials and preservers, see the
[operator preservers](/RealRooted/theorems/operator-preservers/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Interlacing`
modules named in the metadata.
-/
