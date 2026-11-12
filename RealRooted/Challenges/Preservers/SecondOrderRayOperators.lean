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
authors = []
references = []
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

For $L=(a+bx)+(c+dx)\frac d{dx}+f\,x\frac{d^2}{dx^2}$ with $a,c,d\ge0$ and $b,f>0$, we give
an exact criterion on $c$ for $L$ to map every PF polynomial to a PF polynomial.

## Results

A polynomial is *PF* if it has nonnegative coefficients and is zero or has only real,
nonpositive roots. For real $a,b,c,d,f$ let
$$
L=(a+bx)+(c+dx)\,\frac{d}{dx}+f\,x\,\frac{d^2}{dx^2},
$$
and say $L$ *preserves PF polynomials* if $Lp$ is PF for every PF polynomial $p$. Put
$\delta=d^2-4bf$.

**Theorem (obstruction).** If $b>0$ and $\delta<0$, then $L$ does not preserve PF
polynomials. For some $m\ge1$, $L(x^m)$ has a non-real root.

**Theorem (sufficiency).** Let $a,c,d\ge0$, $b,f>0$ and $\delta>0$. For $j\ge1$ let
$$
\tau_j=\begin{cases}
a\bigl(d+\sqrt{\delta+4bf/j}\bigr)/(2b) & \text{if }a^2>j^2\delta+4bfj,\\[2pt]
f+\dfrac{ad}{2b}+\dfrac{j\delta}{4b}+\dfrac{a^2}{4bj} &
\text{if }\lvert j^2\delta-a^2\rvert\le4bfj,\\[6pt]
\bigl(ad+\sqrt{\delta(a^2+4bfj)}\bigr)/(2b) & \text{otherwise.}
\end{cases}
$$
If $c\le\tau_j$ for all $j\ge1$, then $L$ preserves PF polynomials. The sequence $\tau_j$ is
minimized at every integer $m\ge1$ with $\delta m(m-1)\le a^2\le\delta m(m+1)$.

**Theorem (classification).** Under the hypotheses of the sufficiency theorem, let $m\ge1$
satisfy $\delta m(m-1)\le a^2\le\delta m(m+1)$. Then $L$ preserves PF polynomials if and only
if $c\le\tau_m$. Explicitly:

1. (Lower) if $a^2>m^2\delta+4bfm$, the condition is $c\le a\bigl(d+\sqrt{\delta+4bf/m}\bigr)/(2b)$;
2. (Middle) if $\lvert m^2\delta-a^2\rvert\le4bfm$, the condition is
   $(a+dm)^2-4bm\bigl(c+f(m-1)\bigr)\ge0$, which is $c\le\tau_m$ in the second form above;
3. (Upper) in the remaining case, the condition is
   $c\le\bigl(ad+\sqrt{\delta(a^2+4bfm)}\bigr)/(2b)$.

**Theorem (special cases).**

- If $a,d\ge0$, $b,f>0$ and $4bf\le d^2$, then $L$ with $c=0$ preserves PF polynomials.
- If $A,C>0$, $B,E\ge0$ and $4AC\le B^2$, then $x(AD^2+BD+C)+E$ preserves PF polynomials.
- If $a,b>0$ and $c\ge0$, then $x(D+b)(D+a)+c$ preserves PF polynomials.
- For $\rho\ge2$ and $\gamma\ge0$, the operator $p\mapsto xp''+\rho\,xp'+xp+\gamma p$ preserves
  PF polynomials. For $\rho=0$ and $\gamma=1$ it does not: $(x+1)^2$ is PF and its image is
  not.

**Theorem (orbits).** Let $P_0=1$ and let $P_{n+1}$ be the image of $P_n$ under
$p\mapsto xp''+\rho\,xp'+xp+\gamma p$. If $\rho,\gamma\ge0$ and $5\rho^2<8$, then $P_n$ has a
non-real root for all sufficiently large $n$.

## Proof

For the obstruction, $L(x^m)$ has a quadratic factor with discriminant
$(a+dm)^2-4bm\bigl(c+f(m-1)\bigr)$, which is negative for some $m$ when $\delta<0$. For the
orbit statement, the first two signed root moments (Newton sums) and the Cauchy–Schwarz
inequality contradict the reality of all roots for large $n$.

## References

See the [operator preservers](/RealRooted/theorems/operator-preservers/) page for background
on PF polynomials and preservers.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Interlacing`
modules named in the metadata.
-/
