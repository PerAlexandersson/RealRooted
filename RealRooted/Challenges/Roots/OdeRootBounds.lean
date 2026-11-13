module

import RealRooted.Wronskian.OdeRootBound
import RealRooted.Wronskian.OdePropagation

/-!
# Root exclusion for second-order differential equations

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "ode-root-bounds"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.three_mul_sq_eval_derivative_derivative_sub_four_mul_nonneg"
module = "RealRooted.Wronskian.OdeRootBound"
label = "Laguerre's inequality at a root: 3 p''² - 4 p' p''' ≥ 0"

[[theorems]]
name = "RealRooted.ode_discriminant_eval_nonpos_of_isRoot"
module = "RealRooted.Wronskian.OdeRootBound"
label = "At a root z with A(z) ≠ 0 of a real-rooted solution, the ODE discriminant is nonpositive"

[[theorems]]
name = "RealRooted.not_isRoot_of_ode_discriminant_eval_pos"
module = "RealRooted.Wronskian.OdeRootBound"
label = "A point where the ODE discriminant is positive is not a root"

[[theorems]]
name = "RealRooted.eval_derivative_ne_zero_of_ode"
module = "RealRooted.Wronskian.OdeRootBound"
label = "Roots are simple wherever the leading ODE coefficient does not vanish"

[[theorems]]
name = "RealRooted.second_order_ode_family_of_recurrence"
module = "RealRooted.Wronskian.OdePropagation"
label = "An intertwining identity propagates the second-order ODE along a differential recurrence"

[[theorems]]
name = "RealRooted.splits_simple_roots_neg_strictInterl_of_ode"
module = "RealRooted.Wronskian.OdePropagation"
label = "ODE propagation gives real-rooted rows with simple negative roots and interlacing"
headline = true
-->

<!-- realrooted-catalog-content -->
# Root exclusion for second-order differential equations

If a real-rooted polynomial satisfies a second-order linear differential equation, a Laguerre
inequality forces a discriminant to be nonpositive at each of its roots. Many polynomial
families defined by a recurrence $K_nF_{n+1}=p_nF_n+q_nF_n'$ satisfy such equations, and then
a sign condition on the discriminant gives real roots and interlacing for the whole family.

## Results

**Theorem (Laguerre's inequality at a root).** If $p$ is a real-rooted polynomial and $z$ is a
root of $p$, then
$$3\,p''(z)^2-4\,p'(z)\,p'''(z)\ge0.$$

**Theorem (root exclusion).** Let $p\ne0$ and $A\,p''+B\,p'+C\,p=0$ for polynomials $A,B,C$. If
$z$ is a root of $p$ and $A(z)\ne0$, then $p'(z)\ne0$, so the root is simple. If moreover $p$ is
real-rooted, then the discriminant
$$\Delta=B^2+4A'B-4A\,(B'+C)$$
satisfies $\Delta(z)\le0$. Equivalently, a real-rooted solution has no root at a point $z$ with
$A(z)\ne0$ and $\Delta(z)>0$.

**Proposition (propagation).** Let $F_n$ satisfy $K_nF_{n+1}=p_nF_n+q_nF_n'$ with $K_n\ne0$, and
let $a_0F_0''+b_0F_0'+c_0F_0=0$. Suppose that for every $n$ there is a linear map $U_n$ on
polynomials such that, for every polynomial $g$, applying the operator
$a_{n+1}D^2+b_{n+1}D+c_{n+1}$ to $p_ng+q_ng'$ gives $U_n$ applied to
$a_ng''+b_ng'+c_ng$. Then $a_nF_n''+b_nF_n'+c_nF_n=0$ for every $n$.

**Theorem (real roots and interlacing).** In this setting, let moreover $K_n>0$ and
$\deg F_n=d+n$, let each $F_n$ have positive leading coefficient, nonnegative coefficients and
positive constant term, and let $F_0$ be real-rooted. Write $\Delta_n$ for the discriminant of
$(a_n,b_n,c_n)$. Suppose that for all $n$ and all $x<0$ we have $a_n(x)\ne0$, and that
$q_n(x)\ge0$ implies $\Delta_n(x)>0$. Then every $F_n$ is real-rooted with simple negative roots,
and $F_n\ll F_{n+1}$ for all $n$.

## Proof

At a negative root $x$ of $F_n$ the exclusion theorem gives $\Delta_n(x)\le0$, hence
$q_n(x)<0$. The critical-sign criterion of [Ma–Wang and Liu–Wang](rr:ma-wang-liu-wang) then
propagates simple negative roots and interlacing.

## References

For the second Laguerre form, see the [Laguerre inequalities](rr:laguerre-inequalities). For a
related method based on the Sonin function, see [Sonin envelopes](rr:sonin-envelope).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Wronskian.OdeRootBound`
and `RealRooted.Wronskian.OdePropagation`.
-/
