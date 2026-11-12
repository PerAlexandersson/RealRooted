module

import RealRooted.Wronskian.OdeRootBound
import RealRooted.Wronskian.OdePropagation

/-!
# Laguerre's inequality and second-order ODE propagation

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
label = "At a root z with A(z) ≠ 0 of a split solution, the ODE discriminant is nonpositive"

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
name = "RealRooted.splits_simple_roots_neg_and_strictInterl_succ_of_ode_recurrence"
module = "RealRooted.Wronskian.OdePropagation"
label = "ODE propagation gives real-rooted rows with simple negative roots and interlacing"
headline = true
-->

<!-- realrooted-catalog-content -->
# Laguerre's inequality and second-order ODE propagation

**Laguerre's inequality.** If $p$ is a real-rooted polynomial and $z$ is a root of $p$, then
$$
3\,p''(z)^2-4\,p'(z)\,p'''(z)\ge0 .
$$

**ODE root exclusion.** Let $p\ne0$ split over $\mathbb R$ and satisfy
$A\,p''+B\,p'+C\,p=0$ for polynomials $A,B,C$. If $z$ is a root and $A(z)\ne0$, then
$p'(z)\ne0$, so the root is simple, and the ODE discriminant
$$
\Delta=B^2+4A'B-4A\,(B'+C)
$$
satisfies $\Delta(z)\le0$. Equivalently, $p$ has no root at a point $z$ with $A(z)\ne0$ and
$\Delta(z)>0$.

## Propagation along a recurrence

Let $F_n$ satisfy a first-order differential recurrence $K_nF_{n+1}=p_nF_n+q_nF_n'$ with
$K_n>0$, and suppose $F_0$ satisfies a second-order ODE $a_0F_0''+b_0F_0'+c_0F_0=0$. If an
intertwining identity holds, in which applying the $(n+1)$-st ODE operator to
$p_ng+q_ng'$ equals a linear map applied to the $n$-th ODE operator applied to $g$, then every
$F_n$ satisfies the ODE with coefficients $(a_n,b_n,c_n)$.

Suppose moreover that $\deg F_n=d+n$, each $F_n$ has positive leading coefficient, nonnegative
coefficients and positive constant term, $F_0$ splits, $a_n$ has no negative zero, and
$q_n(x)\ge0$ at a negative $x$ forces $\Delta_n(x)>0$. Then every $F_n$ splits with simple
negative roots, and $F_n$ interlaces $F_{n+1}$: the ODE discriminant forces the derivative
coefficient of the recurrence to be negative at every root, so the strict Ma–Wang criterion
propagates simple negative roots and interlacing.

## What is new

These results were developed in this library; no published source is cited, and we
attribute none. See also the [Sonin envelope page](/RealRooted/theorems/sonin-envelope/) and the
[Ma–Wang and Liu–Wang page](/RealRooted/theorems/ma-wang-liu-wang/).

## References

No published source is cited for these results in the formalization.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Wronskian.OdeRootBound`
and `RealRooted.Wronskian.OdePropagation`.
-/
