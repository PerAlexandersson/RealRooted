module

import RealRooted.EulerOperator.CoupledInsertion
import RealRooted.EulerOperator.PowerSeries

/-!
# Coupled Euler recurrences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "coupled-euler-recurrences"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.realEulerInsertionStep"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "The Euler step p ↦ (c + aX) p + (X - X²) p'"

[[definitions]]
name = "RealRooted.powerSeriesEuler"
module = "RealRooted.EulerOperator.PowerSeries"
label = "The Euler operator X d/dX on formal power series"

[[theorems]]
name = "RealRooted.realEulerInsertionStep_simple_roots_strictInterl"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "One Euler step: simple negative roots, one higher degree, interlaces its input"

[[theorems]]
name = "RealRooted.coupledEuler_secondOrder"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "Eliminating the auxiliary family gives a second-order recurrence with a signed lag term"

[[theorems]]
name = "RealRooted.coupledEuler_simple_roots_strictInterl"
module = "RealRooted.EulerOperator.CoupledInsertion"
label = "Both coupled families are real-rooted with simple negative roots and interlace"
headline = true

[[theorems]]
name = "RealRooted.coeff_powerSeriesEuler_iterate"
module = "RealRooted.EulerOperator.PowerSeries"
label = "The k-th iterate of the Euler operator multiplies the n-th coefficient by n^k"

[[theorems]]
name = "RealRooted.mul_iterate_derivation_eq_iterate_derivationShift_of_mul_eq"
module = "RealRooted.EulerOperator.PowerSeries"
label = "Coefficient extraction from Euler differential equations: M D^k F = (D - c)^k N"
-->

<!-- realrooted-catalog-content -->
# Coupled Euler recurrences

For real $c$ and $a$ let $E_{c,a}(p)=(c+ax)\,p+(x-x^2)\,p'$ be the Euler step. If $c>0$,
$p$ is real-rooted with positive leading coefficient, simple roots, nonnegative
coefficients and $p(0)>0$, and $\deg p<a$, then $E_{c,a}(p)$ has degree $\deg p+1$,
nonnegative coefficients, only simple negative roots, positive value at zero, and
$p$ interlaces $E_{c,a}(p)$ with no common root.

## Two coupled families

Let $P_0=Q_0=1$ and
$$
P_{n+1}=\bigl(c+\lambda_n+b_nx\bigr)P_n+(x-x^2)P_n',\qquad
Q_{n+1}=\bigl(c+t_nx\bigr)P_n+(x-x^2)P_n',\qquad t_n=b_n+\lambda_n .
$$
Eliminating $P$ gives a second-order recurrence for $Q_{n+2}$ with a signed lag term, so the
critical-sign criterion applies. If $c>0$, $\lambda_n\ge0$, $n<b_n$ and
$t_{n+1}-t_n\ge1$, then every $P_n$ and $Q_n$ has degree $n$, nonnegative coefficients,
simple negative roots, and
$$
P_n\ll P_{n+1},\qquad P_n\ll Q_{n+1},\qquad Q_n\ll Q_{n+1}.
$$

## The Euler operator on power series

The Euler operator $\theta=x\,d/dx$ on formal power series multiplies the coefficient of
$x^n$ by $n$, so $\theta^k$ multiplies it by $n^k$. More generally, for a derivation $D$ and
$M$ with $DM=cM$, if $MF=N$ then $M\,D^kF=(D+c)^kN$. This is the coefficient-extraction
step from an Euler differential equation to a polynomial recurrence; it is also used to
derive a second-order differential equation from a numerator identity.

## What is new

These results were developed in this library; no published source is cited, and we
attribute none.

## References

No published source is cited for these results in the formalization. The critical-sign
criterion is on the [Ma–Wang and Liu–Wang page](/RealRooted/theorems/ma-wang-liu-wang/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.EulerOperator.CoupledInsertion`
and `RealRooted.EulerOperator.PowerSeries`.
-/
