module

import RealRooted.ThreeTermRecurrence.PositiveAffineLag
import RealRooted.ThreeTermRecurrence.Coefficients

/-!
# Positive affine-lag recurrences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "positive-affine-lag-recurrences"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.hasNonnegCoeffs_and_sub_mul_of_threeTerm"
module = "RealRooted.ThreeTermRecurrence.Coefficients"
label = "Coefficient positivity of a three-term recurrence through weighted differences"

[[theorems]]
name = "RealRooted.PositiveAffineLag.coefficients_and_degree"
module = "RealRooted.ThreeTermRecurrence.PositiveAffineLag"
label = "Rows have nonnegative coefficients and nonnegative successive differences"

[[theorems]]
name = "RealRooted.PositiveAffineLag.interlacing_and_roots"
module = "RealRooted.ThreeTermRecurrence.PositiveAffineLag"
label = "Consecutive rows interlace, have simple negative roots and no common roots"

[[theorems]]
name = "RealRooted.PositiveAffineLag.ratio_interlacing_and_roots"
module = "RealRooted.ThreeTermRecurrence.PositiveAffineLag"
label = "The same conclusions under the weaker ratio hypotheses"
headline = true
-->

<!-- realrooted-catalog-content -->
# Positive affine-lag recurrences

We study polynomial sequences with
$$
P_{n+2}=(1+b_n+c_n)\,P_{n+1}+(d_nx-b_n)\,P_n,
$$
where $P_0=p$ and $P_1=q$ are constants with $0<p\le q$, $b_n,c_n\ge0$ and $d_n>0$.

**Coefficient positivity without parity expansion.** For a general three-term
recurrence $P_{n+2}=A_nP_{n+1}+B_nP_n$ and a polynomial $R$ with nonnegative
coefficients, track $P_n$ together with $P_{n+1}-RP_n$. If the entries
$A_n-R$ and $R(A_n-R)+B_n$ have nonnegative coefficients, if $P_0$ has nonnegative
coefficients and $P_1-RP_0$ does too, then all $P_n$ and all $P_{n+1}-RP_n$ have
nonnegative coefficients, even though the recurrence itself contains a subtraction.

**Theorem.** For the affine-lag recurrence above, with $R=1$, every $P_n$ and every
successive difference $P_{n+1}-P_n$ has nonnegative coefficients, $\deg P_n=\lfloor n/2\rfloor$,
consecutive rows interlace, every row has simple negative roots, and consecutive rows
share no root. The same conclusions hold if the coefficient $1+b_n+c_n$ is replaced by any
$a_n$ with $\rho+b_n/\rho\le a_n$ and $\rho p\le q$ for some $\rho>0$.

## What is new

The results were developed in this library; no published source is cited. The directed
interlacing step uses the plateau-capable Liu–Wang criterion; see the
[Ma–Wang and Liu–Wang page](/RealRooted/theorems/ma-wang-liu-wang/).

## References

No published source is cited for these results in the formalization.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.ThreeTermRecurrence.PositiveAffineLag` and
`RealRooted.ThreeTermRecurrence.Coefficients`.
-/
