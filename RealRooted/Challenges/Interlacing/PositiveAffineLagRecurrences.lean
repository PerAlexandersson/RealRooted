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

Three-term recurrences with a constant leading coefficient and an affine lag term, started from
positive constants, have rows with nonnegative coefficients, simple negative roots and
interlacing consecutive terms.

## Results

**Theorem.** Let $P_0=p$ and $P_1=q$ be constants with $0<p\le q$, let $b_n,c_n\ge0$ and
$d_n>0$, and put
$$
P_{n+2}=(1+b_n+c_n)\,P_{n+1}+(d_nx-b_n)\,P_n .
$$
Then for every $n$ the polynomials $P_n$ and $P_{n+1}-P_n$ have nonnegative coefficients,
$P_n(0)>0$, $\deg P_n=\lfloor n/2\rfloor$, $P_n$ has simple negative roots, $P_n\ll P_{n+1}$,
and $P_n$ and $P_{n+1}$ have no common root.

**Theorem (ratio form).** The same conclusions hold, with $P_{n+1}-\rho P_n$ in place of
$P_{n+1}-P_n$, if the coefficient $1+b_n+c_n$ is replaced by any $a_n$ with
$\rho+b_n/\rho\le a_n$, where $\rho>0$ and $\rho p\le q$.

**Proposition (coefficient positivity).** Let $P_{n+2}=A_nP_{n+1}+B_nP_n$ and let $R$ be a
polynomial with nonnegative coefficients. Suppose $P_0$ and $P_1-RP_0$ have nonnegative
coefficients, and that $A_n-R$ and $R(A_n-R)+B_n$ have nonnegative coefficients for all $n$.
Then $P_n$ and $P_{n+1}-RP_n$ have nonnegative coefficients for all $n$, although the
recurrence contains a subtraction.

## Proof

The proposition, with $R=1$ or $R=\rho$, gives the coefficient statements. The interlacing then
follows from the Liu--Wang criterion for three-term recurrences, which allows equal degrees in
consecutive rows; see the
[Ma--Wang and Liu--Wang page](rr:ma-wang-liu-wang).

## References

The interlacing step is the criterion of [@LiuWang2007].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.ThreeTermRecurrence.PositiveAffineLag` and
`RealRooted.ThreeTermRecurrence.Coefficients`.
-/
