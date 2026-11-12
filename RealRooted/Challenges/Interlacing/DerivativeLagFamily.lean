module

import RealRooted.DerivativeRecurrence.LagParameterFamily
import RealRooted.DerivativeRecurrence.Evaluation
import RealRooted.DerivativeRecurrence.FiniteLagCoefficients

/-!
# A parameter-shifted derivative-lag family

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "derivative-lag-family"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.derivativeLagFamily"
module = "RealRooted.DerivativeRecurrence.LagParameterFamily"
label = "The two-parameter derivative-lag family"

[[theorems]]
name = "RealRooted.splits_derivativeLagFamily"
module = "RealRooted.DerivativeRecurrence.LagParameterFamily"
label = "For β, a ≥ 0 every row is real-rooted"

[[theorems]]
name = "RealRooted.strictInterl_derivativeLagFamily_add_one"
module = "RealRooted.DerivativeRecurrence.LagParameterFamily"
label = "The row with parameter a + 1 interlaces the row with parameter a"

[[theorems]]
name = "RealRooted.strictInterl_derivativeLagFamily_succ"
module = "RealRooted.DerivativeRecurrence.LagParameterFamily"
label = "Row n with parameter a + 1 interlaces row n + 1 with parameter a"
headline = true

[[theorems]]
name = "RealRooted.roots_derivativeLagFamily_neg"
module = "RealRooted.DerivativeRecurrence.LagParameterFamily"
label = "For a > 0 all roots are negative"

[[theorems]]
name = "RealRooted.eval_zero_derivativeLagFamily"
module = "RealRooted.DerivativeRecurrence.LagParameterFamily"
label = "The value at zero is the rising factorial of a"

[[theorems]]
name = "RealRooted.derivativeLagFamily_add_two"
module = "RealRooted.DerivativeRecurrence.LagParameterFamily"
label = "A two-lag derivative recurrence for the family"

[[theorems]]
name = "RealRooted.eq_derivativeLagFamily_of_recurrence"
module = "RealRooted.DerivativeRecurrence.LagParameterFamily"
label = "The two-lag recurrence with two initial rows determines the family"

[[theorems]]
name = "RealRooted.LinRec.natDegree_le_and_hasNonnegCoeffs"
module = "RealRooted.DerivativeRecurrence.FiniteLagCoefficients"
label = "Degree envelope and nonnegative coefficients for finite-lag differential recurrences"

[[theorems]]
name = "RealRooted.eval_eq_of_differential_recurrence"
module = "RealRooted.DerivativeRecurrence.Evaluation"
label = "Evaluation at a point killing the derivative multipliers gives a scalar recurrence"
-->

<!-- realrooted-catalog-content -->
# A parameter-shifted derivative-lag family

For $\beta,a\in\mathbb R$ define $P_0(a)=1$ and
$$
P_{n+1}(a)=x\,P_n(a+2)+\beta\,x\,P_n(a+1)'+a\,P_n(a+1).
$$
Each $P_n(a)$ is monic of degree $n$ and also satisfies
$P_{n+1}(a)=xP_n(a+1)+\beta xP_n(a)'+(a+n)P_n(a)$, together with the parameter-shift
identity $P_{n+1}(a+1)-P_{n+1}(a)=(n+1)P_n(a+1)$. A two-lag derivative recurrence
for $P_{n+2}(a)$ in terms of $P_{n+1}(a)$ and $P_n(a)$, with $P_0=1$ and $P_1=x+a$,
determines the family. The value at zero is the rising factorial
$P_n(a)(0)=a(a+1)\cdots(a+n-1)$.

**Theorem.** For $\beta\ge0$ and $a\ge0$, every $P_n(a)$ has nonnegative
coefficients and only real roots, all roots are $\le0$ (and $<0$ if $a>0$), and
$$
P_n(a+1)\ll P_n(a),\qquad P_n(a+1)\ll P_{n+1}(a).
$$

## Tools for finite-lag differential recurrences

For a recurrence $P_{n+k}=\sum_{j<k}\bigl(B_{n,j}P_{n+j}+A_{n,j}P_{n+j}'\bigr)$ with a degree
envelope $D$ compatible with the multipliers, nonnegativity of $A_{n,j}(0)$, and the
condition $A_{n,j}[x^{i+1}]\,r+B_{n,j}[x^i]\ge0$ for $r\le D(n+j)$, the row $P_n$ has
degree at most $D(n)$ and nonnegative coefficients, even if the derivative multipliers
have negative coefficients. If every positive-order multiplier vanishes at a point $\xi$
and $R_nP_{n+k}=\sum_t(\cdots)$ is the recurrence, evaluation at $\xi$ yields a scalar
recurrence, and matching initial values identifies all $P_n(\xi)$ with a prescribed scalar
solution.

## What is new

These results were developed in this library; no published source is cited, and we
attribute none.

## References

No published source is cited for these results in the formalization. See also the
[recurrence root windows](/RealRooted/theorems/recurrence-root-windows/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.DerivativeRecurrence`
modules named in the metadata.
-/
