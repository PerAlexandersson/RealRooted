module

import RealRooted.DerivativeRecurrence.LagParameterFamily
import RealRooted.DerivativeRecurrence.Evaluation
import RealRooted.DerivativeRecurrence.FiniteLagCoefficients

/-!
# Real roots of a derivative-lag family with shifted parameter

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
label = "For β ≥ 0 and a > 0 all roots are negative"

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
# Real roots of a derivative-lag family with shifted parameter

The rows of a two-parameter derivative-lag family are real-rooted with nonpositive roots, and
rows at parameters differing by one interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; common roots are allowed unless stated. For
$\beta,a\in\mathbb R$ define $P_0(a)=1$ and
$$
P_{n+1}(a)=x\,P_n(a+2)+\beta\,x\,P_n(a+1)'+a\,P_n(a+1).
$$
Each $P_n(a)$ is monic of degree $n$, and
$$
P_{n+1}(a)=xP_n(a+1)+\beta xP_n(a)'+(a+n)P_n(a),\qquad
P_{n+1}(a+1)-P_{n+1}(a)=(n+1)P_n(a+1).
$$
Moreover $P_n(a)(0)=a(a+1)\cdots(a+n-1)$, and
$$
P_{n+2}(a)=(x+a+2n+2)P_{n+1}(a)+\beta xP_{n+1}(a)'
-(n+1)\bigl((a+n)P_n(a)+\beta xP_n(a)'\bigr).
$$
The last recurrence, with $P_0(a)=1$ and $P_1(a)=x+a$, determines the family.

**Theorem.** Let $\beta\ge0$ and $a\ge0$. Then every $P_n(a)$ has nonnegative coefficients and
only real roots, all roots are at most $0$, and all roots are negative if $a>0$. Moreover
$$
P_n(a+1)\ll P_n(a),\qquad P_n(a+1)\ll P_{n+1}(a).
$$

**Proposition (finite-lag recurrences).** Let $P_{n+k}=\sum_{j<k}\bigl(B_{n,j}P_{n+j}
+A_{n,j}P_{n+j}'\bigr)$, and let $D$ be a degree envelope with $D(n+j)\le D(n+k)$,
$\deg A_{n,j}\le D(n+k)-D(n+j)+1$ and $\deg B_{n,j}\le D(n+k)-D(n+j)$. Suppose that
$A_{n,j}(0)\ge0$ and
$$
A_{n,j}[x^{i+1}]\,r+B_{n,j}[x^i]\ge0\qquad\text{for all }i\text{ and all }r\le D(n+j),
$$
and that $P_0,\dotsc,P_{k-1}$ have nonnegative coefficients and $\deg P_j\le D(j)$. Then every
$P_n$ has degree at most $D(n)$ and nonnegative coefficients, even if the multipliers
$A_{n,j}$ have negative coefficients.

**Proposition (evaluation).** Let $R_n\ne0$ be real and let $R_nP_{n+k}=\sum_t M_{t,n}\,
P_{n+\ell_t}^{(o_t)}$ be a recurrence with lags $\ell_t<k$. Suppose that every multiplier $M_{t,n}$
with $o_t>0$ vanishes at $\xi$. If $(s_n)$ satisfies $R_ns_{n+k}=\sum_{o_t=0}M_{t,n}(\xi)\,
s_{n+\ell_t}$ and $P_i(\xi)=s_i$ for $i<k$, then $P_n(\xi)=s_n$ for all $n$.

## References

See also the [recurrence root windows](/RealRooted/theorems/recurrence-root-windows/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.DerivativeRecurrence`
modules named in the metadata.
-/
