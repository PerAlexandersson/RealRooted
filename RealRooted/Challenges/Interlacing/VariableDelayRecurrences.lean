module

import RealRooted.Interlacing.VariableDelay
import RealRooted.Interlacing.ConstantPrefixFixedDelay

/-!
# Variable-delay and fixed-delay interlacing recurrences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "variable-delay-recurrences"
formalized = "2026-11-01"
tags = []
references = [
  "Fisk2006x",
  "Wagner1992",
]
authors = ["Fisk", "Wagner"]
years = [1992, 2006]

[[theorems]]
name = "RealRooted.splits_of_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Variable-delay recurrences have real-rooted rows"

[[theorems]]
name = "RealRooted.strictInterl_of_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Row i interlaces row n whenever p(n) ≤ i ≤ n"

[[theorems]]
name = "RealRooted.hasNonnegCoeffs_of_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Variable-delay rows have nonnegative coefficients"

[[theorems]]
name = "RealRooted.strictInterl_of_scaled_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "The same interlacing for the scaled recurrence a(n+1) F(n) + b(n+1) X F(p(n+1))"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_of_fixedDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Fixed delay L: rows A and B interlace when A ≤ B ≤ A + L"

[[theorems]]
name = "RealRooted.strictInterl_of_scaled_fixedDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Scaled fixed delay L: rows A and B interlace when A ≤ B ≤ A + L"

[[theorems]]
name = "RealRooted.strictInterl_of_constant_prefix_fixed_delay_recurrence"
module = "RealRooted.Interlacing.ConstantPrefixFixedDelay"
label = "Fixed-delay recurrences started from a constant prefix: interlacing of rows"

[[theorems]]
name = "RealRooted.roots_neg_of_constant_prefix_fixed_delay_recurrence"
module = "RealRooted.Interlacing.ConstantPrefixFixedDelay"
label = "Constant-prefix rows have only negative roots"

[[theorems]]
name = "RealRooted.natDegree_of_constant_prefix_fixed_delay_recurrence"
module = "RealRooted.Interlacing.ConstantPrefixFixedDelay"
label = "Constant-prefix rows have degree n / L"
-->

<!-- realrooted-catalog-content -->
# Variable-delay and fixed-delay interlacing recurrences

If each row equals the previous row plus $x$ times an earlier row, with nonnegative weights, then
the rows are real-rooted and rows within the delay window interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.

**Theorem (variable delay).** Let $p:\mathbb N\to\mathbb N$ satisfy $p(i)\le p(j)$ for
$1\le i\le j$ and $p(n)<n$ for $n\ge1$. Let $w(n)\ge0$, $Q_0=1$ and
$$
Q_{n+1}=Q_n+w(n+1)\,x\,Q_{p(n+1)}.
$$
Then every $Q_n$ has nonnegative coefficients and is real-rooted, and $Q_i\ll Q_n$ whenever
$p(n)\le i\le n$. The same interlacing holds for the scaled recurrence
$$
F_{n+1}=a(n+1)\,F_n+b(n+1)\,x\,F_{p(n+1)},\qquad F_0=1,\ a(n)>0,\ b(n)\ge0 .
$$

**Theorem (fixed delay).** Let $L\ge1$ and let $Q_{n+1}=Q_n+w(n+1)\,x\,Q_{\max(n+1-L,0)}$ with
$Q_0=1$ and $w(n)\ge0$; the weights may vanish. Then $Q_A\ll Q_B$ whenever $A\le B\le A+L$. The same
holds for the scaled recurrence
$P_{n+1}=a(n+1)P_n+b(n+1)\,x\,P_{\max(n+1-L,0)}$ with $P_0=1$, $a(n)>0$, $b(n)\ge0$.

**Theorem (constant prefix).** Let $L\ge1$, $c_i>0$ and $P_i=c_i$ for $i<L$, and
$$
P_{n+L}=a_n\,P_{n+L-1}+b_n\,x\,P_n,\qquad a_n>0,\ b_n\ge0 .
$$
Then every root of every $P_n$ is negative, and $P_A\ll P_B$ whenever $A\le B\le A+L$. If all
$b_n>0$, then $\deg P_n=\lfloor n/L\rfloor$.

## References

The induction on the predecessor follows [@Fisk2006x, Example 16.10], using the interlacing cone
rules of [@Wagner1992, Section 3].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Interlacing.VariableDelay`
and `RealRooted.Interlacing.ConstantPrefixFixedDelay`.
-/
