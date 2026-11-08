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
headline = true

[[theorems]]
name = "RealRooted.strictInterl_of_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Row i interlaces row n whenever p(n) ≤ i ≤ n"
headline = true

[[theorems]]
name = "RealRooted.hasNonnegCoeffs_of_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Variable-delay rows have nonnegative coefficients"

[[theorems]]
name = "RealRooted.strictInterl_of_scaled_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "The same interlacing for the scaled recurrence a(n+1) F(n) + b(n+1) X F(p(n+1))"

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
headline = true

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

We study polynomial sequences in which each row is obtained from the previous
row and from an earlier row. The proof is the variable-predecessor induction
behind Fisk's example [@Fisk2006x, Example 16.10], using the interlacing cone
rules of Wagner [@Wagner1992, Section 3].

## Variable delay

Let $p:\mathbb N\to\mathbb N$ be monotone on positive indices with $p(n)<n$ for
$n\ge1$, let $w(n)\ge0$, and let $Q_0=1$ and
$$
Q_{n+1}=Q_n+w(n+1)\,x\,Q_{p(n+1)}.
$$
Then every $Q_n$ has nonnegative coefficients, constant term $1$, and only real
zeros, and $Q_i$ interlaces $Q_n$ whenever $p(n)\le i\le n$. The same
interlacing holds for the scaled recurrence
$F_{n+1}=a(n+1)F_n+b(n+1)\,x\,F_{p(n+1)}$ with $a(n)>0$ and $b(n)\ge0$.

## Fixed delay

For the fixed delay $p(n+1)=n+1-L$ with $L\ge1$ we obtain that $Q_A$ interlaces
$Q_B$ whenever $A\le B\le A+L$. The same holds for the scaled recurrence.

## A constant prefix

Let $c_i>0$ for $i<L$, let $P_i=c_i$ for $i<L$ and
$$
P_{n+L}=a_n\,P_{n+L-1}+b_n\,x\,P_n,\qquad a_n>0,\ b_n\ge0 .
$$
Then every $P_n$ has nonnegative coefficients, positive constant term and only
negative roots, and $P_A$ interlaces $P_B$ whenever $A\le B\le A+L$. If all
$b_n>0$, then $\deg P_n=\lfloor n/L\rfloor$.

## References

See [@Fisk2006x] and [@Wagner1992].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Interlacing.VariableDelay`
and `RealRooted.Interlacing.ConstantPrefixFixedDelay`.
-/
