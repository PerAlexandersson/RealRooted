module

import RealRooted.CoefficientDominance.LogConcavity
import RealRooted.CoefficientDominance.RootGap
import RealRooted.CoefficientDominance.Symmetric.Finite
import RealRooted.CoefficientDominance.Symmetric.Polynomial
import RealRooted.CoefficientDominance.Symmetric.Sharp
import RealRooted.CoefficientDominance.Symmetric.Tail
import RealRooted.CoefficientDominance.Symmetric.Upper

/-!
# Coefficient dominance and reciprocal gaps

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "coefficient-dominance"
formalized = "2026-09-01"
authors = []
tags = []
references = [
  "Kozlov2022",
]

[[theorems]]
name = "RealRooted.CoefficientDominance.eval_neg_ne_zero_of_dominant"
module = "RealRooted.CoefficientDominance.LogConcavity"
label = "Negative-root exclusion from coefficient dominance"
headline = true

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.log_ratio_ge_of_pos"
module = "RealRooted.CoefficientDominance.Symmetric.Upper"
label = "Unconditional logarithmic ratio bound"

[[theorems]]
name = "RealRooted.CoefficientDominance.log_gap_ge"
module = "RealRooted.CoefficientDominance.RootGap"
label = "Logarithmic gap from a root-free interval"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.esym_le_exp"
module = "RealRooted.CoefficientDominance.Symmetric.Upper"
label = "Exponential elementary-symmetric bound"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.esym_le_sharp"
module = "RealRooted.CoefficientDominance.Symmetric.Sharp"
label = "Sharp generating-function bound"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.esym_le_topProd_mul"
module = "RealRooted.CoefficientDominance.Symmetric.Upper"
label = "Multiplicative elementary-symmetric sandwich"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.topProd_mul_tail_le"
module = "RealRooted.CoefficientDominance.Symmetric.Tail"
label = "Tail contribution lower bound"

[[theorems]]
name = "RealRooted.CoefficientDominance.sum_erase_lt"
module = "RealRooted.CoefficientDominance.LogConcavity"
label = "Central-term dominance"

[[theorems]]
name = "RealRooted.CoefficientDominance.sum_hi_le"
module = "RealRooted.CoefficientDominance.LogConcavity"
label = "Upper-tail geometric estimate"

[[theorems]]
name = "RealRooted.CoefficientDominance.sum_lo_le"
module = "RealRooted.CoefficientDominance.LogConcavity"
label = "Lower-tail geometric estimate"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.log_ratio_ge"
module = "RealRooted.CoefficientDominance.Symmetric.Upper"
label = "Logarithmic ratio with a prescribed upper bound"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.esym_mul_pow_le"
module = "RealRooted.CoefficientDominance.Symmetric.Upper"
label = "Generating-product upper bound"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.coeff_prod_one_add"
module = "RealRooted.CoefficientDominance.Symmetric.Polynomial"
label = "Polynomial coefficient bridge"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.esym_eq_sum"
module = "RealRooted.CoefficientDominance.Symmetric.Finite"
label = "Explicit elementary-symmetric expansion"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.topProd_le_esym"
module = "RealRooted.CoefficientDominance.Symmetric.Finite"
label = "Leading-product lower bound"

[[theorems]]
name = "RealRooted.CoefficientDominance.Symmetric.esym_succ"
module = "RealRooted.CoefficientDominance.Symmetric.Finite"
label = "Elementary-symmetric recurrence"
-->

<!-- realrooted-catalog-content -->
# Coefficient dominance and reciprocal gaps

A positive log-concave coefficient sequence whose central term at $s$ dominates both neighbours
by a factor of three has no root at $-s$; elementary symmetric functions of a positive sequence
satisfy two-sided bounds that give lower bounds for consecutive logarithmic ratios.

## Results

**Theorem (tail estimates).** Let $t_0,\dots,t_{N-1}>0$ satisfy $t_kt_{k+2}\le t_{k+1}^2$ for
$k+2<N$, and let $j+1<N$.

- If $r=t_{j+1}/t_j<1$, then $\sum_{j<k<N}t_k\le t_j\,\dfrac r{1-r}$.
- If $j\ge1$ and $r=t_{j-1}/t_j<1$, then $\sum_{0\le k<j}t_k\le t_j\,\dfrac r{1-r}$.
- If $j\ge1$ and both $t_{j+1}/t_j<\tfrac13$ and $t_{j-1}/t_j<\tfrac13$, then
  $\sum_{k\ne j}t_k<t_j$.

**Theorem (negative-root exclusion).** Let $p$ be a real polynomial of degree $N$ with positive
coefficients $c_0,\dots,c_N$ satisfying $c_{i-1}c_{i+1}\le c_i^2$ for $0<i<N$. Let $s>0$ and
$1\le j\le N-1$ be such that
$$
\frac{c_{j+1}s^{j+1}}{c_js^j}<\frac13,\qquad \frac{c_{j-1}s^{j-1}}{c_js^j}<\frac13 .
$$
Then $p(-s)\ne0$.

For a sequence $x=(x_0,x_1,\dots)$ let $e_{n,j}=e_j(x_0,\dots,x_{n-1})$ be the $j$th elementary
symmetric function and $\pi_j=x_0x_1\cdots x_{j-1}$ the leading product. Put
$$
H_j=\sum_{i<j}\frac{x_{j-1}}{x_i},\qquad T_{n,j}=\sum_{j\le l<n}\frac{x_l}{x_{j-1}} .
$$

**Proposition (algebra).** We have $e_{n,j}=\sum_S\prod_{i\in S}x_i$ over the $j$-element subsets
$S$ of $\{0,\dots,n-1\}$,
$$
e_{n+1,j+1}=e_{n,j+1}+x_ne_{n,j},\qquad
\prod_{i<n}(1+x_iz)=\sum_je_{n,j}z^j ,
$$
and if all $x_i\ge0$ and $j\le n$, then $\pi_j\le e_{n,j}$.

**Theorem (upper bounds).** Let all $x_i\ge0$, let $j\le n$ and $t\ge0$. Then
$e_{n,j}\,t^j\le\prod_{i<n}(1+x_it)$. If moreover all $x_i>0$, then
$$
e_{n,j}\le\pi_j\prod_{i<j}\Bigl(1+\frac{x_{j-1}}{x_i}\Bigr)
\prod_{j\le l<n}\Bigl(1+\frac{x_l}{x_{j-1}}\Bigr)\le\pi_j\,e^{H_j+T_{n,j}} .
$$
For $t>0$ and nonnegative $x_i$,
$$
e_{n,j}\le t^{-j}\Bigl(\prod_{i<n}(1+x_it)-\sum_{k\le n,\,k\ne j}\pi_kt^k\Bigr).
$$
For positive $x_i$, $\pi_{j+1}\sum_{j<l<n}x_l\le e_{n,j+2}$.

**Theorem (logarithmic ratios).** Let all $x_i>0$ and $j+2\le n$. Then
$$
\log\frac{e_{n,j+1}^2}{e_{n,j}\,e_{n,j+2}}-2\bigl(H_{j+1}+T_{n,j+1}\bigr)
\le\log\frac{x_j}{x_{j+1}} .
$$
More generally, if $e_{n,j+1}\le\pi_{j+1}e^T$, then the same holds with $H_{j+1}+T_{n,j+1}$
replaced by $T$.

**Proposition (reciprocal gap).** Let $x_j>0$ and $s_1,s_2>0$ with $1/s_1<x_{j-1}$,
$x_j\le1/s_2$ and $s_2/s_1\ge e^2$. Then $\log(x_{j-1}/x_j)\ge2$.

## Use

The coefficients of $\prod_{i<n}(1+x_iz)$ are the $e_{n,j}$, so the bounds on $e_{n,j}$ apply to
the coefficients of such a product. The root-exclusion theorem applies to a polynomial with
positive log-concave coefficients at every point $-s$ with $s>0$.

## References

These results were extracted from a formal proof that the rows of
[OEIS A366159](https://oeis.org/A366159) are real-rooted and interlace. The triangle
appears in [@Kozlov2022].
<!-- /realrooted-catalog-content -->
-/
