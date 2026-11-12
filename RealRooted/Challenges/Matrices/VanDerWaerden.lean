module

import RealRooted.Gurvits

/-!
# Van der Waerden permanent bound challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "van-der-waerden"
formalized = "2026-10-07"
tags = []
references = [
  "Gurvits2008",
  "Egorychev1981",
  "Falikman1981",
]
authors = ["Egorychev", "Falikman", "Gurvits"]
years = [1981, 2008]

[[definitions]]
name = "RealRooted.Gurvits.capacity"
module = "RealRooted.Gurvits.Capacity"
label = "Capacity of a multivariate polynomial"

[[theorems]]
name = "RealRooted.Gurvits.factorial_div_pow_le_permanent"
module = "RealRooted.Gurvits"
label = "Van der Waerden: the permanent of a doubly stochastic matrix is at least n!/nⁿ"
headline = true

[[theorems]]
name = "RealRooted.Gurvits.gurvitsFactor_mul_capacity_le_capacity_step"
module = "RealRooted.Gurvits"
label = "Gurvits: capacity drops by at most ((d−1)/d)^(d−1) per variable"

[[theorems]]
name = "RealRooted.Gurvits.mul_le_coeff_one_of_splits"
module = "RealRooted.Gurvits.Univariate"
label = "Gurvits' univariate coefficient inequality"
-->

<!-- realrooted-catalog-content -->
# The van der Waerden permanent bound

The permanent of an $n\times n$ doubly stochastic matrix is at least $n!/n^n$.

## Results

**Theorem (Egorychev, Falikman).** [@Egorychev1981; @Falikman1981] If $A$ is an $n\times n$
doubly stochastic matrix, then
$$
\operatorname{per}A\ge\frac{n!}{n^n}.
$$

## Proof

The proof follows Gurvits [@Gurvits2008]. The *capacity* of a polynomial $p(x_1,\dots,x_n)$
with nonnegative coefficients is $\inf_{x>0}p(x)/(x_1\cdots x_n)$. Let $p$ be a real stable
polynomial in $k$ variables of total degree at most $k$. Differentiating in one variable and
setting it to zero gives a real stable polynomial whose capacity is at least $((k-1)/k)^{k-1}$
times that of $p$. This rests on a univariate inequality: if $q$ is real-rooted with
nonnegative coefficients and degree at most $d$, and $c\,t\le q(t)$ for all $t>0$, then
$c\,((d-1)/d)^{d-1}\le q'(0)$. The polynomial $\prod_i\sum_ja_{ij}x_j$ is real stable with
capacity at least $1$ and coefficient $\operatorname{per}A$ at $x_1\cdots x_n$; the $n$ steps
extract this coefficient and the factors multiply to $n!/n^n$.

## References

[@Egorychev1981; @Falikman1981]; the proof above is that of [@Gurvits2008].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proof lives in `RealRooted.Gurvits`.
-/
