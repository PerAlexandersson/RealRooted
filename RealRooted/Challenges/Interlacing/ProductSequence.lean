module

import RealRooted.ProductSequence.Core
import RealRooted.ProductSequence.Interlacing
import RealRooted.ProductSequence.FactorFamilies
import RealRooted.ProductSequence.Lifts
import RealRooted.ProductSequence.ScalarFamilies
import RealRooted.ProductSequence.EndpointPair
import RealRooted.ProductSequence.FixedDerivative
import RealRooted.ProductSequence.BinomialDerivativeFamily

/-!
# Product sequences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "product-sequences"
formalized = "2026-07-08"
authors = []
references = []
tags = []

[[theorems]]
name = "RealRooted.isRealRooted_of_product_factor_sequence"
module = "RealRooted.ProductSequence.Core"
label = "Closure under certified product factors"
headline = true

[[theorems]]
name = "RealRooted.productSequence_interlaces"
module = "RealRooted.ProductSequence.Interlacing"
label = "Consecutive product-sequence interlacing"

[[theorems]]
name = "RealRooted.productSequence_natDegree"
module = "RealRooted.ProductSequence.Interlacing"
label = "Product-sequence degree growth"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_affine_sequence"
module = "RealRooted.ProductSequence.FactorFamilies"
label = "Affine-factor product closure"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_X_add_C_pow_sequence"
module = "RealRooted.ProductSequence.FactorFamilies"
label = "Powered affine product closure"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_lift_sequence"
module = "RealRooted.ProductSequence.Lifts"
label = "Row-wise product lifts"

[[theorems]]
name = "RealRooted.isRealRooted_of_scalar_monomial_lift_sequence"
module = "RealRooted.ProductSequence.Lifts"
label = "Scalar-monomial lifts"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_scalar_linear_sequence"
module = "RealRooted.ProductSequence.ScalarFamilies"
label = "Alternating scalar-linear closure"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_sequence"
module = "RealRooted.ProductSequence.ScalarFamilies"
label = "Alternating powered-affine closure"

[[theorems]]
name = "RealRooted.strictInterl_endpoint_sum_then_X_pair_sequence"
module = "RealRooted.ProductSequence.EndpointPair"
label = "Endpoint-pair strict interlacing"

[[theorems]]
name = "RealRooted.isRealRooted_of_endpoint_sum_then_X_pair_sequence"
module = "RealRooted.ProductSequence.EndpointPair"
label = "Endpoint-pair real-rootedness"

[[theorems]]
name = "RealRooted.isRealRooted_of_endpoint_sum_then_X_pair_lift_sequence"
module = "RealRooted.ProductSequence.EndpointPair"
label = "Endpoint-power pair lift"

[[theorems]]
name = "RealRooted.interlaces_self_mul_of_natDegree_eq_one"
module = "RealRooted.ProductSequence.Interlacing"
label = "Interlacing after one linear factor"

[[theorems]]
name = "RealRooted.isRealRooted_finset_prod_X_sub_C"
module = "RealRooted.ProductSequence.Core"
label = "Finite products of linear factors"

[[theorems]]
name = "RealRooted.finiteLinearProductSequence_realRooted"
module = "RealRooted.ProductSequence.Core"
label = "Finite linear product sequences"

[[definitions]]
name = "RealRooted.binomialDerivativeRow"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "The normalized fixed derivatives (r!)⁻¹ D^r (X^r (1 + X)^n)"

[[theorems]]
name = "RealRooted.strictInterl_iterate_derivative_mul_X_sub_C_pow_succ"
module = "RealRooted.ProductSequence.FixedDerivative"
label = "Fixed derivatives of q (X - a)^n and q (X - a)^(n+1) interlace"

[[theorems]]
name = "RealRooted.iterate_derivative_mul_X_sub_C_pow_standard"
module = "RealRooted.ProductSequence.FixedDerivative"
label = "Fixed derivatives of q (X - a)^n are real-rooted with positive leading coefficient"

[[theorems]]
name = "RealRooted.roots_iterate_derivative_mul_X_sub_C_pow_mem_Icc"
module = "RealRooted.ProductSequence.FixedDerivative"
label = "The roots stay in any interval containing a and the roots of q"

[[theorems]]
name = "RealRooted.sum_pow_mul_iterate_derivative_mul_X_sub_C_pow_eq_zero"
module = "RealRooted.ProductSequence.FixedDerivative"
label = "A pure-lag recurrence for fixed derivatives of q (X - a)^n"

[[theorems]]
name = "RealRooted.coeff_binomialDerivativeRow"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "The coefficients are C(n, k) C(k + r, r)"

[[theorems]]
name = "RealRooted.binomialDerivativeRow_add_two"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "A three-term recurrence in n"

[[theorems]]
name = "RealRooted.strictInterl_binomialDerivativeRow_succ"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "Consecutive binomial derivative rows interlace"

[[theorems]]
name = "RealRooted.roots_binomialDerivativeRow_mem_Icc"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "The roots lie in [-1, 0]"
-->

<!-- realrooted-catalog-content -->
# Product sequences

Sequences built by multiplying by real-rooted factors stay real-rooted, and multiplying by a
linear factor gives an interlacing consecutive row.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
Real-rooted polynomials are nonzero here.

**Theorem (product factors).** Let $P_0$ and all $F_n$ be real-rooted, and
$P_{n+1}=F_nP_n$. Then every $P_n$ is real-rooted. If every $F_n$ has degree one, then
$\deg P_n=\deg P_0+n$ and $P_n\ll P_{n+1}$.

The interlacing rests on the one-step statement: if $f$ is real-rooted and $L$ has degree
one, then $f\ll Lf$. A finite product $\prod_{j\in S}(x-r_j)$ of linear factors is real-rooted;
hence if $P_n=\prod_{j<n}(x-r_{n,j})$ for all $n$, every $P_n$ is real-rooted.

**Theorem (factor families).** Let $P_0$ be real-rooted and $P_{n+1}=F_nP_n$, where $F_n$ is
either

- $s_nx+t_n$ with $s_n\ne0$, or
- $(x+t_n)^{m_n}$ with $m_n\ge0$.

Then every $P_n$ is real-rooted. The same holds for alternating steps
$P_{2n+1}=a_nP_{2n}$ with $a_n\ne0$ and $P_{2n+2}=F_nP_{2n+1}$ with $F_n=x+b_n$ or
$F_n=(x+b_n)^{m_n}$.

**Theorem (lifts).** If $Q_n$ and $F_n$ are real-rooted and $P_n=F_nQ_n$, then $P_n$ is
real-rooted. If $Q_n$ is real-rooted, $c_n\ne0$ and $P_n=c_n\,x^{m_n}Q_n$, then $P_n$ is
real-rooted.

**Theorem (endpoint pairs).** Let $A_0\ll B_0$ with nonnegative coefficients, and let
$$
A_{n+1}=A_n+B_n,\qquad B_{n+1}=B_n+x\,A_{n+1}.
$$
Then $A_n\ll B_n$ for all $n$, and $A_n$ and $B_n$ are real-rooted. Moreover, if
$P_{2n}=(x+t)^{m_A(n)}A_n$ and $P_{2n+1}=(x+t)^{m_B(n)}B_n$, then every $P_n$ is real-rooted.

## Fixed derivatives of products

**Theorem.** Let $q$ be real-rooted with positive leading coefficient, $r\le\deg q$ and
$a\in\mathbb R$. Then $D^r\bigl(q\,(x-a)^n\bigr)$ is real-rooted of degree $\deg q+n-r$ with
positive leading coefficient, and
$$
D^r\bigl(q\,(x-a)^n\bigr)\ll D^r\bigl(q\,(x-a)^{n+1}\bigr).
$$
If $a$ and all roots of $q$ lie in an interval $[u,v]$, then all roots of these derivatives lie
in $[u,v]$. The rows satisfy the pure-lag recurrence
$$
\sum_{i=0}^{r+1}(-1)^i\binom{r+1}{i}(x-a)^iD^r\bigl(q\,(x-a)^{n+r+1-i}\bigr)=0 .
$$

**Theorem (binomial derivative rows).** For $r\ge0$ let
$B_n^{(r)}=\frac1{r!}D^r\bigl(x^r(1+x)^n\bigr)$. Its coefficient of $x^k$ is
$\binom nk\binom{k+r}r$, and
$$
(n+2)B_{n+2}^{(r)}=\bigl(2n+3+(n+r+2)x\bigr)B_{n+1}^{(r)}-(n+1)(1+x)B_n^{(r)}.
$$
Every $B_n^{(r)}$ is real-rooted with all roots in $[-1,0]$, and
$B_n^{(r)}\ll B_{n+1}^{(r)}$.

## References

The alternating families are motivated by [OEIS A060523](https://oeis.org/A060523) and the
endpoint pairs by [OEIS A137477](https://oeis.org/A137477).
<!-- /realrooted-catalog-content -->
-/
