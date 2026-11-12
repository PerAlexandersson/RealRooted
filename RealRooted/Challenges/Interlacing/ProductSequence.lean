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

We begin with the generic closure step. If the base row `P 0` is nonzero and
splits, every factor `F n` is nonzero and splits, and
`P (n + 1) = F n * P n`, then every row is nonzero and splits. When each factor
`L n` has natural degree one, the product-sequence results additionally give
`(P n).natDegree = (P 0).natDegree + n` and interlacing of consecutive rows.

The interlacing statement rests on a one-step theorem: a nonzero splitting
polynomial `f` interlaces `L * f` when `L` has natural degree one.
Independently, a finite product of factors `X - C (root j)` is nonzero and
splits. If each row has the form
`P n = ∏ j ∈ Finset.range n, (X - C (root n j))`, the finite linear product
sequence theorem supplies the row certificates without extra base hypotheses.
The affine family assumes a nonzero splitting base row and uses factors
`C (s n) * X + C (t n)` with `s n ≠ 0`; the powered affine family uses
`(X + C (t n)) ^ (m n)` in the same product recurrence.

We can also lift certificates row-wise. If `P n = F n * Q n`, both the model
rows `Q n` and the factors `F n` being nonzero and splitting imply the same for
`P n`. The scalar-monomial lift allows
`P n = C (c n) * (X ^ (m n) * Q n)` when every `c n` is nonzero. Alternating
families cover scalar steps followed by `(X + C (b n))` or its variable power,
with the scalar multiplier required to be nonzero.

For endpoint pairs, we assume a strictly interlacing initial pair with
nonnegative coefficients. The sum-then-`X` recurrences
`A (n + 1) = A n + B n` and
`B (n + 1) = B n + X * A (n + 1)` preserve strict interlacing and hence
nonzero splitting of both rows. The endpoint-power lift then proves
real-rootedness for a sequence with
$P_{2n}=(X+t)^{m_A(n)}A_n$ and
$P_{2n+1}=(X+t)^{m_B(n)}B_n$.

## Fixed derivatives of products

Fix a real-rooted polynomial $q$ with positive leading coefficient, $r\le\deg q$, and
$a\in\mathbb R$. Then $D^r\bigl(q\,(x-a)^n\bigr)$ is nonzero, real-rooted, with positive
leading coefficient, and it interlaces $D^r\bigl(q\,(x-a)^{n+1}\bigr)$. If $a$ and all roots
of $q$ lie in an interval $[u,v]$, then all roots of these derivatives lie in $[u,v]$. The
rows also satisfy a pure-lag recurrence
$$
\sum_{i=0}^{r+1}(-1)^i\binom{r+1}{i}(x-a)^iD^r\bigl(q\,(x-a)^{n+r+1-i}\bigr)=0 .
$$

For $q=x^r$ and $a=-1$ the normalized rows
$B_n^{(r)}=\frac1{r!}D^r\bigl(x^r(1+x)^n\bigr)$ have coefficients
$\binom nk\binom{k+r}r$, satisfy the three-term recurrence
$$
(n+2)B_{n+2}=\bigl(2n+3+(n+r+2)x\bigr)B_{n+1}-(n+1)(1+x)B_n,
$$
are real-rooted of degree $n$ with all roots in $[-1,0]$ and constant term $1$, and
consecutive rows interlace.

## References

[OEIS A060523](https://oeis.org/A060523), the motivating example named in
`RealRooted.ProductSequence.ScalarFamilies`.

[OEIS A137477](https://oeis.org/A137477), the motivating endpoint-pair example
named in `RealRooted.ProductSequence.EndpointPair`.
<!-- /realrooted-catalog-content -->
-/
