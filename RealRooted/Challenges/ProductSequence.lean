import RealRooted.ProductSequence.Core
import RealRooted.ProductSequence.Interlacing
import RealRooted.ProductSequence.FactorFamilies
import RealRooted.ProductSequence.Lifts
import RealRooted.ProductSequence.ScalarFamilies
import RealRooted.ProductSequence.EndpointPair

/-!
# Product sequences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "product-sequences"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_factor_sequence"
module = "RealRooted.ProductSequence.Core"
label = "Closure under certified product factors"

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
-->

<!-- realrooted-catalog-content -->
# Product sequences

We begin with the generic closure step. If the base row `P 0` is nonzero and
splits, every factor `F n` is nonzero and splits, and
`P (n + 1) = F n * P n`, then every row is nonzero and splits. When each factor
`L n` has natural degree one, the product-sequence results additionally give
`(P n).natDegree = (P 0).natDegree + n` and interlacing of consecutive rows.

The interlacing statement rests on a one-step theorem: a nonzero splitting
polynomial `f` interlaces `L * f` when `L` has natural degree one. A finite
product of factors `X - C (root j)` is therefore nonzero and splits. If each row has the form
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
real-rootedness for a sequence whose even and odd rows are endpoint powers of
`A n` and `B n`, respectively.

## References

[OEIS A060523](https://oeis.org/A060523), the motivating example named in
`RealRooted.ProductSequence.ScalarFamilies`.

[OEIS A137477](https://oeis.org/A137477), the product exit named in
`RealRooted.ProductSequence.EndpointPair`.
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.ProductSequence

end RealRooted.Challenges.ProductSequence
