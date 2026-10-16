module

public import RealRooted.CoefficientDominance.LogConcavity
public import RealRooted.CoefficientDominance.RootGap
public import RealRooted.CoefficientDominance.Symmetric.Finite
public import RealRooted.CoefficientDominance.Symmetric.Polynomial
public import RealRooted.CoefficientDominance.Symmetric.Sharp
public import RealRooted.CoefficientDominance.Symmetric.Tail
public import RealRooted.CoefficientDominance.Symmetric.Upper

/-!
# Coefficient dominance and reciprocal gaps

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "coefficient-dominance"
formalized = "2026-09-01"
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

We describe finite positive families through the elementary symmetric values
`esym x n j` and the leading products `topProd x j`. The expansion in
`esym_eq_sum` and the recurrence `esym_succ` give the finite algebraic layer,
while `topProd_le_esym` supplies a lower bound when all entries are
nonnegative. The theorem `coeff_prod_one_add` identifies these values with the
coefficients of a product of linear factors.

For nonnegative entries and a nonnegative parameter, `esym_mul_pow_le` bounds
one weighted elementary symmetric term by the full generating product.
Theorem `esym_le_topProd_mul` rewrites this as a product of head and tail
corrections under positivity. `esym_le_exp` bounds those corrections by
exponentials of `headSum` and `tailSum`, and `esym_le_sharp` retains the
leading-product lower bounds for every term except the distinguished one.
The tail theorem `topProd_mul_tail_le` records a positive part of the next
elementary symmetric value.

For a positive log-concave sequence on a finite range, `sum_hi_le` and
`sum_lo_le` bound the two tails by geometric series when the corresponding
adjacent ratio is below one. If both ratios at an interior index are below
`1/3`, `sum_erase_lt` says that the central term dominates the sum of all
other terms. Applying this to the scaled coefficients of a polynomial gives
`eval_neg_ne_zero_of_dominant`: under positive coefficients, the degree
condition, log-concavity, and the two ratio hypotheses, the polynomial has no
root at `-s` for `s > 0`.

The positive-family estimates also control consecutive logarithmic ratios.
`log_ratio_ge` uses an upper bound by `topProd x (j + 1) * exp T` when
`j + 2 ≤ n`, while `log_ratio_ge_of_pos` supplies the same conclusion with
the explicit correction sums under positivity. Finally, if positive
`x (j - 1)` and `x j` lie on opposite sides of reciprocal endpoints, then
`log_gap_ge` converts a ratio at least `exp 2` between those endpoints into a
logarithmic gap of at least two.

## References

These results were extracted from a formal proof that the rows of
[OEIS A366159](https://oeis.org/A366159) are real-rooted and interlace. The triangle
appears in [@Kozlov2022].
<!-- /realrooted-catalog-content -->
-/

public section

namespace RealRooted.Challenges.CoefficientDominance

end RealRooted.Challenges.CoefficientDominance
