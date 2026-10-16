module

public import RealRooted.EdreiThoma.Converse
public import RealRooted.EdreiThoma.Easy

/-!
# The Edrei--Thoma theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "edrei-thoma"
formalized = "2026-10-13"

[[theorems]]
name = "RealRooted.EdreiThoma.exists_canonicalProduct_representation"
module = "RealRooted.EdreiThoma.Converse"
label = "Edrei: normalized Pólya-frequency sequences are canonical products"
headline = true

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_canonicalProduct"
module = "RealRooted.EdreiThoma.Easy"
label = "Aissen–Schoenberg–Whitney: canonical products are Pólya-frequency"
headline = true

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeq_coeff_canonicalProduct"
module = "RealRooted.EdreiThoma.Easy"
label = "Coefficient sequence is Pólya-frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.canonicalProduct_eq_C_mul_X_pow_mul_aswEdreiSymbol"
module = "RealRooted.EdreiThoma.Easy"
label = "Compatibility with the ASW--Edrei symbol"

[[theorems]]
name = "RealRooted.EdreiThoma.tendsto_canonicalPrefixProduct"
module = "RealRooted.EdreiThoma.Easy"
label = "Convergence of canonical prefixes"

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_canonicalPrefixProduct"
module = "RealRooted.EdreiThoma.Easy"
label = "Finite canonical prefixes are Pólya-frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_tprod_one_add"
module = "RealRooted.EdreiThoma.Easy"
label = "Numerator product is Pólya-frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_inv_tprod_one_sub"
module = "RealRooted.EdreiThoma.Easy"
label = "Reciprocal denominator is Pólya-frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_rescale_exp"
module = "RealRooted.EdreiThoma.Easy"
label = "Rescaled exponential is Pólya-frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_one_add_C_mul_X"
module = "RealRooted.EdreiThoma.Easy"
label = "Nonnegative linear factor is Pólya-frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_geometricFactor"
module = "RealRooted.EdreiThoma.Easy"
label = "Geometric factor is Pólya-frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.IsPolyaFreqSeries.mul"
module = "RealRooted.EdreiThoma.Easy"
label = "Closure under multiplication"

[[theorems]]
name = "RealRooted.EdreiThoma.IsPolyaFreqSeries.of_tendsto"
module = "RealRooted.EdreiThoma.Easy"
label = "Closure under coefficientwise limits"

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_C_mul_X_pow"
module = "RealRooted.EdreiThoma.Easy"
label = "Nonnegative shifted monomial is Pólya-frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.IsPolyaFreqSeries.X_pow_mul"
module = "RealRooted.EdreiThoma.Easy"
label = "Closure under a zero prefix"
-->

<!-- realrooted-catalog-content -->
# The Edrei--Thoma theorem

We work with formal power series over $\mathbb{R}$, equipped with the
coefficientwise topology. We use `IsPolyaFreqSeries` to say that the
coefficient sequence is Pólya-frequency, or equivalently that its lower
triangular Toeplitz matrix is totally nonnegative. We show that the canonical
product
$$
C X^m e^{\gamma X}\prod_i(1+\alpha_iX)\,
  \left(\prod_i(1-\beta_iX)\right)^{-1}
$$
has this property when all parameters are nonnegative and
$\sum_i(\alpha_i+\beta_i)$ is summable. We also record the coefficientwise
formulation directly as an `IsPolyaFreqSeq` statement.

We use the supporting factor theorems for the nonnegative linear factor, the
geometric factor $1/(1-bX)$, and the rescaled exponential
$e^{\gamma X}$. We also use closure under multiplication, powers,
multiplication by a nonnegative scalar, and multiplication by a power of
$X$ for the finite-factor arguments.

For nonnegative $\alpha_i$ and $\beta_i$, we show that the finite
numerator and denominator products are Pólya-frequency. From summability, we
obtain the corresponding absolute summability hypotheses, so the infinite
numerator product and the formal inverse of the denominator product are
coefficientwise limits of Pólya-frequency series. We combine coefficientwise
closure with convergence of the canonical prefixes to obtain the main
canonical-product result.

Finally, we identify this power-series expression with the infinite
ASW--Edrei symbol from `RealRooted.BrandenVecchi` using
`canonicalProduct_eq_C_mul_X_pow_mul_aswEdreiSymbol`.

Conversely, `exists_canonicalProduct_representation` shows that every
Pólya-frequency sequence with $a_0 = 1$ arises this way: there are
$\gamma \ge 0$ and nonnegative $\alpha_i, \beta_i$ with
$\sum_i(\alpha_i+\beta_i) < \infty$ such that the generating function equals
$e^{\gamma z}\prod_i(1+\alpha_i z)/\prod_i(1-\beta_i z)$ near $0$. The proof
follows Edrei's determinant identities and monotone limits, but replaces his
use of Nevanlinna's second main theorem by an elementary growth argument
(Jensen's formula and a Borel-type lemma). Together the two directions give the
classification of all one-sided Pólya-frequency sequences.

## References

M. Aissen, I. J. Schoenberg, and A. M. Whitney, “On the generating functions
of totally positive sequences. I,” *Journal d’Analyse Mathématique* 2 (1952),
93–103, [doi:10.1007/BF02786970](https://doi.org/10.1007/BF02786970), prove the easy direction.
The converse is due to A. Edrei (1952); we
follow his proof in *Canadian Journal of Mathematics* 5 (1953), 86–94,
[doi:10.4153/CJM-1953-010-3](https://doi.org/10.4153/CJM-1953-010-3). See the
[Edrei–Thoma theorem on symmetricfunctions.com](https://www.symmetricfunctions.com/polyaFrequency.htm#edreiThomaTheorem).
<!-- /realrooted-catalog-content -->
-/

public section

namespace RealRooted.Challenges.EdreiThoma

end RealRooted.Challenges.EdreiThoma
