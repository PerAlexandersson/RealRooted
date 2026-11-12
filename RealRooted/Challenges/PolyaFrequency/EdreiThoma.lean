module

import RealRooted.EdreiThoma.Converse
import RealRooted.EdreiThoma.Easy

/-!
# Edrei–Thoma theorem: Pólya frequency sequences as canonical products

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "edrei-thoma"
formalized = "2026-10-13"
authors = ["Aissen", "Schoenberg", "Whitney", "Edrei"]
tags = []
references = [
  "AissenSchoenbergWhitney1952",
  "Edrei1953",
]

[[theorems]]
name = "RealRooted.EdreiThoma.exists_canonicalProduct_representation"
module = "RealRooted.EdreiThoma.Converse"
label = "Edrei: a Pólya frequency sequence with a₀ = 1 has a canonical product representation"
headline = true

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeries_canonicalProduct"
module = "RealRooted.EdreiThoma.Easy"
label = "Canonical products with nonnegative parameters are Pólya frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.isPolyaFreqSeq_coeff_canonicalProduct"
module = "RealRooted.EdreiThoma.Easy"
label = "The coefficient sequence of a canonical product is Pólya frequency"

[[theorems]]
name = "RealRooted.EdreiThoma.canonicalProduct_eq_C_mul_X_pow_mul_aswEdreiSymbol"
module = "RealRooted.EdreiThoma.Easy"
label = "A canonical product is c X^m times the Aissen–Schoenberg–Whitney–Edrei symbol"

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
# Edrei–Thoma theorem: Pólya frequency sequences as canonical products

A one-sided Pólya frequency sequence with $a_0=1$ is given near $0$ by a canonical product
$e^{\gamma z}\prod_i(1+\alpha_iz)/\prod_i(1-\beta_iz)$ with nonnegative parameters, and
conversely every such product has Pólya frequency coefficients.

We work with formal power series over $\mathbb R$ in the coefficientwise topology. A series
is *Pólya frequency* if its coefficient sequence is, that is, if its lower-triangular Toeplitz
matrix is totally nonnegative.

## Results

**Theorem (canonical products).** Let $c,\gamma\ge0$, $m\in\mathbb N$, and let
$\alpha_i,\beta_i\ge0$
with $\sum_i(\alpha_i+\beta_i)<\infty$. Then the series
$$
c\,X^m e^{\gamma X}\prod_i(1+\alpha_iX)\,\Bigl(\prod_i(1-\beta_iX)\Bigr)^{-1}
$$
is Pólya frequency. It equals $c\,X^m$ times the infinite Aissen–Schoenberg–Whitney–Edrei
symbol of $(\gamma,\alpha,\beta)$, and it is the coefficientwise limit of its finite prefixes
(exponential replaced by $(1+\gamma X/N)^N$, products truncated at $N$ factors), each of
which is Pólya frequency.

**Theorem (Edrei).** Let $(a_n)$ be a Pólya frequency sequence with $a_0=1$. There are
$\gamma\ge0$ and $\alpha_i,\beta_i\ge0$ with $\sum_i(\alpha_i+\beta_i)<\infty$ such that the
canonical product with $c=1$, $m=0$ has Pólya frequency coefficients and, for $z$ near $0$,
$$
\sum_n a_nz^n=e^{\gamma z}\,\frac{\prod_i(1+\alpha_iz)}{\prod_i(1-\beta_iz)} .
$$

Together the two theorems classify the one-sided Pólya frequency sequences.

## Use

The ingredients are Pólya frequency series closed under products and coefficientwise
limits, and the series $1+aX$, $1/(1-bX)$ and $e^{\gamma X}$ for $a,b,\gamma\ge0$, together
with $c\,X^m$ for $c\ge0$. The infinite numerator product and the formal inverse of the
denominator product are Pólya frequency under absolute summability of $\alpha$ and $\beta$.

## Proof

The converse follows Edrei's determinant identities and monotone limits, but replaces his
use of Nevanlinna's theorem by an elementary growth argument based on Jensen's formula and a
Borel-type lemma.

## References

The easy direction is [@AissenSchoenbergWhitney1952]. The converse is due to Edrei; we follow
[@Edrei1953]. The headline theorem is the normalized necessity direction of the
[Edrei–Thoma theorem](sf:edreiThomaTheorem); the canonical-product sufficiency direction is
listed separately.
<!-- /realrooted-catalog-content -->
-/
