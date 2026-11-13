module

import RealRooted.MultiplierSequence.CoefficientRatio
import RealRooted.MultiplierSequence.EulerCoefficientRatio

/-!
# Pólya frequency polynomials from a hypergeometric coefficient ratio

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hypergeometric-coefficient-ratios"
formalized = "2026-10-27"
authors = ["Martínez-Finkelshtein", "Morales", "Perales"]
references = []
tags = []

[[definitions]]
name = "RealRooted.pochhammerJensenPolynomial"
module = "RealRooted.MultiplierSequence.CoefficientRatio"
label = "The two-sided Jensen polynomial with reciprocal-Pochhammer weights"

[[definitions]]
name = "RealRooted.eulerPochhammerPolynomial"
module = "RealRooted.MultiplierSequence.EulerCoefficientRatio"
label = "The same model with additional two-sided Euler factors"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_invPochhammerProduct"
module = "RealRooted.MultiplierSequence.CoefficientRatio"
label = "Reciprocal Pochhammer products with positive parameters are PF multiplier sequences"

[[theorems]]
name = "RealRooted.pochhammerJensenPolynomial_isPF"
module = "RealRooted.MultiplierSequence.CoefficientRatio"
label = "Pochhammer Jensen polynomials with positive parameters are PF"

[[theorems]]
name = "RealRooted.isPFPolynomial_of_pochhammer_coeff_ratio"
module = "RealRooted.MultiplierSequence.CoefficientRatio"
label = "A polynomial with coefficient ratio (d-k)(b+d-k-1) / ((k+1)(a+k)), a, b > 0, is PF"

[[theorems]]
name = "RealRooted.isPFPolynomial_of_pochhammer_list_coeff_ratio"
module = "RealRooted.MultiplierSequence.CoefficientRatio"
label = "The coefficient-ratio criterion with arbitrary lists of upper and lower parameters"

[[theorems]]
name = "RealRooted.eq_C_mul_of_coeff_ratio"
module = "RealRooted.MultiplierSequence.CoefficientRatio"
label = "A coefficient ratio determines the polynomial up to a scalar"

[[theorems]]
name = "RealRooted.eulerPochhammerPolynomial_isPF"
module = "RealRooted.MultiplierSequence.EulerCoefficientRatio"
label = "Euler factors preserve the PF property of the Pochhammer Jensen model"

[[theorems]]
name = "RealRooted.isPFPolynomial_of_euler_pochhammer_coeff_ratio"
module = "RealRooted.MultiplierSequence.EulerCoefficientRatio"
label = "Coefficient-ratio criterion with two-sided Euler weights"
headline = true
-->

<!-- realrooted-catalog-content -->
# Pólya frequency polynomials from a hypergeometric coefficient ratio

A real polynomial with positive constant term whose coefficients satisfy a hypergeometric
ratio with positive parameters is PF.

## Results

A polynomial is *PF* (Pólya frequency) if it is zero or has nonnegative coefficients and only
real, nonpositive roots.

**Theorem (coefficient ratio).** Let $a,b>0$, let $p$ be a real polynomial of degree at most $d$
with $p(0)>0$, and suppose
$$
(k+1)(a+k)\,p_{k+1}=(d-k)(b+d-k-1)\,p_k\qquad(0\le k<d).
$$
Then $p$ is PF.

**Theorem (lists of parameters).** Let $a_1,\dots,a_s>0$ and $b_1,\dots,b_t>0$, with $s,t\ge0$
arbitrary and repetitions allowed. If $p$ has degree at most $d$, $p(0)>0$ and
$$
(k+1)\prod_i(a_i+k)\,p_{k+1}=(d-k)\prod_j(b_j+d-k-1)\,p_k\qquad(0\le k<d),
$$
then $p$ is PF. Two polynomials of degree at most $d$ satisfying the same ratio differ by a
scalar factor, provided one of them has nonzero constant term.

**Theorem (Euler factors).** Let moreover $r_1,\dots,r_u>0$ and $s_1,\dots,s_v>0$, and put
$h(k)=\prod_i(r_i+k)\prod_j(s_j+d-k)$. If $p$ has degree at most $d$, $p(0)>0$ and
$$
(k+1)\prod_i(a_i+k)\,h(k)\,p_{k+1}=(d-k)\prod_j(b_j+d-k-1)\,h(k+1)\,p_k\qquad(0\le k<d),
$$
then $p$ is PF.

## Proof

The two-sided Jensen polynomial with weights $1/(a)_k$ and $1/(b)_k$, where $(a)_k$ is the
rising factorial, is PF, because reciprocal Pochhammer products with positive parameters are PF
multiplier sequences. A polynomial with the given coefficient ratio is a positive multiple of
it. The Euler factors are handled with shifted Euler PF multipliers.

## References

The parameter region of the first theorem is that of Theorem 4.6 of A. Martínez-Finkelshtein,
J. Morales and D. Perales,
*Real roots of hypergeometric polynomials via finite free convolution*. For multiplier
sequences, see the [multiplier sequences](rr:multiplier-sequences) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.MultiplierSequence.CoefficientRatio` and
`RealRooted.MultiplierSequence.EulerCoefficientRatio`.
-/
