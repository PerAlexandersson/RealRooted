module

import RealRooted.MultiplierSequence.CoefficientRatio
import RealRooted.MultiplierSequence.EulerCoefficientRatio

/-!
# Real-rootedness from a hypergeometric coefficient ratio

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
# Real-rootedness from a hypergeometric coefficient ratio

Let $p$ be a real polynomial of degree at most $d$ with $p(0)>0$ whose coefficients
satisfy a hypergeometric ratio. The simplest case is
$$
(k+1)(a+k)\,p_{k+1}=(d-k)(b+d-k-1)\,p_k\qquad(0\le k<d),
$$
with $a,b>0$. Then $p$ is a PF polynomial: it has nonnegative coefficients and only
real, nonpositive roots. The proof shows that such a polynomial is a positive multiple
of the two-sided Jensen polynomial with weights $1/(a)_k$ and $1/(b)_k$; the Jensen
polynomial is PF because reciprocal Pochhammer products with positive parameters
are PF multiplier sequences.

## Lists of parameters

The criterion extends to arbitrary finite lists of lower parameters $a_i>0$ and upper
parameters $b_j>0$, which may be empty, repeated, and of different lengths:
$$
(k+1)\prod_i(a_i+k)\,p_{k+1}=(d-k)\prod_j(b_j+d-k-1)\,p_k\qquad(0\le k<d).
$$
An upper parameter $b>0$ corresponds to a falling-factorial parameter $A=d+b-1>d-1$.
A coefficient ratio determines the polynomial up to a scalar.

## Euler factors

We also allow an extra weight $h(k)=\prod_i(r_i+k)\prod_j(s_j+d-k)$ with positive
parameters $r_i$ and $s_j$, so that the descending factors have their zeros strictly above
the ambient degree. The ratio then acquires $h(k)$ on the left and $h(k+1)$ on the right,
and the resulting polynomial is again PF. The proof uses shifted Euler PF multipliers
and two-sided Jensen polynomials.

## What is new

The parameter region implements Theorem 4.6 of Martínez-Finkelshtein, Morales and
Perales, *Real roots of hypergeometric polynomials via finite free convolution*; the
Euler-factor extension was developed in this library.

## References

A. Martínez-Finkelshtein, J. Morales and D. Perales, *Real roots of hypergeometric
polynomials via finite free convolution*, Theorem 4.6. For multiplier sequences, see the
[multiplier sequences](/RealRooted/concepts/multiplier-sequences/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.MultiplierSequence.CoefficientRatio` and
`RealRooted.MultiplierSequence.EulerCoefficientRatio`.
-/
