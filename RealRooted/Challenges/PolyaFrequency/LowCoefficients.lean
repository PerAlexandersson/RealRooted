module

import RealRooted.PFPolynomial.LowCoefficients

/-!
# Roots of a Pólya-frequency polynomial from its lowest coefficients

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "pf-low-coefficients"
formalized = "2026-11-03"
authors = []
tags = []
references = [
  "AissenSchoenbergWhitney1952",
]

[[theorems]]
name = "RealRooted.IsPFPolynomial.exists_largest_root_of_coeff_one_pos"
module = "RealRooted.PFPolynomial.LowCoefficients"
label = "The largest root from the three lowest coefficients"
headline = true

[[theorems]]
name = "RealRooted.IsPFPolynomial.card_filter_roots_lt_of_mul_coeff_one_le"
module = "RealRooted.PFPolynomial.LowCoefficients"
label = "Number of roots near zero from the two lowest coefficients"

[[theorems]]
name = "RealRooted.IsPFPolynomial.coeff_zero_sub_mul_coeff_one_le_eval_neg"
module = "RealRooted.PFPolynomial.LowCoefficients"
label = "Linear lower bound for a PF polynomial near zero"
-->

<!-- realrooted-catalog-content -->
# Roots of a PF polynomial from its lowest coefficients

A real polynomial $p$ is a *Pólya-frequency (PF) polynomial* if its coefficients are
nonnegative and all its roots are real and nonpositive [@AissenSchoenbergWhitney1952].  If
$p(0) = c_0 > 0$, then
$$
p(x) = c_0 \prod_i (1 + \lambda_i x), \qquad \lambda_i = -1/r_i > 0,
$$
where $r_i$ runs over the roots of $p$ with multiplicity, and the coefficient $c_1$ of $x$
satisfies $c_1 = c_0 \sum_i \lambda_i$.  The lowest coefficients $c_0, c_1, c_2$ therefore
control the roots closest to the origin.

**Linear lower bound.** If $p$ is PF with $c_0 > 0$, then for $t \ge 0$ with $t c_1 \le c_0$,
$$
c_0 - t c_1 \le p(-t).
$$
In particular $p(-t) > 0$ whenever $t c_1 < c_0$, and every root $r$ satisfies
$r c_1 \le -c_0$.

**Roots near zero.** If $p$ is PF with $c_0 > 0$, $R > 0$ and $j \ge 1$ is an integer with
$R\, c_1 \le j\, c_0$, then the interval $(-R, 0)$ contains at most $j - 1$ roots of $p$,
counted with multiplicity.

**Largest root.** Let $p$ be PF with $p(0) = 1$ and $c_1 > 0$, and suppose
$2 c_2 = \varepsilon c_1^2$ with $\varepsilon < 1/2$.  Then $p$ has a largest root $-v$, it is
simple, and
$$
1 \le c_1 v \le \frac{1}{1-\varepsilon}, \qquad
|c_1 v - 1| \le \frac{\varepsilon}{1-\varepsilon}, \qquad
\frac{1 - 2\varepsilon}{1 - \varepsilon} \le v\, p'(-v) \le 1 .
$$
Thus the largest root is close to $-1/c_1$ when $\varepsilon$ is small.

## Proof idea

All statements follow from the factorization $p = c_0 \prod_i (1 + \lambda_i x)$ with
$\lambda_i > 0$.  The linear bound is the inequality $\prod_i (1 - z_i) \ge 1 - \sum_i z_i$ for
$z_i \in [0, 1]$ with $z_i = t \lambda_i$.  The root count compares $R \sum_i \lambda_i = R c_1 /
c_0$ with the number of $\lambda_i$ exceeding $1/R$.  For the largest root one uses the first two
power sums of the $\lambda_i$, which are given by $c_1 / c_0$ and $(c_1^2 - 2 c_0 c_2) /
c_0^2$.

## References

See [@AissenSchoenbergWhitney1952] for the characterization of PF polynomials by their roots.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.PFPolynomial.LowCoefficients`.
-/
