module

import RealRooted.CoefficientShape
import RealRooted.Maclaurin
import RealRooted.LaguerreSamuelson
import RealRooted.Mathlib.Algebra.Polynomial.MeanMode

/-!
# Newton, Maclaurin and Laguerre–Samuelson inequalities

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "newton-maclaurin"
formalized = "2026-10-07"
references = []
tags = []
authors = ["Newton", "Maclaurin", "Laguerre", "Darroch", "Samuelson"]
years = [1707, 1729, 1880, 1964, 1968]

[[theorems]]
name = "NewtonAux.newton_esymm_ineq"
module = "RealRooted.NewtonAux"
label = "Newton's inequalities"

[[theorems]]
name = "RealRooted.hasUltraLogConcaveCoeffs_of_eq_zero_or_splits"
module = "RealRooted.CoefficientShape"
label = "Newton's inequalities for every real-rooted polynomial"

[[theorems]]
name = "RealRooted.coeffUltraLogConcaveUpTo_of_natDegree_le"
module = "RealRooted.CoefficientShape"
label = "Newton's inequalities at any level at least the degree"

[[theorems]]
name = "RealRooted.hasLogConcaveCoeffs_of_eq_zero_or_splits"
module = "RealRooted.CoefficientShape"
label = "Real-rooted polynomials have log-concave coefficients"

[[theorems]]
name = "RealRooted.Maclaurin.esymm_div_choose_rpow_le"
module = "RealRooted.Maclaurin"
label = "Maclaurin's inequalities"
headline = true

[[theorems]]
name = "RealRooted.Samuelson.sq_add_coeff_div_le"
module = "RealRooted.LaguerreSamuelson"
label = "Laguerre's root bound from the top coefficients"

[[theorems]]
name = "RealRooted.Samuelson.abs_sub_mean_le"
module = "RealRooted.LaguerreSamuelson"
label = "Samuelson's inequality"

[[theorems]]
name = "Polynomial.abs_sub_lt_one_of_isMode"
module = "RealRooted.Mathlib.Algebra.Polynomial.MeanMode"
label = "Darroch: the mode is within one of the mean"
-->

<!-- realrooted-catalog-content -->
# Newton, Maclaurin and Laguerre–Samuelson inequalities

The elementary symmetric means of real numbers, and the coefficients of a real-rooted
polynomial, satisfy Newton's and Maclaurin's inequalities, and the roots satisfy Laguerre's
bound.

## Results

For real numbers $x_1,\dotsc,x_n$ let $e_k$ be their elementary symmetric functions and
$E_k=e_k/\binom nk$.

**Newton's inequalities.** $E_{k-1}E_{k+1}\le E_k^2$ for $0<k<n$. In polynomial form, for every
real-rooted polynomial $p$ of degree $d$,
$$(k+1)(d-k+1)\,p_{k-1}p_{k+1}\le k(d-k)\,p_k^2\qquad(0<k<d).$$
The same inequality holds with $d$ replaced by any $n\ge d$. The coefficients of $p$ are also
log-concave: $p_{k-1}p_{k+1}\le p_k^2$.

**Maclaurin's inequalities.** If all $x_i\ge0$, then
$$E_1\ge E_2^{1/2}\ge E_3^{1/3}\ge\dotsb\ge E_n^{1/n}.$$

**Samuelson's inequality.** Every $x_j$ lies within $\sqrt{n-1}\,s$ of the mean $\mu$, where
$s^2=\frac1n\sum_i(x_i-\mu)^2$.

**Laguerre's root bound.** If $n\ge2$ and $x^n+ax^{n-1}+bx^{n-2}+\dotsb$ is real-rooted, every
root $r$ satisfies
$$\Bigl(r+\frac an\Bigr)^2\le\frac{n-1}n\Bigl(\frac{n-1}na^2-2b\Bigr).$$

**Darroch's theorem.** Let $p$ be a nonzero real-rooted polynomial with nonnegative
coefficients and $\mu=p'(1)/p(1)$ the mean of the distribution $k\mapsto p_k/p(1)$. Every mode
$k$ (an index with $p_k$ maximal) satisfies $|k-\mu|<1$.

## References

I. Newton, *Arithmetica Universalis* (1707); C. Maclaurin, “A second letter to Martin
Folkes,” *Philosophical Transactions* 36 (1729); E. Laguerre, “Sur une méthode pour obtenir
par approximation les racines d'une équation algébrique qui a toutes ses racines réelles,”
*Nouvelles Annales de Mathématiques* (1880); P. A. Samuelson, “How deviant can you be?”,
*Journal of the American Statistical Association* 63 (1968), 1522–1525; G. H. Hardy,
J. E. Littlewood and G. Pólya, *Inequalities*, §2.22; J. N. Darroch, “On the distribution
of the number of successes in independent trials,” *Annals of Mathematical Statistics* 35
(1964), 1317–1321.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.NewtonAux`,
`RealRooted.Maclaurin`, `RealRooted.LaguerreSamuelson` and
`RealRooted.Mathlib.Algebra.Polynomial.MeanMode`.
-/
