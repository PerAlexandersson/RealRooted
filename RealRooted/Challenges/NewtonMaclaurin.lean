import RealRooted.Maclaurin
import RealRooted.LaguerreSamuelson

/-!
# Newton, Maclaurin and Laguerre–Samuelson inequalities challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "newton-maclaurin"
authors = ["Newton", "Maclaurin", "Laguerre", "Samuelson"]
years = [1707, 1729, 1880, 1968]

[[theorems]]
name = "NewtonAux.newton_esymm_ineq"
module = "RealRooted.NewtonAux"
label = "Newton's inequalities"

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
-->

<!-- realrooted-catalog-content -->
# Newton, Maclaurin and Laguerre–Samuelson inequalities

For real numbers $x_1, \dotsc, x_n$ let $e_k$ be their elementary symmetric functions and
$E_k = e_k / \binom{n}{k}$.

**Newton's inequalities.** $E_{k-1} E_{k+1} \le E_k^2$ for $0 < k < n$; equivalently, the
coefficients of a real-rooted polynomial, divided by binomial coefficients, form a
log-concave sequence.

**Maclaurin's inequalities.** If all $x_i \ge 0$, then
$$
E_1 \ge E_2^{1/2} \ge E_3^{1/3} \ge \dotsb \ge E_n^{1/n}.
$$

**Samuelson's inequality.** Every $x_j$ lies within $\sqrt{n-1}\, s$ of the mean $\mu$, where
$s^2 = \frac1n \sum_i (x_i - \mu)^2$.

**Laguerre's root bound.** If $x^n + a x^{n-1} + b x^{n-2} + \dotsb$ is real-rooted, every root
$r$ satisfies
$$
\Bigl(r + \frac{a}{n}\Bigr)^2 \le \frac{n-1}{n}\Bigl(\frac{n-1}{n} a^2 - 2b\Bigr).
$$

## References

I. Newton, *Arithmetica Universalis* (1707); C. Maclaurin, “A second letter to Martin
Folkes,” *Philosophical Transactions* 36 (1729); E. Laguerre, “Sur une méthode pour obtenir
par approximation les racines d'une équation algébrique qui a toutes ses racines réelles,”
*Nouvelles Annales de Mathématiques* (1880); P. A. Samuelson, “How deviant can you be?”,
*Journal of the American Statistical Association* 63 (1968), 1522–1525; G. H. Hardy,
J. E. Littlewood and G. Pólya, *Inequalities*, §2.22.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.NewtonAux`,
`RealRooted.Maclaurin` and `RealRooted.LaguerreSamuelson`.
-/
