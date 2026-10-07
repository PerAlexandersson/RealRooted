import RealRooted.Gurvits

/-!
# Van der Waerden permanent bound challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "van-der-waerden"
authors = ["Egorychev", "Falikman", "Gurvits"]
years = [1981, 2008]

[[definitions]]
name = "RealRooted.Gurvits.capacity"
module = "RealRooted.Gurvits.Capacity"
label = "Capacity of a multivariate polynomial"

[[theorems]]
name = "RealRooted.Gurvits.factorial_div_pow_le_permanent"
module = "RealRooted.Gurvits"
label = "Van der Waerden: the permanent of a doubly stochastic matrix is at least n!/nⁿ"
headline = true

[[theorems]]
name = "RealRooted.Gurvits.gurvitsFactor_mul_capacity_le_capacity_step"
module = "RealRooted.Gurvits"
label = "Gurvits: capacity drops by at most ((d−1)/d)^(d−1) per variable"

[[theorems]]
name = "RealRooted.Gurvits.mul_le_coeff_one_of_splits"
module = "RealRooted.Gurvits.Univariate"
label = "Gurvits' univariate coefficient inequality"
-->

<!-- realrooted-catalog-content -->
# The van der Waerden permanent bound

**Theorem (Egorychev, Falikman).** If $A$ is an $n \times n$ doubly stochastic matrix, then
$$
\operatorname{per} A \ge \frac{n!}{n^n}.
$$

The formal proof follows Gurvits. The *capacity* of a polynomial $p(x_1, \dotsc, x_n)$ with
nonnegative coefficients is $\inf_{x > 0} p(x) / (x_1 \cdots x_n)$. For a real stable
polynomial $p$ of total degree at most $k$ in $k$ variables, differentiating in one variable
and setting it to zero gives a real stable polynomial whose capacity is at least
$((k-1)/k)^{k-1}$ times that of $p$. The key input is a univariate inequality: if $q$ is
real-rooted with nonnegative coefficients and degree at most $d$, and $c\,t \le q(t)$ for all
$t > 0$, then $c\,((d-1)/d)^{d-1} \le q'(0)$. Applied to $\prod_i \sum_j a_{ij} x_j$, which is
real stable with capacity at least $1$, the $n$ steps extract the coefficient of
$x_1 \cdots x_n$, which is $\operatorname{per} A$, and the factors multiply to $n!/n^n$.

## References

G. P. Egorychev, “The solution of van der Waerden's problem for permanents,” *Advances in
Mathematics* 42 (1981), 299–305; D. I. Falikman, “Proof of the van der Waerden conjecture
regarding the permanent of a doubly stochastic matrix,” *Mathematical Notes* 29 (1981),
475–479; L. Gurvits, “Van der Waerden/Schrijver–Valiant like conjectures and stable (aka
hyperbolic) homogeneous polynomials: one theorem for all,” *Electronic Journal of
Combinatorics* 15 (2008), #R66.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proof lives in `RealRooted.Gurvits`.
-/
