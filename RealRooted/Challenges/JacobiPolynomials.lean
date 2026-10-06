import RealRooted.Jacobi
import RealRooted.Jacobi.Favard
import RealRooted.Jacobi.Markoff
import RealRooted.Jacobi.Orthogonality.Integral
import RealRooted.Jacobi.ParameterInterlacing
import RealRooted.Legendre.Basic

/-!
# Shifted Jacobi polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "jacobi-polynomials"
authors = ["Jacobi", "Markoff", "Szegő"]
years = [1859, 1886, 1939]

[[definitions]]
name = "Polynomial.shiftedJacobi"
module = "RealRooted.Mathlib.RingTheory.Polynomial.Jacobi"
label = "Shifted Jacobi polynomials"

[[definitions]]
name = "Polynomial.shiftedJacobiMonic"
module = "RealRooted.Mathlib.RingTheory.Polynomial.Jacobi"
label = "Monic shifted Jacobi polynomials"

[[definitions]]
name = "RealRooted.shiftedJacobiWeight"
module = "RealRooted.Jacobi.Orthogonality.Integral"
label = "The weight x^α (1 - x)^β"

[[definitions]]
name = "RealRooted.shiftedJacobiMonicRoot"
module = "RealRooted.Jacobi.Markoff"
label = "The i-th smallest root"

[[theorems]]
name = "RealRooted.shiftedJacobi_interlaces_succ"
module = "RealRooted.Jacobi"
label = "Consecutive shifted Jacobi polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.shiftedJacobi_splits"
module = "RealRooted.Jacobi"
label = "Shifted Jacobi polynomials are real-rooted"

[[theorems]]
name = "RealRooted.shiftedJacobi_hasSimpleRoots"
module = "RealRooted.Jacobi"
label = "Shifted Jacobi polynomials have simple roots"

[[theorems]]
name = "RealRooted.shiftedJacobi_isRoot_mem_Ioo"
module = "RealRooted.Jacobi"
label = "Every root lies in (0, 1)"

[[theorems]]
name = "RealRooted.shiftedJacobiMonic_satisfiesFavardRecurrence"
module = "RealRooted.Jacobi.Favard"
label = "Monic shifted Jacobi polynomials satisfy a Favard recurrence"

[[theorems]]
name = "RealRooted.shiftedJacobi_integral_orthogonal"
module = "RealRooted.Jacobi.Orthogonality.Integral"
label = "Orthogonality on (0, 1) for the weight x^α (1 - x)^β"
headline = true

[[theorems]]
name = "RealRooted.shiftedJacobi_interlaces_shift_both"
module = "RealRooted.Jacobi.ParameterInterlacing"
label = "P_n^(α+1,β+1) interlaces P_{n+1}^(α,β)"

[[theorems]]
name = "RealRooted.shiftedJacobiMonic_strictInterl_alpha_add_one"
module = "RealRooted.Jacobi.ParameterInterlacing"
label = "Raising α by one moves the roots to the right, interlacing"

[[theorems]]
name = "RealRooted.strictMonoOn_shiftedJacobiMonicRoot_alpha"
module = "RealRooted.Jacobi.Markoff"
label = "Markoff monotonicity in α, proved for β = 1"

[[theorems]]
name = "RealRooted.shiftedLegendreReal_eq_shiftedJacobi"
module = "RealRooted.Legendre.Basic"
label = "Shifted Legendre polynomials are the case α = β = 0"
-->

<!-- realrooted-catalog-content -->
# Shifted Jacobi polynomials

The library works on the interval $(0, 1)$. For real $\alpha, \beta$, the
shifted Jacobi polynomial is
$$
P_n^{(\alpha,\beta)}(x) = \sum_{k=0}^{n} (-1)^k
  \binom{n + \alpha}{n - k} \binom{n + \alpha + \beta + k}{k} x^k,
$$
with generalized binomial coefficients. It is the classical Jacobi polynomial
evaluated at $1 - 2x$. The monic shifted Jacobi polynomial is $P_n^{(\alpha,\beta)}$
divided by its leading coefficient $(-1)^n \binom{2n + \alpha + \beta}{n}$.

**Theorem.** Let $\alpha, \beta > -1$ and $n \ge 0$.

- $P_n^{(\alpha,\beta)}$ is real-rooted with simple roots, and every root lies
  in the open interval $(0, 1)$.
- Consecutive polynomials interlace: $P_n^{(\alpha,\beta)} \ll P_{n+1}^{(\alpha,\beta)}$.
- For every real polynomial $q$ with $\deg q < n$,
  $$\int_0^1 P_n^{(\alpha,\beta)}(x)\, q(x)\, x^\alpha (1 - x)^\beta \, dx = 0.$$
- The monic polynomials satisfy a Favard three-term recurrence with explicit
  coefficients.
- Raising both parameters gives the derivative family:
  $P_n^{(\alpha+1,\beta+1)} \ll P_{n+1}^{(\alpha,\beta)}$.
- Raising $\alpha$ alone moves the roots to the right while keeping them
  interlaced: the monic polynomial with parameters $(\alpha, \beta)$ is
  interlaced by the one with parameters $(\alpha + 1, \beta)$, both of degree $n$.

**Markoff monotonicity, for $\beta = 1$.** For each $i < n$, the $i$-th
smallest root of the monic shifted Jacobi polynomial with parameters
$(\alpha, 1)$ is strictly increasing in $\alpha$ on $(-1, \infty)$. The root
is read off the sorted root list; outside the admissible range the default
value $0$ of that lookup is irrelevant. The case of general $\beta$ is not
formalized.

The shifted Legendre polynomials of Mathlib, mapped to $\mathbb{R}$, are the
case $\alpha = \beta = 0$.

## References

C. G. J. Jacobi, “Untersuchungen über die Differentialgleichung der
hypergeometrischen Reihe,” *Journal für die reine und angewandte Mathematik*
56 (1859), 149–165;
A. Markoff, “Sur les racines de certaines équations,” *Mathematische Annalen*
27 (1886), 177–182;
G. Szegő, *Orthogonal Polynomials*, American Mathematical Society Colloquium
Publications 23 (1939), Chapters IV and VI.
The general three-term theory is on the
[Favard page](/RealRooted/theorems/favard/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Jacobi` and
`RealRooted.Legendre`.
-/
