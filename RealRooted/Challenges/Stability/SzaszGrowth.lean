module

import RealRooted.BorceaBranden.Transcendental.UniformSzasz
import RealRooted.Mathlib.Analysis.Complex.Polynomial.Szasz
import RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate

/-!
# Multivariate Szász growth bound challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "szasz-growth"
formalized = "2026-10-13"
tags = []
references = [
  "BorceaBranden2009I",
]
authors = ["Borcea", "Brändén"]
years = [2009]

[[definitions]]
name = "MvPolynomial.jensen"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate"
label = "Generalized Jensen multiplier"

[[definitions]]
name = "MvPolynomial.jensenOp"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate"
label = "Jensen-multiplier operator"

[[definitions]]
name = "MvPolynomial.szaszA"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate"
label = "The coefficient constant A"

[[definitions]]
name = "MvPolynomial.szaszC"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate"
label = "The growth constant C"

[[theorems]]
name = "Complex.sum_norm_sq_le_of_im_nonpos"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.Szasz"
label = "Univariate Szász estimate"

[[theorems]]
name = "MvPolynomial.norm_coeff_le_of_forall_jensenOp_stable"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate"
label = "Szász coefficient bound when all Jensen images are stable"

[[theorems]]
name = "MvPolynomial.norm_eval_le_of_forall_jensenOp_stable"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate"
label = "Szász growth bound on polydiscs"
headline = true

[[theorems]]
name = "RealRooted.BorceaBranden.exists_norm_eval_le_exp_sq"
module = "RealRooted.BorceaBranden.Transcendental.UniformSzasz"
label = "Uniform Szász growth bound for stable polynomials with convergent coefficients"
-->

<!-- realrooted-catalog-content -->
# The multivariate Szász growth bound

A polynomial with constant term $1$ whose Jensen-multiplier images are stable has coefficients
and polydisc growth bounded in terms of its linear and quadratic coefficients.

## Results

Throughout, $f\in\mathbb C[z_i:i\in\sigma]$ is a polynomial in finitely many variables. We write
$a(\alpha)$ for the coefficient of $z^\alpha$ in $f$, $|\alpha|=\sum_i\alpha_i$, and $e_i$ for the
$i$th unit exponent. A polynomial is *stable* if it has no zeros when all variables lie in the
open upper half-plane (see [real stability](rr:real-stability)).

For $\alpha,\beta\in\mathbb N^\sigma$ the generalized *Jensen multiplier* is
$$J(\alpha,\beta)=\prod_i\frac{(\beta_i)_{\alpha_i}}{\beta_i^{\alpha_i}}$$
(`jensen`), where $(b)_a=b(b-1)\dotsb(b-a+1)$ is the falling factorial. It is $0$ unless
$\alpha\le\beta$. The operator $J_\beta$ (`jensenOp β`) sends $z^\alpha$ to
$J(\alpha,\beta)\,z^\alpha$.
Put
$$A=\Bigl(3\Bigl(\sum_i|a(e_i)|\Bigr)^2+2\sum_{i,j}|a(e_i+e_j)|\Bigr)^{1/2},\qquad C=2e^2A^2$$
(`szaszA`, `szaszC`).

**Theorem (univariate Szász estimate).** If $\xi_1,\dotsc,\xi_k\in\mathbb C$ have
$\operatorname{Im}\xi_j\le0$, then
$$\sum_j|\xi_j|^2\le3\Bigl|\sum_j\xi_j\Bigr|^2+2\Bigl|\sum_{i<j}\xi_i\xi_j\Bigr|.$$
This applies to $\prod_j(1+\xi_jz)$ when it has no zeros in the open upper half-plane.

In the next two theorems assume that $a(0)=1$ and that $J_\beta f$ has no zeros in the open
upper half-plane for every $\beta\in\mathbb N^\sigma$. This holds for stable $f$ by
[@BorceaBranden2009I, Lemma 5.2].

**Theorem (coefficient bound).** For every $\beta$,
$$|a(\beta)|\le|\beta|^{-|\beta|/2}\Bigl(\prod_i\frac{\beta_i^{\beta_i}}{\beta_i!}\Bigr)
A^{|\beta|}.$$

**Theorem (growth on polydiscs).** If $r\ge0$ and $|z_i|\le r$ for all $i$, then
$$|f(z)|\le2^{|\sigma|}\,\frac{\sqrt{2e^2-e}}{e-1}\;e^{Cr^2},$$
where $|\sigma|$ is the number of variables.

**Theorem (uniform growth bound).** Let $\sigma$ be finite, let $a\colon\mathbb N^\sigma\to\mathbb
C$
and let $\kappa_m(\alpha)\in\mathbb R$ satisfy $\kappa_m(\alpha)\to1$ as $m\to\infty$ for every
$\alpha$. Suppose that for each $m$ the polynomial $f_m$ with coefficients
$\kappa_m(\alpha)\,a(\alpha)$
is stable or zero. Then there are real constants $B,C$ and an index $m_0$ such that
$$|f_m(z)|\le B\,e^{Cr^2}\qquad(m\ge m_0,\ r\ge0,\ |z_i|\le r\text{ for all }i).$$
Here $a$ need not have constant term $1$, and $B$ and $C$ do not depend on $m$, $r$ or $z$.

## Use

The uniform bound is the growth estimate in the stable-limit criteria (Theorem 5.1 of the paper)
behind the [Borcea–Brändén classification](rr:borcea-branden-classification).

## Proof

For the coefficient bound we set all variables equal to $t$ in $J_\beta f$, which gives a
univariate polynomial with no zeros in the open upper half-plane, constant term $1$, degree
$k=|\beta|$ (if $a(\beta)\ne0$) and leading coefficient $(\beta!/\beta^\beta)\,a(\beta)$. Writing it
as $\prod_j(1+\xi_jt)$ we have $\operatorname{Im}\xi_j\le0$. The linear and quadratic coefficients
are controlled by $a(e_i)$ and $a(e_i+e_j)$, so the Szász estimate gives $\sum_j|\xi_j|^2\le A^2$,
and the arithmetic–geometric mean inequality bounds $\prod_j|\xi_j|$ by $A^kk^{-k/2}$. The growth
bound sums the coefficient bounds over all monomials, using $\beta_i^{\beta_i}/\beta_i!\le
e^{\beta_i}$
and the Cauchy–Schwarz inequality.

For the uniform bound we induct on the number of variables occurring in the support of $a$ and on
the minimal total degree of the support, over all families $(\kappa,f)$ at once. In degree $0$ the
polynomials $f_m/f_m(0)$ have constant term $1$ and the growth bound applies uniformly in $m$.
Otherwise we write $f_m=f_m|_{z_i=0}+z_i\int_0^1\partial_if_m(z_it,\cdot)\,dt$ and apply the
induction
hypothesis to the specialization and the partial derivative. This differs from the argument in the
paper, which claims that partial differentiation always lowers the largest degree among the minimal
support elements by one; this fails for a general support.

## References

See [@BorceaBranden2009I, Lemmas 5.2 and 5.4 and Thms. 5.5 and 5.6].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The univariate estimate is in
`RealRooted.Mathlib.Analysis.Complex.Polynomial.Szasz`, the coefficient and growth bounds in
`RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate`, and the uniform bound in
`RealRooted.BorceaBranden.Transcendental.UniformSzasz`.
-/
