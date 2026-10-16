module

public import RealRooted.BorceaBranden.Transcendental.UniformSzasz
public import RealRooted.Mathlib.Analysis.Complex.Polynomial.Szasz
public import RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate

/-!
# Multivariate Szász growth bound challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "szasz-growth"
formalized = "2026-10-13"
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
label = "Szász coefficient bound (Borcea–Brändén, Lemma 5.4)"
headline = true

[[theorems]]
name = "MvPolynomial.norm_eval_le_of_forall_jensenOp_stable"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate"
label = "Szász growth bound on polydiscs (Borcea–Brändén, Theorem 5.5)"
headline = true

[[theorems]]
name = "RealRooted.BorceaBranden.exists_norm_eval_le_exp_sq"
module = "RealRooted.BorceaBranden.Transcendental.UniformSzasz"
label = "Uniform Szász growth bound for stable polynomials with convergent coefficients"
headline = true
-->

<!-- realrooted-catalog-content -->
# The multivariate Szász growth bound

Throughout, $f \in \mathbb C[z_i : i \in \sigma]$ is a polynomial in finitely many variables.
We write $a(\alpha)$ for the coefficient of $z^\alpha$ in $f$, $|\alpha| = \sum_i \alpha_i$,
and $e_i$ for the $i$th unit exponent. A polynomial is *stable* if it has no zeros when all
variables lie in the open upper half-plane (see
[real stability](/RealRooted/theorems/real-stability/)).

For $\alpha, \beta \in \mathbb N^\sigma$ the generalized **Jensen multiplier** is
$$
J(\alpha, \beta) = \prod_i \frac{(\beta_i)_{\alpha_i}}{\beta_i^{\alpha_i}},
$$
where $(b)_a = b (b-1) \dotsb (b-a+1)$ is the falling factorial (`jensen`). It is $0$ unless
$\alpha \leq \beta$. The operator $J_\beta$ (`jensenOp β`) sends $z^\alpha$ to
$J(\alpha, \beta)\, z^\alpha$. We also define
$$
A = \Bigl(3 \Bigl(\sum_i |a(e_i)|\Bigr)^2
  + 2 \sum_{i,j} |a(e_i + e_j)|\Bigr)^{1/2}, \qquad C = 2e^2 A^2 ,
$$
as `szaszA` and `szaszC`.

**Theorem** (univariate Szász estimate). If $\xi_1, \dotsc, \xi_k \in \mathbb C$ have
$\operatorname{Im} \xi_j \leq 0$, then
$$
\sum_j |\xi_j|^2 \leq 3 \Bigl|\sum_j \xi_j\Bigr|^2 + 2 \Bigl|\sum_{i<j} \xi_i \xi_j\Bigr| .
$$
This applies to a polynomial $\prod_j (1 + \xi_j z)$ with no zeros in the open upper half-plane.

In the next two theorems, assume that $a(0) = 1$ and that $J_\beta f$ is stable for every
$\beta \in \mathbb N^\sigma$. For stable $f$ this is Borcea–Brändén
[@BorceaBranden2009I, Lemma 5.2].

**Theorem** (coefficient bound). For every $\beta$,
$$
|a(\beta)| \leq |\beta|^{-|\beta|/2}
  \Bigl(\prod_i \frac{\beta_i^{\beta_i}}{\beta_i!}\Bigr) A^{|\beta|} .
$$

**Theorem** (growth on polydiscs). If $r \geq 0$ and $|z_i| \leq r$ for all $i$, then
$$
|f(z)| \leq 2^{|\sigma|}\,
  \frac{\sqrt{2e^2 - e}}{e - 1}\; e^{C r^2} ,
$$
where $|\sigma|$ is the number of variables.

**Theorem** (uniform growth bound). Let $\sigma$ be finite, let
$a \colon \mathbb N^\sigma \to \mathbb C$, and let $\kappa_m(\alpha) \in \mathbb R$
satisfy $\kappa_m(\alpha) \to 1$ as $m \to \infty$ for every $\alpha$.
Suppose that for each $m$ the polynomial $f_m$ with coefficients
$\kappa_m(\alpha)\, a(\alpha)$ is stable or zero. Then there are real constants $B, C$ and an
index $m_0$ such that
$$
|f_m(z)| \leq B\, e^{C r^2} \qquad (m \geq m_0,\ r \geq 0,\ |z_i| \leq r \text{ for all } i).
$$
Here $a$ need not have constant term $1$, and $B$ and $C$ do not depend on $m$, $r$ or $z$.

This is the growth estimate used in the proofs of the stable-limit criteria (Theorem 5.1 of
the paper) behind the
[Borcea–Brändén classification](/RealRooted/theorems/borcea-branden-classification/).

## Proof idea

For the coefficient bound, we set all variables equal to $t$ in $J_\beta f$. This gives a
univariate polynomial $g(t) = \sum_{\alpha \leq \beta} J(\alpha, \beta)\, a(\alpha)\, t^{|\alpha|}$
with no zeros in the open upper half-plane, constant term $1$, degree $k = |\beta|$ (if
$a(\beta) \neq 0$) and leading coefficient $(\beta!/\beta^\beta)\, a(\beta)$. Writing
$g = \prod_j (1 + \xi_j t)$, we have $\operatorname{Im} \xi_j \leq 0$. The linear and
quadratic coefficients of $g$ are controlled by the coefficients $a(e_i)$ and $a(e_i + e_j)$, so
the univariate Szász estimate gives $\sum_j |\xi_j|^2 \leq A^2$. The arithmetic–geometric mean
inequality then bounds the leading coefficient $\prod_j |\xi_j|$ by $A^k k^{-k/2}$.

For the growth bound, we sum the coefficient bounds over all monomials. We use
$\beta_i^{\beta_i}/\beta_i! \leq e^{\beta_i}$ and count the exponents $\beta$ of total degree $k$,
and we finish with the Cauchy–Schwarz inequality against the series of $e^{R^2/2}$.

For the uniform bound, we induct on the number of variables occurring in the support of $a$
and on the minimal total degree of the support, over all families $(\kappa, f)$ at once. If that
degree is $0$, the normalized polynomials $f_m / f_m(0)$ have constant term $1$ and the
growth bound applies, uniformly in $m$ because their coefficients converge. Otherwise we write
$f_m = f_m|_{z_i = 0} + z_i \int_0^1 \partial_i f_m(z_i t, \cdot)\, dt$ and apply the
induction hypothesis to the specialization and to the partial derivative. We note that this
induction differs from the argument in the paper, which claims that partial differentiation
always lowers the largest degree among the minimal support elements by one; this fails for a
general support.

## References

See [@BorceaBranden2009I, Lemmas 5.2 and 5.4 and Thms. 5.5 and 5.6].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The univariate estimate is in
`RealRooted.Mathlib.Analysis.Complex.Polynomial.Szasz`, the coefficient and growth bounds in
`RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate`, and the uniform bound in
`RealRooted.BorceaBranden.Transcendental.UniformSzasz`.
-/
