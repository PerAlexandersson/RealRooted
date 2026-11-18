module

import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol
import RealRooted.BorceaBranden.FiniteOrderWeylPreserver
import RealRooted.BorceaBranden.FiniteSymbolClassification
import RealRooted.BorceaBranden.RealFiniteClassificationIff
import RealRooted.BorceaBranden.Transcendental.ComplexClassification
import RealRooted.BorceaBranden.Transcendental.PivotForward
import RealRooted.BorceaBranden.Transcendental.RealClassification
import RealRooted.BorceaBranden.Transcendental.UniformSzasz
import RealRooted.Mathlib.Analysis.Complex.Polynomial.Szasz
import RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate

/-!
# Borcea–Brändén classification of stability preservers

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "borcea-branden-classification"
formalized = "2026-10-13"
references = [
  "BorceaBranden2009I",
]
authors = ["Borcea", "Brändén", "Szász"]
years = [1943, 2009]

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesComplexStability"
module = "RealRooted.BorceaBranden.Transcendental.ComplexClassification"
label = "Complex stability preserver"

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesRealStability"
module = "RealRooted.BorceaBranden.Transcendental.RealOperatorBasics"
label = "Real stability preserver"

[[theorems]]
name = "RealRooted.BorceaBranden.finiteComplexSymbolClassification"
module = "RealRooted.BorceaBranden.FiniteSymbolClassification"
label = "On a degree box: stability preserver iff rank one with stable range or stable symbol"

[[theorems]]
name = "RealRooted.BorceaBranden.realStabilityOnDegreeBox_iff_rankTwo_or_stable_symbol"
module = "RealRooted.BorceaBranden.RealFiniteClassificationIff"
label = "On a degree box: real stability preserver iff rank two or a real stable symbol"
symcat = "borceaBrandenFiniteSymbol"

[[theorems]]
name = "RealRooted.BorceaBranden.complexStability_iff_rankOne_or_stableLimit_symbol"
module = "RealRooted.BorceaBranden.Transcendental.ComplexClassification"
label = "Stability preserver iff rank one or the symbol is a limit of stable polynomials"

[[theorems]]
name = "RealRooted.BorceaBranden.realStability_iff_rankTwo_or_stableLimit_signedSymbol"
module = "RealRooted.BorceaBranden.Transcendental.RealClassification"
label = "Borcea–Brändén: real stability preserver iff rank two or a real stable-limit symbol"
headline = true
symcat = "borceaBrandenTranscendentalSymbol"

[[theorems]]
name = "RealRooted.BorceaBranden.isComplexStableLimit_iff_fallingFactorial_glue_stable"
module = "RealRooted.BorceaBranden.Transcendental.PivotForward"
label = "A series is a limit of stable polynomials iff all its weighted truncations are stable"

[[theorems]]
name = "RealRooted.BorceaBranden.PreservesRealRootedUpTo.of_finiteSymbol"
module = "RealRooted.BorceaBranden.Applications.RealUnivariateSymbol"
label = "A real stable symbol $T((x + y)^d)$ gives a real-rootedness preserver up to degree $d$"

[[theorems]]
name = "RealRooted.MvUpperHalfPlaneStable.finiteOrderWeylOperator"
module = "RealRooted.BorceaBranden.FiniteOrderWeylPreserver"
label = "Σ Qⱼ ∂ʲ preserves stability when Σ Qⱼ(z)(−w)ʲ is stable"

[[theorems]]
name = "Complex.sum_norm_sq_le_of_im_nonpos"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.Szasz"
label = "Szász: Σ|ξⱼ|² ≤ 3|Σ ξⱼ|² + 2|Σ ξᵢξⱼ| when every Im ξⱼ ≤ 0"

[[theorems]]
name = "MvPolynomial.norm_eval_le_of_forall_jensenOp_stable"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SzaszMultivariate"
label = "Szász growth bound for stable polynomials on polydiscs"

[[theorems]]
name = "RealRooted.BorceaBranden.exists_norm_eval_le_exp_sq"
module = "RealRooted.BorceaBranden.Transcendental.UniformSzasz"
label = "Limits of stable polynomials grow at most like exp(Cr²)"
-->

<!-- realrooted-catalog-content -->
# Borcea–Brändén classification of stability preservers

A linear operator on polynomials in finitely many variables preserves stability if and only if
it has rank at most one (two, in the real case) with a stable range, or its symbol is stable or
a limit of stable polynomials. This solves the multivariate form of the problem that Pólya and
Schur solved for diagonal operators.

## Results

A polynomial in $z=(z_i)_{i\in\sigma}$, $\sigma$ finite, is *stable* if it has no zero with
every $z_i$ in the open upper half-plane, and *real stable* if moreover its coefficients are
real. An operator *preserves* (real) stability if it maps (real) stable polynomials to (real)
stable polynomials or to zero. The *algebraic symbol* of $T$ on the degree box
$\kappa\in\mathbb N^\sigma$ is $T\bigl[\prod_i(z_i+w_i)^{\kappa_i}\bigr]$, and the
*transcendental symbol* is
$$
T\bigl[e^{-z\cdot w}\bigr]=\sum_\alpha(-1)^{|\alpha|}\,T(z^\alpha)\,\frac{w^\alpha}{\alpha!},
$$
with $T$ acting on $z$.

**Theorem (Borcea–Brändén).** [@BorceaBranden2009I, Thms. 1.1–1.4] Let $T$ be a linear
operator on polynomials in $z$.

1. A complex-linear $T$ on the polynomials of degree at most $\kappa_i$ in each $z_i$
   preserves stability if and only if $Tf=\varphi(f)P$ for a linear functional $\varphi$ and a
   stable $P$, or its algebraic symbol is stable.
2. A real-linear $T$ on this degree box preserves real stability if and only if
   $Tf=\varphi(f)P+\psi(f)Q$, where every real combination of $P$ and $Q$ is real stable or
   zero, or one of $T\bigl[\prod_i(z_i\pm w_i)^{\kappa_i}\bigr]$ is real stable.
3. A complex-linear $T$ on all polynomials preserves stability if and only if it has the
   rank-one form, or its transcendental symbol is a locally uniform limit of stable
   polynomials.
4. A real-linear $T$ on all polynomials preserves real stability if and only if it has the
   rank-two form, or its transcendental symbol or the same series with $w$ replaced by $-w$ is
   a locally uniform limit of real stable polynomials.

**Theorem (stable limits).** [@BorceaBranden2009I, Thm. 5.1] A series
$\sum_\alpha P_\alpha(z)\,w^\alpha$ is a locally uniform limit of stable polynomials if and
only if every truncation
$\sum_{\alpha\le\beta}\prod_i\binom{\beta_i}{\alpha_i}\alpha_i!\,P_\alpha(z)\,w^\alpha$ is
stable or zero.

**Corollary (preservers).** If $T$ is a real-linear operator on $\mathbb R[x]$ and
$T\bigl[(x+y)^d\bigr]$ is real stable, then $T$ maps real-rooted polynomials of degree at most
$d$ to real-rooted polynomials or zero. If $\sum_jQ_j(z)(-w)^j$ is stable, then
$\sum_jQ_j(z)\,\partial_q^j$ preserves stability in every degree.

**Theorem (Szász).** If $\xi_1,\dots,\xi_k\in\mathbb C$ have $\operatorname{Im}\xi_j\le0$,
then $\sum_j|\xi_j|^2\le3\bigl|\sum_j\xi_j\bigr|^2+2\bigl|\sum_{i<j}\xi_i\xi_j\bigr|$. Hence
a stable $f$ with $f(0)=1$ satisfies $|f(z)|\le Be^{Cr^2}$ on the polydisc $|z_i|\le r$, with
$B,C$ depending only on the number of variables and the coefficients of degree at most $2$.
The same bound holds uniformly for stable polynomials with coefficients $\kappa_m(\alpha)a(\alpha)$,
where $\kappa_m(\alpha)\to1$ for every $\alpha$ [@BorceaBranden2009I, Thms. 5.5 and 5.6].

## Use

The univariate corollary is the standard way to show that an operator preserves
real-rootedness: compute one bivariate polynomial and check that it is real stable. It gives
the [Pólya–Schur theorem](rr:multiplier-sequences), the
[Hermite–Kakeya–Obreschkoff theorem](rr:hermite-kakeya-obreschkoff) in several variables and
the [derivative products](rr:derivative-products).

## Proof

Szász's bound controls the growth of stable polynomials, which is what allows passing from
symbols on degree boxes to the transcendental symbol. The uniform growth bound is proved by
induction on the number of variables in the support and on its minimal total degree, writing
$f_m=f_m|_{z_i=0}+z_i\int_0^1\partial_if_m(z_it,\cdot)\,dt$. This replaces a step in
[@BorceaBranden2009I, Thm. 5.6], which assumes that partial differentiation lowers the largest
degree among the minimal exponents of the support by one; that fails for a general support.

## References

[@BorceaBranden2009I]; O. Szász, “On sequences of polynomials and the distribution of their
zeros,” *Bull. Amer. Math. Soc.* 49 (1943), 377–383. See also the
[finite-symbol](sf:borceaBrandenFiniteSymbol) and
[transcendental-symbol](sf:borceaBrandenTranscendentalSymbol) classifications on
symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
