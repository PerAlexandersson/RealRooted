module

import RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial
import RealRooted.BorceaBranden.Applications.PoissonStarFinal
import RealRooted.BorceaBranden.Applications.PoissonStarGeneral
import RealRooted.BorceaBranden.Applications.PoissonStarTransport
import RealRooted.DerivativeProduct.Kernel
import RealRooted.DerivativeProduct.KernelSufficiency
import RealRooted.DerivativeProduct.KernelWeyl
import RealRooted.DerivativeProduct.PoissonPower
import RealRooted.DerivativeProduct.ProductPower
import RealRooted.DerivativeProduct.ProductPowerCriteria
import RealRooted.DerivativeProduct.ProductPowerRoots

/-!
# Derivative products: Poisson and diamond products

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "derivative-products"
formalized = "2026-10-12"
references = [
  "Branden2006",
  "BorceaBranden2009I",
]
authors = ["Brändén", "Borcea"]
years = [2006, 2009]

[[definitions]]
name = "RealRooted.derivProductPowMap"
module = "RealRooted.DerivativeProduct.ProductPower"
label = "The linear map S_g sending t^n to the product power g^{⋆n}"

[[theorems]]
name = "RealRooted.Poisson.PreservesPF.iff"
module = "RealRooted.BorceaBranden.Applications.PoissonStarGeneral"
label = "Brändén: g ↦ f ⋆_c g preserves PF iff f is PF (c ≥ 0) or a constant ≥ 0 (c < 0)"
headline = true

[[theorems]]
name = "RealRooted.Poisson.realRootedOrZero_iff_eulerPencil_stable"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFinal"
label = "Poisson real-rootedness preservers are given by Euler-pencil stability"

[[theorems]]
name = "RealRooted.Poisson.starC_assoc"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial"
label = "The Poisson product is associative"

[[theorems]]
name = "RealRooted.assocProduct_kernel_tfae"
module = "RealRooted.DerivativeProduct.Kernel"
label = "Fixed-factor criterion: preservation holds iff g is real-rooted with w ≤ 0 on its roots"

[[theorems]]
name = "RealRooted.betaProduct_kernel_tfae"
module = "RealRooted.DerivativeProduct.Kernel"
label = "Diamond family: preservation holds iff the fixed factor has roots in [−1, 0]"

[[theorems]]
name = "RealRooted.derivProduct_isRealRootedIn_univ"
module = "RealRooted.DerivativeProduct.KernelSufficiency"
label = "Derivative products with a PF multiplier sequence preserve real-rootedness"

[[theorems]]
name = "RealRooted.sum_mul_iterate_derivative_eq_zero_or_splits"
module = "RealRooted.DerivativeProduct.KernelWeyl"
label = "Borcea–Brändén: an operator with stable Weyl symbol preserves real-rootedness"

[[theorems]]
name = "RealRooted.Poisson.poisson_affine_recurrence_strict"
module = "RealRooted.BorceaBranden.Applications.PoissonStarTransport"
label = "Rows of P(n+1) = (a + bx)P(n) + c b x P(n)′ are PF and interlace"

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_derivProductPowMap_iff"
module = "RealRooted.DerivativeProduct.ProductPowerRoots"
label = "S_g maps J-rooted inputs to T-rooted outputs iff every level g − r, r ∈ J, is T-rooted"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.Poisson.forall_isRealRootedIn_starCPowMap_Icc_iff"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "Poisson powers map [a, b]-rooted inputs to (−∞, 0]-rooted outputs iff both ends do"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_derivProductPow_iff"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "All product powers are real-rooted iff q and q ⋆ q are"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Derivative products: Poisson and diamond products

A derivative product $f\ast g=\sum_kc_kw^kf^{(k)}g^{(k)}$ deforms the ordinary product. For the
associative family, which contains Brändén's Poisson and diamond products, multiplication by a
fixed $g$ preserves real-rootedness exactly when $g$ is real-rooted and $w\le0$ at its roots.

## Results

For a weight $w=Ax^2+Bx+C$ with $A\ge0$ and $a>0$, the *associative derivative product* is
$$
f\ast g=\sum_{k\ge0}\frac{a^k\,w^k}{k!\prod_{j<k}(1+aAj)}\,f^{(k)}g^{(k)}.
$$
It is the *Poisson product* $f\star_cg=\sum_jc^jx^jf^{(j)}g^{(j)}/j!$ for $w=x$ and $a=c$,
and the *diamond product* for $w=x(x+1)$ and $a=A=1$. A polynomial is *PF* if it has
nonnegative coefficients and is zero or has only real, nonpositive roots.

**Theorem (Brändén).** [@Branden2006, Thm. 3.11] Let $c\in\mathbb R$. Then $f\star_cg$ is PF
for every PF polynomial $g$ if and only if $f$ is PF, when $c\ge0$, and if and only if $f$ is a
nonnegative constant, when $c<0$. The product $\star_c$ is associative.

**Theorem (fixed-factor criterion).** Let $g\ne0$. The following are equivalent.

1. $f\ast g$ is zero or real-rooted for every nonzero real-rooted $f$.
2. The same holds for every $f\ne0$ of degree at most one.
3. $g$ is real-rooted and $w(r)\le0$ at every root $r$ of $g$.

For the diamond family, (3) says that all roots of $g$ lie in $[-1,0]$. For the Poisson product,
(1) is also equivalent to stability of the Euler pencil $x(g+cg')+yg$ in the upper half-plane.

**Theorem (Weyl symbols; Borcea–Brändén).** [@BorceaBranden2009I, Thms. 1.3–1.4] If
$\sum_ja_j(x)(-y)^j\ne0$ whenever $\operatorname{Im}x>0$ and $\operatorname{Im}y>0$, then
$\sum_ja_jg^{(j)}$ is zero or real-rooted for every real-rooted $g$. Consequently
$\sum_k\gamma_kw^kf^{(k)}g^{(k)}/k!$ is real-rooted for every PF multiplier sequence $\gamma$
with $\gamma_0=1$, $\gamma_k>0$, when $f,g\ne0$ are real-rooted and $w\le0$ at the roots of $f$.

**Corollary (recurrences).** If $c,a_n,b_n>0$ and $P_{n+1}=(a_n+b_nx)P_n+c\,b_nxP_n'$, then
the rows are PF with simple negative roots and consecutive rows interlace.

**Theorem (product powers).** For a polynomial $g$ let $S_g$ be the linear map with
$S_g(t^n)=g^{\ast n}$. Call a polynomial *rooted in* a set if it is nonzero and real-rooted with
all roots there. If $\ast$ preserves being rooted in $T$, then $S_g$ maps polynomials rooted in
$J$ to polynomials rooted in $T$ if and only if $g-r$ is rooted in $T$ for every $r\in J$. For
the Poisson product with $c\ge0$ and $J=[u,v]$, $T=(-\infty,0]$, the two levels $g-u$ and $g-v$
suffice. Every power $q^{\ast n}$ is real-rooted if and only if $q$ and $q\ast q$ are.

## Use

The [Touchard transform](rr:touchard-transform) turns ordinary products into Poisson products,
and the falling-factorial transform turns Poisson products into ordinary ones. The
[Borcea–Brändén classification](rr:borcea-branden-classification) is the general form of the
Weyl-symbol criterion.

## Proof

The falling-factorial transform $\Phi_c$ with step $c$ satisfies
$\Phi_c(f\star_cg)=\Phi_c(f)\,\Phi_c(g)$, which gives associativity. Sufficiency in the
fixed-factor criterion comes from the stable Weyl symbol of $f\mapsto f\ast g$, since
$1/\prod_{j<k}(1+aAj)$ is a PF multiplier sequence; necessity uses the inputs $1$ and $x$. For
product powers, $S_g\bigl((t-r)p\bigr)=(g-r)\ast S_g(p)$ reduces the claim to the levels $g-r$.

## References

[@Branden2006, Thm. 3.11]; [@BorceaBranden2009I, Thms. 1.3–1.4].
<!-- /realrooted-catalog-content -->
-/
