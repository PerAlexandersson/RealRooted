module

import RealRooted.DerivativeProduct.Kernel

/-!
# Associative derivative products with a fixed factor

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "derivative-product-kernel"
formalized = "2026-11-09"
tags = []
references = [
  "Branden2006",
  "BorceaBranden2009I",
]
authors = ["Brändén", "Borcea"]
years = [2006, 2009]

[[theorems]]
name = "RealRooted.sum_mul_iterate_derivative_eq_zero_or_splits"
module = "RealRooted.DerivativeProduct.KernelWeyl"
label = "A differential operator with stable Weyl symbol preserves real-rootedness"

[[theorems]]
name = "RealRooted.derivProduct_isRealRootedIn_univ"
module = "RealRooted.DerivativeProduct.KernelSufficiency"
label = "Derivative products with a PF multiplier sequence preserve real-rootedness"

[[theorems]]
name = "RealRooted.betaProduct_isRealRootedIn_univ"
module = "RealRooted.DerivativeProduct.KernelSufficiency"
label = "The diamond family with a kernel rooted in [−1, 0] preserves real-rootedness"

[[theorems]]
name = "RealRooted.assocProduct_isRealRootedIn_univ"
module = "RealRooted.DerivativeProduct.KernelSufficiency"
label = "Associative product with a kernel having w ≤ 0 at its roots preserves real-rootedness"

[[theorems]]
name = "RealRooted.isRealRootedIn_of_splits_derivProduct_affine"
module = "RealRooted.DerivativeProduct.KernelNecessity"
label = "Real-rooted outputs on affine inputs force the roots into the set where w ≤ 0"

[[theorems]]
name = "RealRooted.betaProduct_kernel_tfae"
module = "RealRooted.DerivativeProduct.Kernel"
label = "Kernel characterization of the diamond family: roots in [−1, 0]"

[[theorems]]
name = "RealRooted.assocProduct_kernel_tfae"
module = "RealRooted.DerivativeProduct.Kernel"
label = "Fixed-factor criterion: preservation holds iff g is real-rooted with w ≤ 0 on its roots"
headline = true
-->

<!-- realrooted-catalog-content -->
# Associative derivative products with a fixed factor

A fixed polynomial $g$ gives a real-rootedness preserver $f\mapsto f\ast g$ for the associative
derivative product exactly when $g$ is real-rooted and $w\le0$ at its roots. The family contains
the Poisson product and the diamond product.

## Results

For a weight $w$ and coefficients $c_k$, the *derivative product* is
$$
f\ast g=\sum_k c_k\,w^kf^{(k)}g^{(k)}.
$$
The *associative family* has $w=Ax^2+Bx+C$ with $A\ge0$ and
$c_k=a^k/\bigl(k!\prod_{j<k}(1+aAj)\bigr)$ with $a>0$. It contains the Poisson product
($A=0$, $w=x$) and the *diamond family*
$$
f\ast_\beta g=\sum_k\frac{[x(x+1)]^k}{k!\,(\beta)_k}\,f^{(k)}g^{(k)},\qquad
(\beta)_k=\beta(\beta+1)\dotsm(\beta+k-1),
$$
for $\beta>0$; the diamond product is $\beta=1$.

**Theorem (fixed-factor criterion).** Let $g\ne0$ be a real polynomial. The following are
equivalent.

1. For every real-rooted polynomial $f\ne0$, $f\ast g=0$ or $f\ast g$ is real-rooted.
2. The same holds for every $f\ne0$ of degree at most one.
3. $g$ is real-rooted and $w(r)\le0$ at every root $r$ of $g$.

When (3) holds and $f\ne0$ is real-rooted, $f\ast g\ne0$. For the diamond family, (3) says that
all roots of $g$ lie in $[-1,0]$.

**Theorem (sufficiency).** Let $\gamma$ be a PF multiplier sequence with $\gamma_0=1$ and
$\gamma_k>0$, let $w$ have degree at most two with $A\ge0$, let $f\ne0$ be real-rooted with
$w\le0$ at its roots, and let $g\ne0$ be real-rooted. Then
$\sum_k\frac{\gamma_k}{k!}\,w^kf^{(k)}g^{(k)}$ is nonzero and real-rooted. The same holds for
$f\ast g$ in the associative family with $a>0$, and for $f\ast_\beta g$ with $\beta>0$ and $f$
real-rooted with all roots in $[-1,0]$.

**Theorem (necessity).** Let $c_0=1$, $c_k\ge0$ and $c_1>0$, let $w$ have degree at most two
and $A\ge0$, and let $g\ne0$. If $g\ast(\alpha+\beta x)$ is zero or real-rooted for all real
$\alpha,\beta$, then $g$ is real-rooted and $w\le0$ at its roots.

**Theorem (Weyl symbols; Borcea–Brändén).** Let $a_0,\dotsc,a_m$ be real polynomials such that
$\sum_j a_j(x)(-y)^j\ne0$ whenever $\operatorname{Im}x>0$ and $\operatorname{Im}y>0$. For every
real-rooted $g\ne0$, the polynomial $\sum_j a_jg^{(j)}$ is zero or real-rooted.

## Proof

For sufficiency, the sequence $1/(\beta)_k$ is a PF multiplier sequence, which makes the Weyl
symbol of $g\mapsto f\ast g$ stable when $w\le0$ at the roots of $f$. Necessity uses the pencil
spanned by $g$ and $xg+a\,w\,g'$, which arises from the inputs $1$ and $x$.

## References

- [@Branden2006, Thm. 3.11], for the diamond family
- [@BorceaBranden2009I, Thms. 1.3–1.4], for the Weyl-symbol criterion
<!-- /realrooted-catalog-content -->
-/
