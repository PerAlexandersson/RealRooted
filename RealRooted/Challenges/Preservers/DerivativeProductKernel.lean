module

import RealRooted.DerivativeProduct.Kernel

/-!
# The fixed-factor criterion for associative derivative products

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
label = "Sufficiency in the fixed-factor criterion for the associative family"

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
label = "Complete fixed-factor criterion for the associative family"
headline = true
-->

<!-- realrooted-catalog-content -->
# The fixed-factor criterion for associative derivative products

For a weight $w$ and coefficients $c_k$, the derivative product is
$f\ast g=\sum_k c_k\,w^k f^{(k)}g^{(k)}$.  We take $w=AX^2+BX+C$ with $A\geq 0$ and
$c_k=a^k/\bigl(k!\prod_{j<k}(1+aAj)\bigr)$ with $a>0$; this is the associative family,
which contains the Poisson product ($A=0$, $w=X$) and the diamond family
$f\ast_\beta g=\sum_k [X(X+1)]^k f^{(k)}g^{(k)}/(k!\,(\beta)_k)$, where the diamond product is
$\beta=1$.

**Theorem.** For a nonzero real polynomial $g$, the following are equivalent.

1. The map $f\mapsto f\ast g$ sends every nonzero real-rooted polynomial to a nonzero
   real-rooted polynomial.
2. It does so for every nonzero polynomial of degree at most one.
3. $g$ is real-rooted and $w(r)\leq 0$ at every root $r$ of $g$.

For the diamond family (3) says that all roots of $g$ lie in $[-1,0]$.  No restriction on
the roots of $w$ is needed: the proof covers distinct real roots, a double root, complex roots,
a linear or constant weight (a ray, the whole line, or no admissible root), and
$w=0$.

**Sufficiency.** Write $c_k=\gamma_k/k!$.  The sequence $\gamma_k=1/(\beta)_k$ is a PF
multiplier sequence, since its Jensen polynomials are Laguerre polynomials.  The signed Weyl
symbol of $g\mapsto f\ast g$ is $\sum_j \gamma_j\,\mathrm{hasse}_j f(x)\,(-w(x)y)^j$, which is
the multiplier $\gamma$ applied to the Taylor polynomial $s\mapsto f(x+w(x)s)$.  Its roots
$s=(r-x)/w(x)$, for $r$ a root of $f$, lie in the closed upper half-plane when
$\operatorname{Im}x>0$ and $w(r)\leq 0$, because
$w(x)/(x-r)=w(r)/(x-r)+w'(r)+A(x-r)$ has nonnegative imaginary part.  A PF multiplier preserves
this root location, so the symbol is stable, and the finite-order Weyl-symbol theorem of
Borcea–Brändén gives preservation of real-rootedness.

**Necessity.** The inputs $1$ and $X$ give the pencil $g,\ F=Xg+a\,w\,g'$, and the affine
inputs give all its real combinations.  Deleting all but one copy of a root $r$ of $g$ keeps
the pencil real-rooted; its degrees differ by one and the leading coefficients are positive
multiples of each other, so the pencil is in directed proper position.  The sign rule at a
root of the left polynomial then gives $a\,m\,w(r)\,h(r)^2\leq 0$, where $m$ is the multiplicity
of $r$ and $g=(X-r)^m h$.

The Poisson case $A=0$, $w=X$ is the classification of
`RealRooted.Poisson.preservesRealRootedOrZero_iff_isAdmissible`.  The diamond family follows
Theorem 3.11 of [@Branden2006]; the Weyl-symbol criterion is Theorems 1.3 and 1.4 of
[@BorceaBranden2009I].

## References

See [@Branden2006] and [@BorceaBranden2009I].
<!-- /realrooted-catalog-content -->
-/
