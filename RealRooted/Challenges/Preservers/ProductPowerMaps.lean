module

import RealRooted.Chebyshev.Levels
import RealRooted.DerivativeProduct.PoissonPower
import RealRooted.DerivativeProduct.ProductPower
import RealRooted.DerivativeProduct.ProductPowerCriteria
import RealRooted.DerivativeProduct.ProductPowerRoots

/-!
# Real roots of sequence maps t^n ↦ g^{⋆n} for derivative products

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "product-power-maps"
formalized = "2026-11-09"
references = [
  "Branden2006",
]
authors = ["Brändén"]
years = [2006]
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.derivProductPow"
module = "RealRooted.DerivativeProduct.ProductPower"
label = "The product power g^{⋆n} of a derivative product"

[[definitions]]
name = "RealRooted.derivProductPowMap"
module = "RealRooted.DerivativeProduct.ProductPower"
label = "The linear map S_g sending t^n to the product power g^{⋆n}"

[[definitions]]
name = "RealRooted.Poisson.starCPowMap"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "The map S_g for the Poisson product"

[[theorems]]
name = "RealRooted.derivProductPowMap_X_sub_C_mul"
module = "RealRooted.DerivativeProduct.ProductPower"
label = "Functional calculus: S_g((t − r) p) = (g − r) ⋆ S_g(p)"

[[theorems]]
name = "RealRooted.derivProductPowMap_mul"
module = "RealRooted.DerivativeProduct.ProductPower"
label = "For an associative product, S_g(p q) = S_g(p) ⋆ S_g(q)"

[[theorems]]
name = "RealRooted.isRealRootedIn_derivProductPowMap"
module = "RealRooted.DerivativeProduct.ProductPowerRoots"
label = "Levels rooted in a ⋆-closed class give images rooted in that class"

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_derivProductPowMap_iff"
module = "RealRooted.DerivativeProduct.ProductPowerRoots"
label = "Source-interval reduction to the one-factor levels g − r"

[[theorems]]
name = "RealRooted.natDegree_derivProductPowMap"
module = "RealRooted.DerivativeProduct.ProductPowerRoots"
label = "The image of a real-rooted input has degree deg(p) deg(g)"

[[theorems]]
name = "RealRooted.leadingCoeff_derivProductPowMap"
module = "RealRooted.DerivativeProduct.ProductPowerRoots"
label = "Leading coefficient of the image for a weight with vanishing quadratic part"

[[theorems]]
name = "RealRooted.splits_sub_C_of_mem_Icc"
module = "RealRooted.Chebyshev.Levels"
label = "If two constant levels of g split, every intermediate level splits"

[[theorems]]
name = "RealRooted.Poisson.isRealRootedIn_Iic_starC"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "Polynomials rooted in (−∞, 0] are closed under the Poisson product"

[[theorems]]
name = "RealRooted.Poisson.isRealRootedIn_Iic_sub_C_of_mem_Icc"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "Two endpoint levels rooted in (−∞, 0] give all intermediate levels"

[[theorems]]
name = "RealRooted.Poisson.forall_isRealRootedIn_starCPowMap_Icc_iff"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "Poisson powers map [a, b]-rooted inputs to (−∞, 0]-rooted outputs iff both ends do"

[[theorems]]
name = "RealRooted.Poisson.forall_mapsRealRootedIn_starCPowMap_Icc_iff"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "The same criterion in the vocabulary of MapsRealRootedIn"

[[theorems]]
name = "RealRooted.Poisson.natDegree_leadingCoeff_starCPowMap"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "Degree and leading coefficient of the Poisson sequence map"

[[theorems]]
name = "RealRooted.eval_assocProduct_self_pos"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "Self-product lemma: (q ⋆ q)(x) > 0 wherever the weight is positive"

[[theorems]]
name = "RealRooted.isRealRootedIn_of_splits_assocProduct_self"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "A real-rooted self-product has all its roots in {w ≤ 0}"

[[theorems]]
name = "RealRooted.assocProduct_self_splits_iff"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "The square of left multiplication preserves real-rootedness iff q ⋆ q is real-rooted"

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_derivProductPow_iff"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "All product powers are real-rooted iff q and q ⋆ q are"
headline = true

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_derivProductPowMap_singleton_iff"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "A singleton source root is tested by g − r and (g − r) ⋆ (g − r)"

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_derivProductPowMap_iff_of_forall_nonpos"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "Weights with W = ℝ: one-factor tests suffice on every source set"
-->

<!-- realrooted-catalog-content -->
# Real roots of sequence maps t^n ↦ g^{⋆n} for derivative products

For an associative derivative product $\star$, the map $t^n\mapsto g^{\star n}$ sends
polynomials rooted in $J$ to real-rooted polynomials if and only if every level $g-r$,
$r\in J$, is real-rooted; for the Poisson product and an interval $J$, the two endpoint levels
suffice.

## Results

Let $\star$ be the associative derivative product
$f\star g=\sum_k c_k\,w^k f^{(k)}g^{(k)}$ with $w=Ax^2+Bx+C$, $A\ge0$ and
$c_k=a^k/(k!\prod_{j<k}(1+aAj))$, $a>0$; this is the fixed-factor family of
`RealRooted.assocProduct_kernel_tfae`, and the Poisson product is $A=0$, $w=x$. For a
polynomial $g$ put $g^{\star0}=1$ and $g^{\star(n+1)}=g\star g^{\star n}$, and let $S_g$ be
the linear map with $S_g(t^n)=g^{\star n}$. Let $W=\{r: w(r)\le0\}$. A polynomial is *rooted
in* a set $T$ if it is nonzero, real-rooted and has all roots in $T$.

**Theorem (functional calculus).** $S_g((t-r)\,p)=(g-r)\star S_g(p)$. If $\star$ is
associative, then $S_g(pq)=S_g(p)\star S_g(q)$. Hence
$S_g\bigl(A\prod_i(t-r_i)\bigr)=A\,\bigl((g-r_1)\star\cdots\star(g-r_m)\bigr)$.

**Theorem (source-interval reduction).** Let $T$ be a set of real numbers such that
$f\star q$ is rooted in $T$ whenever $f,q$ are. For any set $J$, the map $S_g$ sends every
polynomial rooted in $J$ to a polynomial rooted in $T$ if and only if $g-r$ is rooted in $T$
for every $r\in J$.

**Theorem (degree and leading coefficient).** Let $g$ be nonconstant and let $p$ be
rooted in some set. Then $S_g(p)\ne0$ and $\deg S_g(p)=\deg p\cdot\deg g$.
If $A=0$, then $\operatorname{lc}(S_g(p))=\operatorname{lc}(p)\operatorname{lc}(g)^{\deg p}$.

**Theorem (Poisson powers on an interval).** Let $f\star g=\sum_k\lambda^kx^kf^{(k)}g^{(k)}/k!$
with $\lambda\ge0$. Let $g$ be nonconstant and $a\le b$. Then $S_g$ sends every polynomial
rooted in $[a,b]$ to a polynomial rooted in $(-\infty,0]$ if and only if $g-a$ and $g-b$ are
rooted in $(-\infty,0]$. Equivalently, for every $n$, $S_g$ sends each polynomial of degree at
most $n$ rooted in $[a,b]$ to zero or to a polynomial rooted in $(-\infty,0]$. The class of
polynomials rooted in $(-\infty,0]$ is closed under the Poisson product.

**Lemma (intermediate levels).** Let $g$ be nonconstant. If $g-a$ and $g-b$ split, then
$g-s$ splits for every $s\in[a,b]$. If moreover $g-a$ and $g-b$ are rooted in
$(-\infty,0]$ and $r\in[a,b]$, then $g-r$ is rooted in $(-\infty,0]$.

**Theorem (squares and all powers).** Let $a>0$, let $w$ have degree at most $2$ with
$A\ge0$, and let $q\ne0$.

- If $w(x)>0$, then $(q\star q)(x)=\sum_k c_k\,w(x)^k\,(q^{(k)}(x))^2>0$. So if $q\star q$ is
  real-rooted, all its roots lie in $W$.
- The map $f\mapsto q\star(q\star f)$ sends real-rooted polynomials to real-rooted polynomials
  if and only if $q\star q$ splits.
- Every power $q^{\star n}$, $n\ge0$, is real-rooted if and only if $q$ and $q\star q$ both
  split.
- For $g-r\ne0$, the map $S_g$ sends every polynomial rooted in $\{r\}$ to a real-rooted
  polynomial if and only if $g-r$ and $(g-r)\star(g-r)$ split.
- If $w(x)\le0$ for all real $x$, then $S_g$ sends every polynomial rooted in a set $J$ to a
  real-rooted polynomial if and only if $g-r$ is real-rooted for every $r\in J$.

## Proof

For the Poisson interval theorem, necessity uses the inputs $t-a$ and $t-b$. For sufficiency,
the levels $g-a$ and $g-b$ have the same derivative $g'$, which gives real-rootedness of every
level $g-r$ with $r\in[a,b]$; a positive point $x$ is not a root of $g-r$ because $g(x)-a$
and $g(x)-b$ have the sign of $\operatorname{lc}(g)$ there. Closure under the Poisson
product follows from the fact that, after normalizing leading coefficients, the product of two
PF polynomials is PF. The functional calculus finishes the proof. For all powers,
$q^{\star2m}=(q\star q)^{\star m}$ and $q^{\star(2m+1)}=(q\star q)^{\star m}\star q$.

## References

Brändén's theorem that Poisson multiplication by a PF polynomial preserves PF polynomials,
and the fixed-factor sufficiency for associative derivative products, are in
[@Branden2006, Thm 3.11].
<!-- /realrooted-catalog-content -->
-/
