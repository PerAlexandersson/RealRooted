module

import RealRooted.Chebyshev.Levels
import RealRooted.DerivativeProduct.PoissonPower
import RealRooted.DerivativeProduct.ProductPower
import RealRooted.DerivativeProduct.ProductPowerCriteria
import RealRooted.DerivativeProduct.ProductPowerRoots

/-!
# Sequence maps defined by powers of an associative derivative product

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
label = "Poisson powers map [a, b]-rooted inputs to (−∞, 0]-rooted outputs iff both endpoints do"
headline = true

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
headline = true

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
# Sequence maps defined by powers of an associative derivative product

Let $\star$ be an associative derivative product
$f\star g=\sum_k c_k\,w^k f^{(k)}g^{(k)}$ with $w=AX^2+BX+C$, $A\ge0$ and
$c_k=a^k/(k!\prod_{j<k}(1+aAj))$, $a>0$ (the fixed-factor criterion of
`RealRooted.assocProduct_kernel_tfae`; the Poisson product is $A=0$, $w=X$).  For a polynomial $g$
write $g^{\star0}=1$, $g^{\star(n+1)}=g\star g^{\star n}$, and let $S_g$ be the linear map with
$S_g(t^n)=g^{\star n}$.  Put $W=\{r: w(r)\le0\}$.

**Functional calculus.** $S_g((t-r)\,p)=(g-r)\star S_g(p)$, and for an associative product $S_g$
is multiplicative, $S_g(pq)=S_g(p)\star S_g(q)$.  Hence
$S_g\bigl(A\prod_i(t-r_i)\bigr)=A\,\bigl((g-r_1)\star\cdots\star(g-r_m)\bigr)$.  If a class $T$ of
root locations is closed under $\star$, then $S_g$ sends polynomials rooted in a source set $J$ to
polynomials rooted in $T$ if and only if every level $g-r$, $r\in J$, is rooted in $T$.  For
real-rooted inputs of degree $m$ and nonconstant $g$, the image is nonzero of degree $m\deg g$,
with leading coefficient $\operatorname{lc}(p)\operatorname{lc}(g)^m$ for a weight with $A=0$.

**Poisson powers on a source interval.** For the Poisson product and a nonconstant $g$, $a\le b$:
$S_g$ sends every nonzero polynomial rooted in $[a,b]$ to a nonzero polynomial rooted in
$(-\infty,0]$ if and only if $g-a$ and $g-b$ have only nonpositive real roots.  Necessity uses the
two affine inputs $t-a$ and $t-b$.  For sufficiency, the levels $g-a$ and $g-b$ have the common
derivative $g'$, so real-rootedness of every intermediate level $g-r$ follows from the
constant-level argument for common derivatives
(`RealRooted.splits_sub_C_of_mem_Icc`); a positive point $x$ is not a root of $g-r$ because
$g(x)-a$ and $g(x)-b$ have the sign of $\operatorname{lc}(g)$ there.  The class of polynomials
rooted in $(-\infty,0]$ is closed under the Poisson product, since after normalising the leading
coefficients the product of two PF polynomials is PF.  The functional calculus finishes the proof.

**Squares and all powers.** For $q\ne0$ and $w(x)>0$,
$(q\star q)(x)=\sum_k c_k\,w(x)^k\,(q^{(k)}(x))^2>0$, since all terms are nonnegative and the top
one is positive.  So if $q\star q$ is real-rooted, its roots lie in $W$.  Consequently the following
are equivalent: the square of left multiplication, $f\mapsto q\star(q\star f)=(q\star q)\star f$,
preserves real-rootedness; $q\star q$ is real-rooted.  Moreover every product power
$q^{\star n}$ is real-rooted if and only if both $q$ and $q\star q$ are, because
$q^{\star 2m}=(q\star q)^{\star m}$ and $q^{\star(2m+1)}=(q\star q)^{\star m}\star q$.  For a
singleton source $\{r\}$, $S_g$ sends every polynomial rooted in $\{r\}$ to a real-rooted polynomial
if and only if $g-r$ and $(g-r)\star(g-r)$ are real-rooted.  If $w\le0$ on all of $\mathbb R$, the
one-factor tests $g-r$, $r\in J$, suffice for every source set $J$.

**Provenance.** The proofs on this page are new, developed for RealRooted (issues #2364, #2371 and
#2372), and are of independent research interest.  The classical input is Brändén's theorem that
Poisson multiplication by a PF polynomial preserves PF polynomials and, more generally, the
fixed-factor sufficiency for associative derivative products [@Branden2006, Thm 3.11].  The
degree-three source-interval tests for a general weight, which require continuity of ordered
roots, are not part of this page.

## References

See [@Branden2006].
<!-- /realrooted-catalog-content -->
-/
