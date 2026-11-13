module

import RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial
import RealRooted.BorceaBranden.Applications.PoissonStarFinal
import RealRooted.BorceaBranden.Applications.PoissonStarGeneral
import RealRooted.BorceaBranden.Applications.PoissonStarTransport
import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar
import RealRooted.Chebyshev.Levels
import RealRooted.DerivativeProduct.PoissonPower
import RealRooted.DerivativeProduct.ProductPower
import RealRooted.DerivativeProduct.ProductPowerCriteria
import RealRooted.DerivativeProduct.ProductPowerRoots

/-!
# Poisson star product

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "univariate-poisson-star-c"
formalized = "2026-10-12"
tags = []
references = [
  "Branden2006",
]
authors = ["Brändén"]
years = [2006]

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
name = "RealRooted.Poisson.starC_comm"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "The univariate Poisson product is symmetric"

[[theorems]]
name = "RealRooted.Poisson.starC_affine_right"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Formula for affine right inputs"

[[theorems]]
name = "RealRooted.Poisson.starC_nonneg"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Nonnegative inputs give nonnegative coefficients"

[[theorems]]
name = "RealRooted.Poisson.PreservesAffineRealRooted.linear_iff"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Affine test for a single linear factor"

[[theorems]]
name = "RealRooted.Poisson.starC_root_obstruction_not_splits"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "A root of the wrong sign obstructs real-rootedness"

[[theorems]]
name = "RealRooted.Poisson.poissonSignedSymbol_stable"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Signed-symbol stability from the root-sign condition"

[[theorems]]
name = "RealRooted.Poisson.PreservesPF.iff_of_neg"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "PF preservers at a negative parameter"

[[theorems]]
name = "RealRooted.PreservesRealRootedOrZero.poissonStar_zero_iff"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Real-rootedness preservers at parameter zero"

[[theorems]]
name = "RealRooted.Poisson.PreservesPF.zero_iff"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "PF preservers at parameter zero"

[[theorems]]
name = "RealRooted.Poisson.PreservesPF.iff"
module = "RealRooted.BorceaBranden.Applications.PoissonStarGeneral"
label = "Complete PF-preserver classification for every parameter"
headline = true

[[theorems]]
name = "RealRooted.Poisson.realRootedOrZero_iff_eulerPencil_stable"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFinal"
label = "Real-rootedness preservation is equivalent to Euler-pencil stability"

[[theorems]]
name = "RealRooted.Poisson.affineRealRooted_iff_eulerPencil_stable"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFinal"
label = "Affine preservation is equivalent to Euler-pencil stability"

[[theorems]]
name = "RealRooted.Poisson.isUpperHalfPlaneStablePencil_euler_iff_isAdmissible"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFinal"
label = "Euler-pencil stability is equivalent to root-sign admissibility"

[[theorems]]
name = "RealRooted.Poisson.eulerPencil_stable_iff_signedSymbol_stable"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFinal"
label = "Euler-pencil stability is equivalent to signed-symbol stability"

[[theorems]]
name = "RealRooted.Poisson.poisson_affine_recurrence_strict"
module = "RealRooted.BorceaBranden.Applications.PoissonStarTransport"
label = "Five-way classification for positive affine Poisson recurrences"

[[theorems]]
name = "RealRooted.Poisson.fallingFactorialTransform_starC"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial"
label = "The falling-factorial transform is multiplicative for the Poisson product"

[[theorems]]
name = "RealRooted.Poisson.starC_assoc"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial"
label = "Associativity of the univariate Poisson product"

[[theorems]]
name = "RealRooted.derivProductPowMap_X_sub_C_mul"
module = "RealRooted.DerivativeProduct.ProductPower"
label = "Functional calculus: S_g((t − r) p) = (g − r) ⋆ S_g(p)"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.derivProductPowMap_mul"
module = "RealRooted.DerivativeProduct.ProductPower"
label = "For an associative product, S_g(p q) = S_g(p) ⋆ S_g(q)"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.isRealRootedIn_derivProductPowMap"
module = "RealRooted.DerivativeProduct.ProductPowerRoots"
label = "Levels rooted in a ⋆-closed class give images rooted in that class"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_derivProductPowMap_iff"
module = "RealRooted.DerivativeProduct.ProductPowerRoots"
label = "Source-interval reduction to the one-factor levels g − r"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.natDegree_derivProductPowMap"
module = "RealRooted.DerivativeProduct.ProductPowerRoots"
label = "The image of a real-rooted input has degree deg(p) deg(g)"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.leadingCoeff_derivProductPowMap"
module = "RealRooted.DerivativeProduct.ProductPowerRoots"
label = "Leading coefficient of the image for a weight with vanishing quadratic part"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.splits_sub_C_of_mem_Icc"
module = "RealRooted.Chebyshev.Levels"
label = "If two constant levels of g split, every intermediate level splits"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.Poisson.isRealRootedIn_Iic_starC"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "Polynomials rooted in (−∞, 0] are closed under the Poisson product"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.Poisson.isRealRootedIn_Iic_sub_C_of_mem_Icc"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "Two endpoint levels rooted in (−∞, 0] give all intermediate levels"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.Poisson.forall_isRealRootedIn_starCPowMap_Icc_iff"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "Poisson powers map [a, b]-rooted inputs to (−∞, 0]-rooted outputs iff both ends do"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.Poisson.forall_mapsRealRootedIn_starCPowMap_Icc_iff"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "The same criterion, degree by degree"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.Poisson.natDegree_leadingCoeff_starCPowMap"
module = "RealRooted.DerivativeProduct.PoissonPower"
label = "Degree and leading coefficient of the Poisson sequence map"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.eval_assocProduct_self_pos"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "Self-product lemma: (q ⋆ q)(x) > 0 wherever the weight is positive"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.isRealRootedIn_of_splits_assocProduct_self"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "A real-rooted self-product has all its roots in {w ≤ 0}"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.assocProduct_self_splits_iff"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "The square of left multiplication preserves real-rootedness iff q ⋆ q is real-rooted"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_derivProductPow_iff"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "All product powers are real-rooted iff q and q ⋆ q are"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_derivProductPowMap_singleton_iff"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "A singleton source root is tested by g − r and (g − r) ⋆ (g − r)"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.derivProductPowMap_realRooted_iff_of_nonpos"
module = "RealRooted.DerivativeProduct.ProductPowerCriteria"
label = "If w ≤ 0 on ℝ, the one-factor levels decide every source set"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Poisson star product

Multiplication by a fixed polynomial $f$ in the Poisson star product $\star_c$ preserves Pólya
frequency polynomials exactly when $f$ is Pólya frequency (for $c\ge0$) or a nonnegative
constant (for $c<0$). For an associative derivative product $\star$, the root location of the
images of the map $t^n\mapsto g^{\star n}$ is decided by the one-factor levels $g-r$.

## Results

For $c\in\mathbb R$ let
$$
f\star_c g=\sum_{j\ge0}\frac{c^j}{j!}\,x^jf^{(j)}g^{(j)}.
$$
This product is symmetric, associative and bilinear, has unit $1$, and equals the ordinary
product at $c=0$. A polynomial is *PF* if it has nonnegative coefficients and is zero or has
only real nonpositive roots.

**Theorem (fixed PF factors).** Let $c\in\mathbb R$. Then $f\star_cg$ is PF for every PF
polynomial $g$ if and only if $f$ is PF, when $c\ge0$, and if and only if $f$ is a nonnegative
constant, when $c<0$.

**Theorem (real-rootedness preservers).** Let $f\ne0$. The following are equivalent:

1. $f\star_cg$ is zero or real-rooted for every real-rooted $g$;
2. $f\star_c(a+bx)$ is real-rooted for all real $a,b$;
3. $f$ is real-rooted and $cr\le0$ for every root $r$ of $f$;
4. the Euler pencil $x\,(f+cf')+yf$ is stable in the upper half-plane;
5. the signed Weyl symbol $f\bigl(z(1-cw)\bigr)$ is stable.

**Theorem (product powers).** Let $\star$ be an associative derivative product
$f\star g=\sum_k\lambda_k\,\omega^kf^{(k)}g^{(k)}$ with $\omega=Ax^2+Bx+C$, $A\ge0$, $s>0$ and
$\lambda_k=s^k/\bigl(k!\prod_{j<k}(1+sAj)\bigr)$; the Poisson product $\star_s$ is the case
$\omega=x$.
For a polynomial $g$ let $S_g$ be the linear map with $S_g(t^n)=g^{\star n}$, and call a
polynomial *rooted in* a set if it is nonzero, real-rooted and has all its roots in that set.

- If $f\star q$ is rooted in $T$ whenever $f$ and $q$ are, then $S_g$ sends every polynomial
  rooted in $J$ to a polynomial rooted in $T$ if and only if $g-r$ is rooted in $T$ for every
  $r\in J$.
- For the Poisson product $\star_c$ with $c\ge0$, nonconstant $g$ and $u\le v$, the map $S_g$
  sends every polynomial rooted in $[u,v]$ to a polynomial rooted in $(-\infty,0]$ if and only
  if $g-u$ and $g-v$ are rooted in $(-\infty,0]$.
- Every power $q^{\star n}$ is real-rooted if and only if $q$ and $q\star q$ are.

The declarations below also give the degree and leading coefficient of $S_g(p)$, the case
$\omega\le0$ on $\mathbb R$, where real-rootedness of the levels $g-r$ suffices, and the affine
recurrences $P_{n+1}=(a_n+b_nx)P_n+c\,b_nxP_n'$ with $c,a_n,b_n>0$, whose rows are PF with
simple negative roots and interlace without common roots.

## Use

The fixed-factor family of derivative products is classified on the
[derivative product kernel](rr:derivative-product-kernel) page, and the
[Touchard transform](rr:touchard-transform) turns products into Poisson products.

## Proof

For $c\ge0$, sufficiency is Brändén's theorem [@Branden2006, Theorem 3.11]. The
falling-factorial transform $\Phi_c$ with step $c$ satisfies
$\Phi_c(f\star_cg)=\Phi_c(f)\,\Phi_c(g)$, which gives associativity, and a root $r$ with
$cr>0$ is excluded by $(x-r)\star_c(x-r-c)=(x-r)^2+cr$. For product powers,
$S_g\bigl((t-r)p\bigr)=(g-r)\star S_g(p)$ reduces the claim to the levels $g-r$; on an interval
all levels share the derivative $g'$, so the two endpoint levels control the others.

## References

- [@Branden2006, Theorem 3.11]
<!-- /realrooted-catalog-content -->
-/
