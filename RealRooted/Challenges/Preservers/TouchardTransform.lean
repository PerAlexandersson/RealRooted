module

import RealRooted.Transforms.StirlingRootRegions

/-!
# The Touchard transform, PF products and grouped cubic regions

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "touchard-transform"
formalized = "2026-10-28"
authors = []
references = []
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.Poisson.fallingFactorialTransform_touchard"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform is inverse to the step-one falling factorial transform"

[[theorems]]
name = "RealRooted.basisTransform_touchard_mul"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform turns products into the parameter-one Poisson product"

[[theorems]]
name = "RealRooted.isPFPolynomial_basisTransform_touchard_prod"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "Products of polynomials with PF Touchard transforms again have PF Touchard transforms"

[[theorems]]
name = "RealRooted.basisTransform_touchard_fallingFactorialPolynomial_mul"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "A falling factorial prefix becomes X^m times a shift of the transform"

[[theorems]]
name = "RealRooted.isPFPolynomial_touchard_fallingFactorial_C_mul_prod"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "PF criterion for a falling factorial times a nonnegative multiple of a product"

[[theorems]]
name = "RealRooted.isPFPolynomial_monic_cubic_iff"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "A monic cubic is PF exactly when its coefficients and discriminant are nonnegative"

[[theorems]]
name = "RealRooted.isPFPolynomial_touchard_linear_mul_quadratic_iff"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "Exact coefficient and discriminant criterion for the grouped cubic (X + a)((X + b)² + w)"
headline = true

[[theorems]]
name = "RealRooted.isPFPolynomial_touchard_half_shifted_cubic_iff"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "Sharp region b ≥ -1/2 and w ≤ 3b + 9/4 for the half-shifted grouped cubic"

[[theorems]]
name = "RealRooted.not_splits_basisTransform_touchard_y_sq_add_half"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform of X² + 1/2 is not real-rooted"
-->

<!-- realrooted-catalog-content -->
# The Touchard transform, PF products and grouped cubic regions

The Touchard transform turns products into Poisson star products, which preserves PF
polynomials, and the transform of $(x+a)\bigl((x+b)^2+w\bigr)$ is PF exactly on an explicit
region.

## Results

Let $T_n$ be the Touchard polynomials, $T_0=1$ and $T_{n+1}=xT_n+xT_n'$, so that
$T_n(x)=\sum_kS(n,k)x^k$ with the Stirling numbers $S(n,k)$ of the second kind. The *Touchard
transform* is the linear map $S$ with $S(x^n)=T_n$. It is inverse to the step-one falling
factorial transform $x^n\mapsto x(x-1)\cdots(x-n+1)$. A polynomial is *PF* if it has
nonnegative coefficients and is zero or has only real, nonpositive roots.

**Theorem (products).** For all polynomials $p,q$,
$$
S(pq)=S(p)\star_1S(q),
$$
where $\star_1$ is the Poisson star product with parameter one. If each $S(f_i)$, $i\in I$,
is a PF polynomial for a finite family $(f_i)$, then $S\bigl(\prod_if_i\bigr)$ is PF. The
product is preserved by the PF-preserving property of the Poisson star product; see the
[univariate Poisson star product](/RealRooted/theorems/univariate-poisson-star-c/) page.

**Theorem (falling factorial prefix).** For $m\in\mathbb N$ and a polynomial $p$,
$$
S\bigl(x^{\underline m}\,p\bigr)=x^m\,S\bigl(p(x+m)\bigr).
$$
Hence, if $c\ge0$ and each $S\bigl(f_i(x+m)\bigr)$ is PF, then
$S\bigl(x^{\underline m}\cdot c\prod_if_i\bigr)$ is PF.

**Theorem (cubic criterion).** A monic cubic $x^3+Ax^2+Bx+C_0$ is PF if and only if
$A,B,C_0\ge0$ and its discriminant $A^2B^2-4B^3-4A^3C_0-27C_0^2+18ABC_0$ is nonnegative.

**Theorem (grouped cubic).** For real $a,b,w$,
$$
S\bigl((x+a)((x+b)^2+w)\bigr)=x^3+(3+a+2b)x^2+(1+a+2b+b^2+w+2ab)x+a(b^2+w),
$$
and this is PF if and only if its coefficients $A,B,C_0$ satisfy the cubic criterion. For
$w\ge0$ and $a=b+\tfrac12$,
$$
S\bigl((x+b+\tfrac12)((x+b)^2+w)\bigr)\text{ is PF}\iff b\ge-\tfrac12\text{ and }w\le3b+\tfrac94 .
$$
For example, $S\bigl((x+\tfrac12)(x^2+\tfrac12)\bigr)$ is PF, while $S(x^2+\tfrac12)$ is not
real-rooted.

## References

The root criterion is in the spirit of Brenti, Royle and Wagner, *Location of zeros of
chromatic and related polynomials of graphs* (1994), Theorem 4.7. For the Poisson product, see
the [univariate Poisson star product](/RealRooted/theorems/univariate-poisson-star-c/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Transforms.StirlingRootRegions`.
-/
