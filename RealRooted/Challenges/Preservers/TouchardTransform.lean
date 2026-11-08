module

import RealRooted.Transforms.StirlingRootRegions

/-!
# The Touchard transform, PF products and grouped cubic regions

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "touchard-transform"
formalized = "2026-10-28"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.Poisson.fallingFactorialTransform_touchard"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform is inverse to the step-one falling factorial transform"

[[theorems]]
name = "RealRooted.basisTransform_touchard_mul"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform turns products into the parameter-one Poisson product"
headline = true

[[theorems]]
name = "RealRooted.isPFPolynomial_basisTransform_touchard_prod"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "Products of polynomials with PF Touchard transforms again have PF Touchard transforms"
headline = true

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
headline = true

[[theorems]]
name = "RealRooted.not_splits_basisTransform_touchard_y_sq_add_half"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform of X² + 1/2 is not real-rooted"
-->

<!-- realrooted-catalog-content -->
# The Touchard transform, PF products and grouped cubic regions

Let $T_n$ be the Touchard polynomials, $T_0=1$ and $T_{n+1}=xT_n+xT_n'$, so
$T_n(x)=\sum_kS(n,k)x^k$ with the Stirling numbers of the second kind. The
*Touchard transform* is the linear map $S$ with $S(x^n)=T_n$. It is inverse to
the step-one falling factorial transform $x^n\mapsto x(x-1)\cdots(x-n+1)$.

## Products

The Touchard transform turns ordinary products into the Poisson star product
with parameter one:
$$
S(pq)=S(p)\star_1S(q).
$$
By the preservation of PF polynomials under the Poisson star product (see the
[univariate Poisson star product](/RealRooted/theorems/univariate-poisson-star-c/) page), if each
$S(f_i)$ is a PF polynomial, then so is $S(c\prod_if_i)$ for
every $c\ge0$. A falling factorial prefix is handled by the identity
$$
S\bigl(x^{\underline m}\,p\bigr)=x^m\,S\bigl(p(x+m)\bigr),
$$
so a falling factorial times a nonnegative multiple of a product $\prod_if_i$ has
PF transform as soon as each $S\bigl(f_i(x+m)\bigr)$ is PF.

## Grouped cubic regions

A monic cubic $x^3+Ax^2+Bx+C_0$ is PF if and only if $A,B,C_0\ge0$ and its
discriminant
$A^2B^2-4B^3-4A^3C_0-27C_0^2+18ABC_0$ is nonnegative. We compute
$$
S\bigl((x+a)((x+b)^2+w)\bigr)=x^3+(3+a+2b)x^2+(1+a+2b+b^2+w+2ab)x+a(b^2+w),
$$
which gives an exact criterion for this transform to be PF. In the half-shifted
subfamily $a=b+\tfrac12$ the cubic factors as
$(x+b+\tfrac12)\bigl(x^2+(2b+3)x+b^2+w\bigr)$, and for $w\ge0$ it is PF if and only if
$$
b\ge-\tfrac12\quad\text{and}\quad w\le3b+\tfrac94 .
$$
For instance $S\bigl((x+\tfrac12)(x^2+\tfrac12)\bigr)$ is PF, while
$S(x^2+\tfrac12)$ is not real-rooted.

## What is new

The transform identities are implicit in the inverse falling factorial transform
and the Poisson product developed in this library. The root criterion follows the
spirit of Brenti, Royle and Wagner, *Location of zeros of chromatic and related
polynomials of graphs* (1994), Theorem 4.7; the grouped cubic extension was proved
here directly (RealRooted issue #2134).

## References

Brenti, Royle and Wagner, *Location of zeros of chromatic and related polynomials
of graphs* (1994), Theorem 4.7. For the Poisson product, see the
[univariate Poisson star product](/RealRooted/theorems/univariate-poisson-star-c/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Transforms.StirlingRootRegions`.
-/
