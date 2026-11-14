module

import RealRooted.DerivativeProduct.DiamondIntervals
import RealRooted.RootLocation.DerivativeSigns
import RealRooted.RootLocation.Pairing
import RealRooted.Transforms.BrandenE.RootDomain
import RealRooted.Transforms.StirlingRootRegions
import RealRooted.Transforms.StirlingRootRegions.Parabolic
import RealRooted.Transforms.TouchardRootDomain

/-!
# Touchard transform

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "touchard-transform"
formalized = "2026-11-09"
authors = ["Brändén", "Brenti", "Royle", "Wagner"]
years = [1994, 2006]
references = [
  "Branden2006",
]
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.forall_splits_basisTransform_touchard_iff"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The Touchard transform of every polynomial rooted in J is real-rooted iff J ⊆ (−∞, 1/4]"
headline = true

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_Iic_basisTransform_touchard_iff"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The upper ray (−∞, c] is invariant under the Touchard transform iff 0 ≤ c ≤ 1/4"

[[theorems]]
name = "RealRooted.forall_splits_brandenE_iff"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The E transform of every polynomial rooted in J is real-rooted iff J ⊆ [L, U]"

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_Icc_brandenE_iff"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The interval [A, B] is invariant under the E transform iff L ≤ A ≤ −1 and 0 ≤ B ≤ U"

[[theorems]]
name = "RealRooted.isRealRootedIn_Iic_quarter_of_touchard_recurrence"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "Rows of the recurrence P_{n+1} = (x + a) P_n + x P_n′ with a ≥ −1/4 have roots ≤ 1/4"

[[theorems]]
name = "RealRooted.isRealRootedIn_Icc_of_brandenE_recurrence"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "Rows of the Euler type recurrence with (1 − √2)/2 ≤ a ≤ (1 + √2)/2 are rooted in [L, U]"

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
name = "RealRooted.StirlingRootRegion.isPFPolynomial_fallingFactorial_mul"
module = "RealRooted.Transforms.StirlingRootRegions.Parabolic"
label = "Brenti–Royle–Wagner: the closed parabolic root criterion gives a PF Stirling transform"

[[theorems]]
name = "RealRooted.StirlingRootRegion.isPFPolynomial_fallingFactorial_two_mul"
module = "RealRooted.Transforms.StirlingRootRegions.Parabolic"
label = "Roots in the closed disk about one give a PF transform with a falling factorial prefix"

[[theorems]]
name = "RealRooted.StirlingRootRegion.isPFPolynomial_cycle"
module = "RealRooted.Transforms.StirlingRootRegions.Parabolic"
label = "Brenti–Royle–Wagner: the Stirling transform of the cycle chromatic polynomial is PF"
objects = ["Cycle graph partition polynomials"]
property = "pf"

[[theorems]]
name = "RealRooted.isPFPolynomial_monic_cubic_iff"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "A monic cubic is PF exactly when its coefficients and discriminant are nonnegative"

[[theorems]]
name = "RealRooted.isPFPolynomial_touchard_linear_mul_quadratic_iff"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "Exact coefficient and discriminant criterion for the grouped cubic (X + a)((X + b)² + w)"

[[theorems]]
name = "RealRooted.isPFPolynomial_touchard_half_shifted_cubic_iff"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "Sharp region b ≥ -1/2 and w ≤ 3b + 9/4 for the half-shifted grouped cubic"

[[theorems]]
name = "RealRooted.not_splits_basisTransform_touchard_y_sq_add_half"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform of X² + 1/2 is not real-rooted"

[[theorems]]
name = "RealRooted.betaProduct_one_isRealRootedIn_Icc"
module = "RealRooted.DerivativeProduct.DiamondIntervals"
label = "The diamond product of a [−1, 0]-rooted and a [A, B]-rooted polynomial is [A, B]-rooted"

[[theorems]]
name = "RealRooted.IsRealRootedIn.basisTransform_touchard"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The Touchard transform of a polynomial rooted in (−∞, 1/4] is real-rooted"

[[theorems]]
name = "RealRooted.IsRealRootedIn.basisTransform_touchard_Iic"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The Touchard transform preserves root location in (−∞, c] for 0 ≤ c ≤ 1/4"

[[theorems]]
name = "RealRooted.exists_eq_C_mul_mul_of_isRealRootedIn_Iic_quarter"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "Pairing of positive roots: all but at most one factor has a PF Touchard image"

[[theorems]]
name = "RealRooted.not_splits_basisTransform_touchard_X_sub_C_sq"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The Touchard transform of (X − r)² is not real-rooted for r > 1/4"

[[theorems]]
name = "RealRooted.IsRealRootedIn.brandenE_Icc"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The E transform preserves root location in [A, B] for L ≤ A ≤ −1 and 0 ≤ B ≤ U"

[[theorems]]
name = "RealRooted.exists_eq_C_mul_mul_of_isRealRootedIn_Icc"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "Pairing of roots: all but at most one positive and one negative factor are admissible"

[[theorems]]
name = "RealRooted.splits_brandenE_X_sub_C_sq_iff"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The E transform of (X − r)² is real-rooted iff r ∈ [L, U]"

[[theorems]]
name = "RealRooted.exists_rootPolynomial_eq_mul_of_pairs"
module = "RealRooted.RootLocation.Pairing"
label = "Pairing the linear factors of a root polynomial inside a multiplicative class"

[[theorems]]
name = "RealRooted.IsRealRootedIn.leadingCoeff_mul_eval_iterate_derivative_nonneg"
module = "RealRooted.RootLocation.DerivativeSigns"
label = "Derivatives to the right of all roots have the sign of the leading coefficient"
-->

<!-- realrooted-catalog-content -->
# Touchard transform

The Touchard transform $t^n\mapsto\sum_kS(n,k)x^k$ sends every polynomial with roots in a set $J$
to a real-rooted polynomial exactly when $J\subseteq(-\infty,1/4]$. Brändén's ordered Bell
transform does so exactly when $J\subseteq[L,U]$, with $L=-\frac{1+\sqrt2}2$ and
$U=\frac{\sqrt2-1}2$. Neither transform preserves real-rootedness in general.

## Results

The *Touchard transform* $\mathcal T$ is the linear map with
$\mathcal T(t^n)=T_n(x)=\sum_kS(n,k)x^k$, where $S(n,k)$ are the Stirling numbers of the second
kind; equivalently $\mathcal T(t^{\underline n})=x^n$, with $t^{\underline n}=t(t-1)\dotsm(t-n+1)$.
It turns multiplication into the Poisson product:
$$
\mathcal T(pq)=\mathcal T(p)\star\mathcal T(q),\qquad
(F\star G)(x)=\sum_{k\ge0}\frac{x^k}{k!}F^{(k)}(x)G^{(k)}(x).
$$
Brändén's *ordered Bell transform* $E$, with $E\binom tn=x^n$, turns multiplication into the
diamond product $(F\diamond G)(x)=\sum_{k\ge0}\frac{[x(x+1)]^k}{(k!)^2}F^{(k)}(x)G^{(k)}(x)$.
A polynomial is *rooted in* a set $S$ if it is nonzero, real-rooted and has all its roots in
$S$; nonzero constants are rooted in every set.

**Theorem (root domains).** Let $J\subseteq\mathbb R$.

1. $\mathcal T$ sends every polynomial rooted in $J$ to a real-rooted polynomial if and only if
   $J\subseteq(-\infty,1/4]$.
2. $E$ sends every polynomial rooted in $J$ to a real-rooted polynomial if and only if
   $J\subseteq[L,U]$.
3. For $c\in\mathbb R$, $\mathcal T$ maps the polynomials rooted in $(-\infty,c]$ to themselves
   if and only if $0\le c\le1/4$.
4. For $A\le B$, $E$ maps the polynomials rooted in $[A,B]$ to themselves if and only if
   $L\le A\le-1$ and $0\le B\le U$.

**Corollary (recurrences).** If $P_0=1$ and $P_{n+1}=(x+a_{n+1})P_n+xP_n'$ with all
$a_i\ge-1/4$, then every $P_n$ is rooted in $(-\infty,1/4]$. If $Q_0=1$ and
$Q_{n+1}=(x+a_{n+1})Q_n+x(x+1)Q_n'$ with all $\frac{1-\sqrt2}2\le a_i\le\frac{1+\sqrt2}2$, then
every $Q_n$ is rooted in $[L,U]$.

**Theorem (Brenti–Royle–Wagner, Theorem 4.7).** A polynomial is *PF* if it has nonnegative
coefficients and is zero or has only real nonpositive roots. Let $m\ge0$ be an integer and let
$f$ be monic with real coefficients. If every real zero $r$ satisfies $r\le m$ and every
nonreal zero $s+it$ satisfies $4t^2\le1+4m-4s$, then
$\mathcal T(t^{\underline m}f(t))$ is PF. All inequalities include equality.

For $m=2$, the disk $(s-1)^2+t^2\le1$ satisfies these bounds. Consequently
$\mathcal T((t-1)^n+(-1)^n(t-1))$ is PF for $n\ge2$. For $n\ge3$ the source is the
cycle chromatic polynomial, giving Proposition 4.10.

**Theorem (grouped cubics).** A monic cubic $x^3+\alpha x^2+\beta x+\gamma$ is PF if and
only if $\alpha,\beta,\gamma\ge0$ and its discriminant is nonnegative. For real $a,b,w$,
$$
\mathcal T\bigl((t+a)((t+b)^2+w)\bigr)=x^3+(3+a+2b)x^2+(1+a+2b+2ab+b^2+w)x+a(b^2+w),
$$
and for $w\ge0$,
$$
\mathcal T\bigl((t+b+\tfrac12)((t+b)^2+w)\bigr)\text{ is PF}\iff
b\ge-\tfrac12\text{ and }w\le3b+\tfrac94 .
$$

For instance $\mathcal T\bigl((t+\tfrac12)(t^2+\tfrac12)\bigr)$ is PF, while
$\mathcal T(t^2+\tfrac12)$ is not real-rooted. We also have the inverse
relation with the falling factorial transform, the rule
$\mathcal T(t^{\underline m}p(t))=x^m\,\mathcal T(p(t+m))$, and closure of PF images under
products.

## Use

The Touchard polynomials themselves form a
[Sturm sequence](rr:sturm-sequence-families). The ordered Bell transform has its own
[page](rr:branden-e-transform), and fixed-factor Poisson multiplication is classified on the
[Poisson star product](rr:univariate-poisson-star-c) page.

## Proof

Since $\mathcal T\bigl((t-r)(t-s)\bigr)=x^2+(1-r-s)x+rs$ and
$E\bigl((t-r)(t-s)\bigr)=2x^2+(1-r-s)x+rs$, the image of $(t-r)^2$ is real-rooted exactly when
$r\le1/4$, respectively $4r^2+4r\le1$; this gives necessity. For sufficiency, we pair the roots
of the input so that each pair has an admissible image, and the product rule reduces the claim
to Poisson multiplication by a PF polynomial or diamond multiplication by a polynomial rooted in
$[-1,0]$, which preserve real-rootedness [@Branden2006, Theorems 3.11 and 3.13]. For the
invariant sets, all summands of the product have the sign of the leading coefficient beyond
$c$, respectively outside $[A,B]$.

For the parabolic criterion, factor $f$ into real linear and conjugate-pair quadratic factors
and translate by $m$. Each factor has a PF Touchard image: the quadratic image has
discriminant $1+4m-4s-4t^2\ge0$ and nonnegative coefficients. The product rule then applies.
For cycles, remove $t(t-1)$ and use the disk containing the source roots.

## References

- [@Branden2006, Theorems 3.11 and 3.13]
- F. Brenti, G. F. Royle and D. G. Wagner, *Location of zeros of chromatic and related
  polynomials of graphs*, Canad. J. Math. 46 (1994), 55–80,
  [Theorem 4.7 and Proposition 4.10](https://doi.org/10.4153/CJM-1994-002-3).
- Durán, *Generalized Bell polynomials*, arXiv:2409.11344, Problem 1 and Theorem 5, for the
  recurrences with negative parameters.
<!-- /realrooted-catalog-content -->
-/
