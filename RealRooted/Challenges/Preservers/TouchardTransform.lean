module

import RealRooted.Transforms.BrandenE.RootDomain
import RealRooted.Transforms.StirlingRootRegions
import RealRooted.Transforms.StirlingRootRegions.Parabolic
import RealRooted.Transforms.TouchardRootDomain

/-!
# Touchard and ordered Bell transforms

<!-- realrooted-catalog
version = 1
kind = "original"
section = "theorems"
slug = "touchard-transform"
formalized = "2026-11-09"
references = [
  "Branden2006",
]
authors = ["Brändén", "Brenti", "Royle", "Wagner"]
years = [1994, 2006]

[[theorems]]
name = "RealRooted.forall_splits_basisTransform_touchard_iff"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The Touchard transform of every polynomial rooted in J is real-rooted iff J ⊆ (−∞, 1/4]"
headline = true
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_Iic_basisTransform_touchard_iff"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The upper ray (−∞, c] is invariant under the Touchard transform iff 0 ≤ c ≤ 1/4"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.forall_splits_brandenE_iff"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The E transform of every polynomial rooted in J is real-rooted iff J ⊆ [L, U]"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_Icc_brandenE_iff"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The interval [A, B] is invariant under the E transform iff L ≤ A ≤ −1 and 0 ≤ B ≤ U"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.isRealRootedIn_Iic_quarter_of_touchard_recurrence"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "Rows of the recurrence P_{n+1} = (x + a) P_n + x P_n′ with a ≥ −1/4 have roots ≤ 1/4"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.isRealRootedIn_Icc_of_brandenE_recurrence"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "Rows of the E-transform recurrence with (1 − √2)/2 ≤ aᵢ ≤ (1 + √2)/2 are rooted in [L, U]"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.basisTransform_touchard_mul"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform turns products into the parameter-one Poisson product"

[[theorems]]
name = "RealRooted.StirlingRootRegion.isPFPolynomial_fallingFactorial_mul"
module = "RealRooted.Transforms.StirlingRootRegions.Parabolic"
label = "Brenti–Royle–Wagner: roots in a parabolic region give a PF Touchard transform"

[[theorems]]
objects = ["Cycle graph partition polynomials"]
property = "pf"
name = "RealRooted.StirlingRootRegion.isPFPolynomial_cycle"
module = "RealRooted.Transforms.StirlingRootRegions.Parabolic"
label = "Brenti–Royle–Wagner: the Stirling transform of the cycle chromatic polynomial is PF"

[[theorems]]
name = "RealRooted.isPFPolynomial_touchard_linear_mul_quadratic_iff"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "Exact coefficient and discriminant criterion for the grouped cubic (X + a)((X + b)² + w)"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.isPFPolynomial_touchard_half_shifted_cubic_iff"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform of (t + b + 1/2)((t + b)² + w) is PF iff b ≥ −1/2 and w ≤ 3b + 9/4"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.not_splits_basisTransform_touchard_y_sq_add_half"
module = "RealRooted.Transforms.StirlingRootRegions"
label = "The Touchard transform of X² + 1/2 is not real-rooted"

-->

<!-- realrooted-catalog-content -->
# Touchard and ordered Bell transforms

The Touchard transform $t^n\mapsto\sum_kS(n,k)x^k$ sends every polynomial with all roots in a
set $J$ to a real-rooted polynomial exactly when $J\subseteq(-\infty,1/4]$. Brändén's ordered
Bell transform does so exactly when $J\subseteq[L,U]$, with $L=-\frac{1+\sqrt2}2$ and
$U=\frac{\sqrt2-1}2$.

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

**Theorem (Brenti–Royle–Wagner).** A polynomial is *PF* if it has nonnegative
coefficients and is zero or has only real nonpositive roots. Let $m\ge0$ be an integer and let
$f$ be monic with real coefficients. If every real zero $r$ satisfies $r\le m$ and every
nonreal zero $s+it$ satisfies $4t^2\le1+4m-4s$, then
$\mathcal T(t^{\underline m}f(t))$ is PF. All inequalities include equality.

For $m=2$, the disk $(s-1)^2+t^2\le1$ satisfies these bounds, so the Touchard transform of the
chromatic polynomial $(t-1)^n+(-1)^n(t-1)$ of the $n$-cycle, $n\ge3$, is PF.

**Theorem (grouped cubics).** For real $a,b,w$ the transform
$\mathcal T\bigl((t+a)((t+b)^2+w)\bigr)$ is PF exactly when its coefficients and its
discriminant are nonnegative. In particular, for $w\ge0$,
$$
\mathcal T\bigl((t+b+\tfrac12)((t+b)^2+w)\bigr)\text{ is PF}\iff
b\ge-\tfrac12\text{ and }w\le3b+\tfrac94 .
$$

For instance $\mathcal T\bigl((t+\tfrac12)(t^2+\tfrac12)\bigr)$ is PF, while
$\mathcal T(t^2+\tfrac12)$ is not real-rooted.

## Use

The root domains say exactly which real-rooted polynomials the two transforms can be applied to.
With all $a_i=0$ the first recurrence gives the Touchard polynomials; Durán studies such recurrences
with negative parameters (Problem 1 and Thm. 5). Brenti, Royle and Wagner proposed cubic factors as
the next step after their quadratic criterion; the grouped cubics give such a criterion. The ordered
Bell transform has its own [page](rr:branden-e-transform), and Poisson multiplication by a fixed
factor is classified on the [derivative products](rr:derivative-products) page.

## Proof

Since $\mathcal T\bigl((t-r)(t-s)\bigr)=x^2+(1-r-s)x+rs$ and
$E\bigl((t-r)(t-s)\bigr)=2x^2+(1-r-s)x+rs$, the image of $(t-r)^2$ is real-rooted exactly when
$r\le1/4$, respectively $4r^2+4r\le1$; this gives necessity. For sufficiency, we pair the roots
of the input so that each pair has an admissible image, and the product rule reduces the claim
to Poisson multiplication by a PF polynomial or diamond multiplication by a polynomial rooted in
$[-1,0]$, which preserve real-rootedness [@Branden2006, Thms. 3.11 and 3.13]. For the
invariant sets, all summands of the product have the sign of the leading coefficient beyond
$c$, respectively outside $[A,B]$. The parabolic criterion is the same argument for real
linear and conjugate-pair quadratic factors.

## References

[@Branden2006, Thms. 3.11 and 3.13]; F. Brenti, G. F. Royle and D. G. Wagner, “Location of
zeros of chromatic and related polynomials of graphs,” *Canad. J. Math.* 46 (1994), 55–80,
[Thm. 4.7, Prop. 4.10 and §6](https://doi.org/10.4153/CJM-1994-002-3); A. J. Durán,
“Generalized Bell polynomials,” arXiv:2409.11344 (2024), Problem 1 and Thm. 5.
<!-- /realrooted-catalog-content -->
-/
