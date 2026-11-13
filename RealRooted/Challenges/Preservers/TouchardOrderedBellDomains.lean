module

import RealRooted.DerivativeProduct.DiamondIntervals
import RealRooted.RootLocation.DerivativeSigns
import RealRooted.RootLocation.Pairing
import RealRooted.Transforms.BrandenE.RootDomain
import RealRooted.Transforms.TouchardRootDomain

/-!
# Sharp root domains for the Touchard and ordered Bell transforms

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "touchard-ordered-bell-root-domains"
formalized = "2026-11-09"
tags = ["realrooted-original"]
references = [
  "Branden2006",
]
authors = ["Brändén"]
years = [2006]

[[theorems]]
name = "RealRooted.forall_splits_basisTransform_touchard_iff"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The Touchard transform of every polynomial rooted in J is real-rooted iff J ⊆ (−∞, 1/4]"

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_Iic_basisTransform_touchard_iff"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The upper ray (−∞, c] is invariant under the Touchard transform iff 0 ≤ c ≤ 1/4"

[[theorems]]
name = "RealRooted.forall_splits_brandenE_iff"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The E transform of every polynomial rooted in J is real-rooted iff J ⊆ [L, U]"
headline = true

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_Icc_brandenE_iff"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The interval [A, B] is invariant under the E transform iff L ≤ A ≤ −1 and 0 ≤ B ≤ U"

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
name = "RealRooted.isRealRootedIn_Iic_quarter_of_touchard_recurrence"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "Rows of the recurrence P_{n+1} = (x + a) P_n + x P_n′ with a ≥ −1/4 have roots ≤ 1/4"

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
name = "RealRooted.isRealRootedIn_Icc_of_brandenE_recurrence"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "Rows of the Euler type recurrence with (1 − √2)/2 ≤ a ≤ (1 + √2)/2 are rooted in [L, U]"

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
# Sharp root domains for the Touchard and ordered Bell transforms

The Touchard transform sends every polynomial with roots in $J$ to a real-rooted polynomial
exactly when $J\subseteq(-\infty,1/4]$, and Brändén's ordered Bell transform does so exactly
when $J\subseteq[L,U]$ with $L=-\frac{1+\sqrt2}2$ and $U=\frac{\sqrt2-1}2$.

## Results

Let $T$ be the *Touchard transform*, the linear map with $T(t^{\underline n})=x^n$, where
$t^{\underline n}=t(t-1)\cdots(t-n+1)$; equivalently $T(t^n)=\sum_kS(n,k)x^k$. It turns
ordinary multiplication into the Poisson product
$(F\star G)(x)=\sum_{k\ge0}\frac{x^k}{k!}F^{(k)}(x)G^{(k)}(x)$. Let $E$ be Brändén's *ordered
Bell transform*, $E\binom tn=x^n$, which turns multiplication into the diamond product
$(F\diamond G)(x)=\sum_{k\ge0}\frac{[x(x+1)]^k}{(k!)^2}F^{(k)}(x)G^{(k)}(x)$. A polynomial is
*rooted in* a set $S$ if it is nonzero, real-rooted and has all roots in $S$; nonzero constants
are included, and repeated roots and boundary values are allowed. Put
$$
L=-\frac{1+\sqrt2}{2},\qquad U=\frac{\sqrt2-1}{2}.
$$

**Theorem (sharp source domains).** For every set $J\subseteq\mathbb R$, including singletons
and the empty set:

1. $T$ sends every polynomial rooted in $J$ to a real-rooted polynomial if and only if
   $J\subseteq(-\infty,1/4]$.
2. $E$ sends every polynomial rooted in $J$ to a real-rooted polynomial if and only if
   $J\subseteq[L,U]$.

In particular, neither transform preserves real-rootedness globally.

**Theorem (invariant root sets).**

3. For $c\in\mathbb R$, the transform $T$ sends every polynomial rooted in $(-\infty,c]$ to a
   polynomial rooted in $(-\infty,c]$ if and only if $0\le c\le1/4$.
4. For $A\le B$, the transform $E$ sends every polynomial rooted in $[A,B]$ to a polynomial
   rooted in $[A,B]$ if and only if $L\le A\le-1$ and $0\le B\le U$.

**Theorem (recurrences).** Let $P_0=1$ and $P_{n+1}=(x+a_{n+1})P_n+xP_n'$ with all
$a_i\ge-1/4$. Then every $P_n$ is rooted in $(-\infty,1/4]$. Let $Q_0=1$ and
$Q_{n+1}=(x+a_{n+1})Q_n+x(x+1)Q_n'$ with all
$\tfrac{1-\sqrt2}{2}\le a_i\le\tfrac{1+\sqrt2}{2}$. Then every $Q_n$ is rooted in $[L,U]$.

**Lemma (images of quadratics).** For real $r,s$,
$T\bigl((t-r)(t-s)\bigr)=x^2+(1-r-s)x+rs$ and $E\bigl((t-r)(t-s)\bigr)=2x^2+(1-r-s)x+rs$.
Both transforms send $t-r$ to $x-r$. If $0\le r,s\le1/4$, then
$T\bigl((t-r)(t-s)\bigr)$ is a PF polynomial. The polynomial $T\bigl((t-r)^2\bigr)$ is
real-rooted if and only if $r\le1/4$, and $E\bigl((t-r)^2\bigr)$ is real-rooted if and only if
$r\in[L,U]$, that is, $4r^2+4r\le1$.

**Lemma (pairing).** Let $K$ be a set of polynomials containing $1$ and closed under
multiplication, and let $S\subseteq\mathbb R$ with $(x-r)(x-s)\in K$ for all $r,s\in S$. Then
every product of linear factors $x-r$ with $r\in S$ is $F\cdot R$ with $F\in K$ and $R$ equal to
$1$ or to a single factor $x-r$. For $T$, all but at most one positive root can be paired; for
$E$, all but at most one positive and one negative root.

## Proof

For $T$, Poisson multiplication by a PF polynomial preserves real-rootedness
([@Branden2006], Thm 3.11). By the pairing lemma with $K$ the polynomials with PF image, a
polynomial rooted in $(-\infty,1/4]$ is a constant times $F\cdot R$ where $T(F)$ is PF and $R$
is $1$ or one factor $x-r$ with $0<r\le1/4$. Hence $T$ of it is real-rooted. If the roots are
at most $c\le1/4$, the unpaired factor gives, with $G=T(F)$, $(x-r)G+xG'>0$ for $x>r$, so the
image stays rooted in $(-\infty,c]$.

For $E$, the images of $x-r$ with $r\in[-1,0]$ are admissible kernels for the diamond
product ([@Branden2006], Thm 3.13). So is $E\bigl((t-r)(t-s)\bigr)$ for two roots in
$(0,U]$ or two roots in $[L,-1)$, because it is then rooted in $[-1,0]$. The discriminant of
the quadratic is $\tfrac12\bigl[(1-4r-4r^2)+(1-4s-4s^2)\bigr]+3(r-s)^2$. After pairing, at
most one positive root $s$ and one negative root $r<-1$ remain; the image of $(x-r)(x-s)$ has
its roots in $[r,s]$. If $G$ is rooted in $[-1,0]$ and $R$ in $[A,B]$ with $A\le-1$ and
$B\ge0$, then $G\diamond R$ is rooted in $[A,B]$: outside $[A,B]$ the weight $x(x+1)$ is
positive and the derivatives of $G$ and $R$ have the sign of the leading coefficient, so
all summands of the diamond product have the same sign and the $k=0$ summand is nonzero.

## References

The classical inputs are Brändén's theorems that fixed Poisson, respectively diamond,
multiplication by a PF, respectively $[-1,0]$-rooted, kernel preserves real-rootedness
([@Branden2006], Theorems 3.11 and 3.13), as used on the
[derivative product kernel](rr:derivative-product-kernel) page. See the
[Touchard transform](rr:touchard-transform) and
[Brändén E transform](rr:branden-e-transform) pages for the transforms.
Durán, *Generalized Bell polynomials* (arXiv:2409.11344), Problem 1 and Theorem 5, discuss
negative parameters; the uniform bounds here follow by pairing.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Transforms.TouchardRootDomain`,
`RealRooted.Transforms.BrandenE.RootDomain`, `RealRooted.DerivativeProduct.DiamondIntervals`,
`RealRooted.RootLocation.Pairing` and `RealRooted.RootLocation.DerivativeSigns` modules.
-/
