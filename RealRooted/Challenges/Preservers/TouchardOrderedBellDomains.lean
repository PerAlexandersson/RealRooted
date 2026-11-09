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
headline = true

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_Iic_basisTransform_touchard_iff"
module = "RealRooted.Transforms.TouchardRootDomain"
label = "The upper ray (−∞, c] is invariant under the Touchard transform iff 0 ≤ c ≤ 1/4"
headline = true

[[theorems]]
name = "RealRooted.forall_splits_brandenE_iff"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The E transform of every polynomial rooted in J is real-rooted iff J ⊆ [L, U]"
headline = true

[[theorems]]
name = "RealRooted.forall_isRealRootedIn_Icc_brandenE_iff"
module = "RealRooted.Transforms.BrandenE.RootDomain"
label = "The interval [A, B] is invariant under the E transform iff L ≤ A ≤ −1 and 0 ≤ B ≤ U"
headline = true

[[theorems]]
name = "RealRooted.betaProduct_one_isRealRootedIn_Icc"
module = "RealRooted.DerivativeProduct.DiamondIntervals"
label = "The diamond product of a [−1, 0]-rooted and a [A, B]-rooted polynomial is [A, B]-rooted"
headline = true

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

Let $T$ be the *Touchard transform*, the linear map with $T(t^{\underline n})=x^n$, where
$t^{\underline n}=t(t-1)\cdots(t-n+1)$, equivalently $T(t^n)=T_n(x)=\sum_kS(n,k)x^k$. It turns
ordinary multiplication into the Poisson product
$(F\star G)(x)=\sum_{k\ge0}\frac{x^k}{k!}F^{(k)}(x)G^{(k)}(x)$. Let $E$ be Brändén's *ordered
Bell transform*, $E\binom tn=x^n$, which turns multiplication into the diamond product
$(F\diamond G)(x)=\sum_{k\ge0}\frac{[x(x+1)]^k}{(k!)^2}F^{(k)}(x)G^{(k)}(x)$. Both transforms
preserve degree and nonzeroness, and neither is a global real-rootedness preserver. Put
$$
L=-\frac{1+\sqrt2}{2},\qquad U=\frac{\sqrt2-1}{2}.
$$
A nonzero constant counts as real-rooted, and repeated roots and boundary parameters are
included.

**Theorem (sharp source domains).** For every set $J\subseteq\mathbb R$ (including singletons and
the empty set):

1. $T$ sends every nonzero polynomial with all roots in $J$ to a real-rooted polynomial
   **if and only if** $J\subseteq(-\infty,1/4]$.
2. $E$ has this property **if and only if** $J\subseteq[L,U]$.

**Theorem (invariant root intervals).**

3. The invariant upper rays of $T$, those $(-\infty,c]$ such that polynomials rooted there are
   sent to polynomials rooted there, are exactly the rays with $0\le c\le 1/4$.
4. The nonempty invariant closed intervals $[A,B]$ of $E$ are exactly those with
   $L\le A\le-1$ and $0\le B\le U$.

**Recurrences.** If $P_0=1$ and $P_{n+1}=(x+a_{n+1})P_n+xP_n'$ with all $a_i\ge-1/4$, then
every $P_n$ has all its roots in $(-\infty,1/4]$. If $Q_0=1$ and
$Q_{n+1}=(x+a_{n+1})Q_n+x(x+1)Q_n'$ with all
$\tfrac{1-\sqrt2}{2}\le a_i\le\tfrac{1+\sqrt2}{2}$, then every $Q_n$ has all its roots in
$[L,U]$. The rows are the images of $\prod_i(t+a_i)$, whose roots $-a_i$ lie in the invariant
domain.

## Proof

*Pairing.* Under $T$, a linear factor $t-r$ becomes $x-r$, and
$T\bigl((t-r)(t-s)\bigr)=x^2+(1-r-s)x+rs$. For $0\le r,s\le1/4$ this quadratic has nonnegative
coefficients and discriminant $1-2(r+s)+(r-s)^2\ge0$, so it is a PF polynomial, and the images
of the factors $t-r$ with $r\le0$ are PF as well. Since $T$ turns products into the Poisson
product and Poisson multiplication by a PF polynomial preserves PF polynomials, all these
factors can be combined first, and at most one positive factor $t-r$ remains. Fixed Poisson
multiplication by a PF polynomial preserves real-rootedness (Brändén's Theorem 3.11), so the
image of the whole polynomial is real-rooted. Necessity: $T\bigl((t-r)^2\bigr)=x^2+(1-2r)x+r^2$
has discriminant $1-4r$.

For $E$ one has $E\bigl((t-r)(t-s)\bigr)=2x^2+(1-r-s)x+rs$, whose discriminant is
$\tfrac12\bigl[(1-4r-4r^2)+(1-4s-4s^2)\bigr]+3(r-s)^2$. Hence it is nonnegative for all
$r,s\in[L,U]$, and the identity $4r^2+4r\le1\iff r\in[L,U]$ shows that the discriminant
condition and the location condition fit exactly with $L$ and $U$. For two roots in
$(0,U]$, or two roots in $[L,-1)$, the quadratic has both roots in $[-1,0]$, so it is an
admissible kernel for the diamond product, as are the images $x-r$ of the factors with
$r\in[-1,0]$. After combining all admissible factors at most one positive and at most one
negative root remain. Their pair has a real-rooted image, since the constant term $rs$ is
negative, and its roots lie in $(r,-1)\cup(0,s)$. Necessity: $E\bigl((t-r)^2\bigr)$ has
discriminant $1-4r-4r^2$.

*Invariant intervals.* If $G$ is rooted in $[-1,0]$ and $R$ is rooted in $[A,B]$ with
$A\le-1$ and $B\ge0$, then $G\diamond R$ is rooted in $[A,B]$. Real-rootedness is Brändén's
theorem. Outside $[A,B]$ the weight $x(x+1)$ is positive, every derivative of $G$ and $R$ has
the sign dictated by the leading coefficient (to the left of the roots, with alternating
signs), so all summands have the same sign and the $k=0$ summand is nonzero. For the Touchard
transform the paired image is a PF polynomial $G$ times an unpaired factor $x-r$ with
$0<r\le c$, and $(x-r)G+xG'>0$ for $x>r$. Necessity of the conditions on $c$, $A$ and $B$
comes from $T\bigl((t-c)^2\bigr)$ and $E\bigl((t-c)^2\bigr)$, whose roots are explicit.

## What is new

The proofs are new, developed for RealRooted (issue #2365), and are of independent research
interest; we are not aware of a published statement of these sharp domains, and we make no
priority claim. The classical inputs are cited as classical: Brändén's theorem that fixed
Poisson and diamond multiplication by a PF, respectively $[-1,0]$-rooted, kernel preserves
real-rootedness ([@Branden2006], Theorems 3.11 and 3.13), and the Laguerre and
Pólya--Schur theory behind it, as formalized in the
[derivative product kernel](/RealRooted/theorems/derivative-product-kernel/) page. See also the
[Touchard transform](/RealRooted/theorems/touchard-transform/) and
[Brändén E transform](/RealRooted/theorems/branden-e-transform/) pages for the transforms.
Durán, *Generalized Bell polynomials* (arXiv:2409.11344), Problem 1 and Theorem 5, discuss
negative parameters; the uniform bounds here follow by pairing.

## References

See [@Branden2006].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Transforms.TouchardRootDomain`,
`RealRooted.Transforms.BrandenE.RootDomain`, `RealRooted.DerivativeProduct.DiamondIntervals`,
`RealRooted.RootLocation.Pairing` and `RealRooted.RootLocation.DerivativeSigns` modules.
-/
