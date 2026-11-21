module

public import RealRooted.GammaPencil.AllRank
public import RealRooted.GammaTransform.Basic
public import RealRooted.GammaTransform.Preservation
public import RealRooted.GammaTransform.ProperPosition
public import RealRooted.GammaTransform.RootLists
public import RealRooted.GammaTransform.StrictLifting
public import RealRooted.GammaTransform.TwoStep
public import RealRooted.Transforms.RationalSubstitution
public import RealRooted.Transforms.RationalSubstitutionDerivative

/-!
# Gamma transform

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "gamma-transform"
formalized = "2026-10-06"
references = [
  "Petersen2015EulerianNumbers",
  "HosterStump2025x",
  "Branden2015",
  "Zhang2026SeparableInterlacing",
]
authors = ["Petersen", "Hoster", "Stump", "Zhang"]
years = [2015, 2025, 2026]

[[definitions]]
name = "RealRooted.gammaTransform"
module = "RealRooted.GammaTransform.Basic"
label = "Gamma transform"

[[definitions]]
name = "RealRooted.rationalSubstitution"
module = "RealRooted.Transforms.RationalSubstitution"
label = 'The substitution $B^{\deg p} p(A/B)$, cleared of denominators'

[[theorems]]
name = "RealRooted.GammaTransform.isRealRooted_and_roots_nonpos_iff"
module = "RealRooted.GammaTransform.Preservation"
label = "γ has only real nonpositive roots iff its gamma transform does"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_gammaTransform_succ_iff"
module = "RealRooted.GammaTransform.ProperPosition"
label = "Hoster–Stump: gamma transforms of adjacent degrees interlace iff the γ's do"

[[theorems]]
name = "RealRooted.roots_gammaTransform_eq_reciprocal_add_neg_one_add"
module = "RealRooted.GammaTransform.RootLists"
label = "The roots of a gamma transform are reciprocal pairs together with roots at −1"

[[theorems]]
name = "RealRooted.GammaTransform.strictInterl_succ_of_no_common"
module = "RealRooted.GammaTransform.StrictLifting"
label = "Strict interlacing of gamma polynomials lifts to simple-rooted gamma transforms"

[[theorems]]
name = "RealRooted.strictInterl_gammaTransform_two_step"
module = "RealRooted.GammaTransform.TwoStep"
label = "Two successive gamma-transform steps preserve proper position"

[[theorems]]
name = "RealRooted.gammaUV_allComboRealRooted"
module = "RealRooted.GammaPencil.AllRank"
label = "Every real combination of the gamma-pencil components is real-rooted"

[[theorems]]
name = "RealRooted.rationalSubstitution_splits_iff"
module = "RealRooted.Transforms.RationalSubstitution"
label = "The substitution splits exactly when p splits and every fiber A − rB splits"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.quadraticSubstitution_splits_iff"
module = "RealRooted.Transforms.RationalSubstitution"
label = "The substitution x ↦ x/(1 + sx)² splits iff p splits and 1 − 4sr ≥ 0 at its roots"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.dicksonSubstitution_splits_iff"
module = "RealRooted.Transforms.RationalSubstitutionDerivative"
label = "The substitution x ↦ (x² + a)/x splits iff p splits and 4a ≤ r² at its roots"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Gamma transform

A palindromic polynomial, such as an Eulerian polynomial, is a combination
$\sum_i\gamma_ix^i(1+x)^{d-2i}$. It has only real nonpositive roots exactly when its gamma
polynomial $\sum_i\gamma_ix^i$ does, and interlacing passes in both directions too. Both facts
are cases of a criterion for rational substitutions $p\mapsto B^dp(A/B)$.

## Results

For $\gamma=\sum_i\gamma_ix^i$ with $\deg\gamma\le d/2$, the *gamma transform* is
$$
\Gamma_d(\gamma)=\sum_i\gamma_i\,x^i(1+x)^{d-2i}=(1+x)^d\,\gamma\Bigl(\frac x{(1+x)^2}\Bigr).
$$
Every palindromic polynomial with center $d/2$ is $\Gamma_d(\gamma)$ for a unique *gamma
polynomial* $\gamma$.

**Theorem (real roots).** Let $\deg\gamma\le d/2$. Then $\gamma$ is nonzero and real-rooted
with only nonpositive roots if and only if $\Gamma_d(\gamma)$ is. If all roots of
$\Gamma_d(\gamma)\ne0$ are negative, they are its roots in $(-1,0)$, their reciprocals, and $-1$
with multiplicity $d-2\deg\gamma$.

**Theorem (Hoster–Stump).** [@HosterStump2025x, Prop. 2.5] Let $\deg\gamma\le d/2$ and
$\deg\delta\le(d+1)/2$, where $\gamma,\delta$ have nonnegative coefficients and nonzero
constant terms. Then $\Gamma_d(\gamma)\ll\Gamma_{d+1}(\delta)$ if and only if $\gamma\ll\delta$.

**Corollary (two steps).** If such $\gamma\ll\delta$ have degrees at most $n$ and $n+1$, then
$\Gamma_{2n}(\gamma)\ll(x+1)\,\Gamma_{2n}(\gamma)\ll\Gamma_{2n+2}(\delta)$.

**Theorem (strict lifting).** [@Zhang2026SeparableInterlacing] If $A\ll B$ have positive leading
coefficients, only negative roots, no common root, and degrees $\lfloor(n-1)/2\rfloor$ and
$\lfloor n/2\rfloor$ with $n\ge2$, then $\Gamma_{n-1}(A)\ll\Gamma_n(B)$, and both have simple
negative roots and no common root.

**Proposition (gamma pencil).** For $n\ge2$ let $T_nf=(1+2nx)f+x(1-4x)f'$, $U_2=1$, $V_2=x$,
$U_{n+1}=T_nU_n$ and $V_{n+1}=T_nV_n$. Then every real combination $aU_n+bV_n$ is zero or
real-rooted.

**Theorem (rational substitutions).** Let $p\ne0$ have degree $d$, and let $A,B\ne0$ be coprime
real polynomials that are not proportional over $\mathbb C$. Then $B^dp(A/B)$ is real-rooted if
and only if $p$ is real-rooted and $A-rB$ is real-rooted for every root $r$ of $p$.

**Corollary (quadratic and Dickson substitutions).** For $s\in\mathbb R$, the polynomial
$(1+sx)^{2d}p\bigl(x/(1+sx)^2\bigr)$ is real-rooted if and only if $p$ is real-rooted with
$1-4sr\ge0$ at every root $r$; the case $s=1$ is the gamma transform. For $a\ne0$, the
polynomial $x^dp\bigl((x^2+a)/x\bigr)$ is real-rooted if and only if $p$ is real-rooted with
$4a\le r^2$ at every root $r$.

## Use

For Eulerian-type polynomials, real-rootedness and interlacing of the gamma polynomials, which
have half the degree, are equivalent to the same properties of the palindromic polynomials; see
the [Eulerian polynomials](rr:eulerian) page. The Dickson substitution with $a=1$ handles
palindromic polynomials through $x+1/x$.

## Proof

If $p$ splits, then $B^dp(A/B)=\operatorname{lc}(p)\prod_r(A-rB)$, so it splits exactly when
every fiber does. A nonreal root $z$ of $p$ gives nonreal roots of $A-zB$, because $A/B$ is real
at real points. For the gamma transform, the fiber $x-r(1+x)^2$ has discriminant $1-4r$, which
is positive for $r\le0$. For the pencil, $T_n$ has a stable algebraic symbol, so the finite
Borcea–Brändén theorem [@Branden2015] applies.

## References

[@Petersen2015EulerianNumbers, Sec. 4.6]; [@HosterStump2025x, Prop. 2.5];
[@Zhang2026SeparableInterlacing]; [@Branden2015]. See also
[gamma polynomials](sf:gammaPolynomial) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
