module

public import RealRooted.GammaPencil.Basic
public import RealRooted.GammaPencil.Preserver
public import RealRooted.GammaPencil.Theorem
public import RealRooted.GammaTransform.Basic
public import RealRooted.GammaTransform.Preservation
public import RealRooted.GammaTransform.ProperPosition
public import RealRooted.GammaTransform.RootLists
public import RealRooted.GammaTransform.StrictLifting
public import RealRooted.GammaTransform.TwoStep

/-!
# Real-rootedness and interlacing of the gamma transform

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "gamma-transform"
formalized = "2026-10-06"
tags = []
references = [
  "Petersen2015EulerianNumbers",
  "HosterStump2025x",
  "Branden2015",
  "Zhang2026SeparableInterlacing",
]
authors = ["Petersen", "Hoster", "Stump"]
years = [2015, 2025]

[[definitions]]
name = "RealRooted.gammaTransform"
module = "RealRooted.GammaTransform.Basic"
label = "Gamma transform"

[[definitions]]
name = "RealRooted.gammaOperator"
module = "RealRooted.GammaPencil.Basic"
label = "Gamma-pencil operator"

[[definitions]]
name = "RealRooted.gammaU"
module = "RealRooted.GammaPencil.Basic"
label = "Constant component of the gamma pencil"

[[definitions]]
name = "RealRooted.gammaV"
module = "RealRooted.GammaPencil.Basic"
label = "Parameter component of the gamma pencil"

[[theorems]]
name = "RealRooted.GammaTransform.isRealRooted_and_roots_nonpos_iff"
module = "RealRooted.GammaTransform.Preservation"
label = "Real roots transfer through the gamma transform"
headline = true

[[theorems]]
name = "RealRooted.gammaU_strictInterl_gammaV"
module = "RealRooted.GammaPencil.Theorem"
label = "The gamma-pencil components interlace"

[[theorems]]
name = "RealRooted.GammaTransform.isRealRooted_gammaTransform_of_hasNonnegCoeffs"
module = "RealRooted.GammaTransform.Preservation"
label = "Gamma transforms of real-rooted nonnegative polynomials"

[[theorems]]
name = "RealRooted.strictInterl_gammaTransform_succ_iff"
module = "RealRooted.GammaTransform.ProperPosition"
label = "Gamma transforms of adjacent degree preserve interlacing"

[[theorems]]
name = "RealRooted.gammaUV_allComboRealRooted"
module = "RealRooted.GammaPencil.Theorem"
label = "Every real combination of the gamma-pencil components is real-rooted"

[[theorems]]
name = "RealRooted.gammaOperator_splits_or_zero"
module = "RealRooted.GammaPencil.Preserver"
label = "The gamma-pencil operator preserves real-rootedness"

[[definitions]]
name = "RealRooted.IsGammaExpansion"
module = "RealRooted.GammaTransform.Basic"
label = "The polynomial γ is the gamma polynomial of p in ambient degree d"

[[theorems]]
name = "RealRooted.IsGammaExpansion.isRealRooted_and_hasRootsNonpos_iff"
module = "RealRooted.GammaTransform.Preservation"
label = "A gamma expansion is real-rooted with nonpositive roots iff its gamma polynomial is"

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
-->

<!-- realrooted-catalog-content -->
# Real-rootedness and interlacing of the gamma transform

The gamma transform $\Gamma_d$ sends a real-rooted polynomial with nonpositive roots to a
real-rooted polynomial with nonpositive roots, and conversely; adjacent transforms interlace
exactly when the gamma polynomials do.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
For $d\ge0$ and $\gamma=\sum_i\gamma_ix^i$, the *gamma transform* in ambient degree $d$ is
$$
\Gamma_d(\gamma)(x)=\sum_{i=0}^{\lfloor d/2\rfloor}\gamma_i\,x^i(1+x)^{d-2i}.
$$
A palindromic polynomial $p$ with center of symmetry $d/2$ is $\Gamma_d(\gamma_p)$ for a unique
*gamma polynomial* $\gamma_p$ of degree at most $d/2$; $p$ is *gamma-positive* if
$\gamma_p$ has nonnegative coefficients.

**Theorem (real roots).** Let $\deg\gamma\le d/2$. Then $\gamma$ is nonzero and real-rooted with
only nonpositive roots if and only if $\Gamma_d(\gamma)$ is. If $\gamma\ne0$ is real-rooted with
nonnegative coefficients, then $\Gamma_d(\gamma)$ is nonzero and real-rooted.

**Theorem (Hoster--Stump [@HosterStump2025x, Prop. 2.5]).** Let $\deg\gamma\le d/2$ and
$\deg\delta\le(d+1)/2$, where $\gamma,\delta$ have nonnegative coefficients and nonzero constant
terms. Then $\Gamma_d(\gamma)\ll\Gamma_{d+1}(\delta)$ if and only if $\gamma\ll\delta$.

**Theorem (roots).** Let $\deg\gamma\le d/2$ with $\gamma\ne0$, and suppose all roots of
$\Gamma_d(\gamma)$ are negative. Then the roots of $\Gamma_d(\gamma)$, with multiplicity, are
the roots $x\in(-1,0)$, their reciprocals $1/x$, and $-1$ with multiplicity $d-2\deg\gamma$.

**Theorem (strict lifting).** Let $n\ge2$, and let $A,B$ have positive leading coefficients,
only negative roots, and degrees $\lfloor(n-1)/2\rfloor$ and $\lfloor n/2\rfloor$. If $A\ll B$
and $A,B$ have no common root, then $\Gamma_{n-1}(A)$ and $\Gamma_n(B)$ have degrees $n-1$ and
$n$, simple negative roots and no common root, and $\Gamma_{n-1}(A)\ll\Gamma_n(B)$. The argument
follows [@Zhang2026SeparableInterlacing].

**Theorem (two steps).** Let $\gamma\ll\delta$ have nonnegative coefficients and nonzero
constant terms, with $\deg\gamma\le n$ and $\deg\delta\le n+1$. Then
$$
\Gamma_{2n}(\gamma)\ \ll\ (x+1)\,\Gamma_{2n}(\gamma)\ \ll\ \Gamma_{2n+2}(\delta).
$$

**The gamma pencil.** For $n\ge2$ let
$$
T_nf=(1+2nx)\,f+x(1-4x)\,f'.
$$
Put $U_2=1$, $V_2=x$, $U_{n+1}=T_nU_n$ and $V_{n+1}=T_nV_n$.

**Theorem (pencil).** For $n\ge2$, $T_n$ maps every real-rooted polynomial of degree at most
$n/2$ to zero or a real-rooted polynomial. For all real $a,b$, $aU_n+bV_n$ is zero or
real-rooted, and $U_n\ll V_n$.

## Proof

Since $\Gamma_d(\gamma)(x)=(1+x)^d\gamma\bigl(x/(1+x)^2\bigr)$ and $x/(1+x)^2$ maps
$(-\infty,0]\setminus\{-1\}$ onto $(-\infty,0]$, each nonpositive root $y$ of $\gamma$ pulls
back to two real roots, which are nonpositive because $y\le0<1/4$. For the pencil, $T_n$ has a
stable algebraic symbol, so the finite Borcea--Brändén theorem [@Branden2015] applies.

## References

[@Petersen2015EulerianNumbers, Sec. 4.6], [@HosterStump2025x, Prop. 2.5], [@Branden2015]. The
[gamma polynomial on symmetricfunctions.com](sf:gammaPolynomial) gives the discussion of
gamma-positivity.
<!-- /realrooted-catalog-content -->

This module exposes the real-rootedness transfer for the gamma transform, the
Hoster–Stump interlacing equivalence, and the all-rank gamma-pencil theorem.
The gamma transform lives in `RealRooted.GammaTransform`; the pencil lives in
`RealRooted.GammaPencil`.  The two pencil statements restate
`RealRooted.gammaUV_allComboRealRooted` and `RealRooted.gammaU_strictInterl_gammaV`
from `RealRooted.GammaPencil.Theorem`.
-/
