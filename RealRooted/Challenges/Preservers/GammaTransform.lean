module

import RealRooted.GammaPencil.Theorem
import RealRooted.GammaTransform.Preservation
import RealRooted.GammaTransform.ProperPosition
import RealRooted.GammaTransform.StrictLifting
import RealRooted.GammaTransform.TwoStep
import RealRooted.GammaPencil.Preserver
public import RealRooted.GammaPencil.Basic
public import RealRooted.GammaTransform.Basic

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
name = "RealRooted.Challenges.GammaTransform.isRealRooted_and_roots_nonpos_gammaTransform_iff"
label = "Real roots transfer through the gamma transform"
headline = true

[[theorems]]
name = "RealRooted.Challenges.GammaTransform.gammaU_strictInterl_gammaV"
label = "The gamma-pencil components interlace"

[[theorems]]
name = "RealRooted.Challenges.GammaTransform.isRealRooted_gammaTransform_of_hasNonnegCoeffs"
label = "Gamma transforms of real-rooted nonnegative polynomials"

[[theorems]]
name = "RealRooted.Challenges.GammaTransform.strictInterl_gammaTransform_succ_iff"
label = "Gamma transforms of adjacent degree preserve interlacing"

[[theorems]]
name = "RealRooted.Challenges.GammaTransform.splits_C_mul_gammaU_add_C_mul_gammaV"
label = "Every real combination of the gamma-pencil components is real-rooted"

[[theorems]]
name = "RealRooted.Challenges.GammaTransform.gammaOperator_eq_zero_or_splits"
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
name = """RealRooted.strictInterl_gammaTransform_succ_of_\
strictInterl_of_no_common"""
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

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace GammaTransform

/-- **Gamma real-rootedness criterion**: for `γ` of degree at most `d / 2`,
`γ` is real-rooted with nonpositive roots if and only if its gamma transform
is. -/
theorem isRealRooted_and_roots_nonpos_gammaTransform_iff {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) :
    ((γ ≠ 0 ∧ γ.Splits) ∧ ∀ r ∈ γ.roots, r ≤ 0) ↔
      ((gammaTransform d γ ≠ 0 ∧ (gammaTransform d γ).Splits) ∧
        ∀ r ∈ (gammaTransform d γ).roots, r ≤ 0) :=
  ⟨fun h ↦ isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
      hγdeg h.1.1 h.1.2 h.2,
    fun h ↦ isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
      hγdeg h.1.1 h.1.2 h.2⟩

/-- The gamma transform of a nonzero real-rooted polynomial with nonnegative
coefficients is real-rooted. -/
theorem isRealRooted_gammaTransform_of_hasNonnegCoeffs {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) (hγ_ne : γ ≠ 0) (hγ_splits : γ.Splits)
    (hγ_nonneg : HasNonnegCoeffs γ) :
    gammaTransform d γ ≠ 0 ∧ (gammaTransform d γ).Splits :=
  isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs hγdeg hγ_ne hγ_splits
    hγ_nonneg

/-- **Hoster–Stump**, Proposition 2.5: gamma transforms of adjacent ambient
degrees interlace exactly when the gamma polynomials do. -/
theorem strictInterl_gammaTransform_succ_iff {d : ℕ} {γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) (hδdeg : δ.natDegree ≤ (d + 1) / 2)
    (hγ_nonneg : HasNonnegCoeffs γ) (hδ_nonneg : HasNonnegCoeffs δ)
    (hγ0 : γ.coeff 0 ≠ 0) (hδ0 : δ.coeff 0 ≠ 0) :
    StrictInterl (gammaTransform d γ) (gammaTransform (d + 1) δ) ↔ StrictInterl γ δ :=
  RealRooted.strictInterl_gammaTransform_succ_iff hγdeg hδdeg hγ_nonneg hδ_nonneg hγ0 hδ0

/-- The rank-`n` gamma-pencil operator maps every real-rooted polynomial of
degree at most `n / 2` to zero or a real-rooted polynomial. -/
theorem gammaOperator_eq_zero_or_splits {n : ℕ} (hn : 2 ≤ n) {p : ℝ[X]}
    (hdeg : p.natDegree ≤ n / 2) (hp : p.Splits) :
    gammaOperator n p = 0 ∨ (gammaOperator n p).Splits :=
  gammaOperator_splits_or_zero hn hdeg hp

/-- Every real linear combination of the rank-`n` gamma-pencil components
splits. -/
theorem splits_C_mul_gammaU_add_C_mul_gammaV {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    (C a * gammaU n + C b * gammaV n).Splits :=
  gammaUV_allComboRealRooted n hn a b

/-- **Gamma pencil**: the two components of the rank-`n` gamma pencil
interlace. -/
theorem gammaU_strictInterl_gammaV {n : ℕ} (hn : 2 ≤ n) :
    StrictInterl (gammaU n) (gammaV n) :=
  RealRooted.gammaU_strictInterl_gammaV n hn

end GammaTransform
end Challenges
end RealRooted
