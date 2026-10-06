import RealRooted.GammaPencil.Theorem
import RealRooted.GammaTransform.Preservation
import RealRooted.GammaTransform.ProperPosition

/-!
# Gamma transform challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "gamma-transform"
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
headline = true

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
-->

<!-- realrooted-catalog-content -->
# The gamma transform

For $d \geq 0$ and a polynomial $\gamma(x) = \sum_i \gamma_i x^i$, the
**gamma transform** in ambient degree $d$ is
$$
\Gamma_d(\gamma)(x) = \sum_{i=0}^{\lfloor d/2 \rfloor}
  \gamma_i\, x^i (1+x)^{d-2i}.
$$
Every palindromic polynomial $p$ with center of symmetry $d/2$ has the form
$p = \Gamma_d(\gamma_p)$ for a unique **gamma polynomial** $\gamma_p$ of degree
at most $d/2$, and $p$ is gamma-positive when $\gamma_p$ has nonnegative
coefficients.

**Theorem.** Let $\deg \gamma \leq d/2$. Then $\gamma$ is nonzero and
real-rooted with only nonpositive zeros if and only if $\Gamma_d(\gamma)$ is
nonzero and real-rooted with only nonpositive zeros. In particular, if
$\gamma \neq 0$ is real-rooted with nonnegative coefficients, then
$\Gamma_d(\gamma)$ is real-rooted.

**Theorem** (Hoster–Stump). Let $\deg \gamma \leq d/2$ and
$\deg \delta \leq (d+1)/2$, and let $\gamma$ and $\delta$ have nonnegative
coefficients and nonzero constant terms. Then
$\Gamma_d(\gamma) \ll \Gamma_{d+1}(\delta)$ if and only if
$\gamma \ll \delta$.

## The gamma pencil

For $n \geq 2$, let $T_n$ be the operator
$$
T_n f = (1 + 2nx)\, f + x (1 - 4x)\, f'.
$$
Define $U_2 = 1$, $V_2 = x$, and $U_{n+1} = T_n U_n$,
$V_{n+1} = T_n V_n$; these are `gammaU` and `gammaV`, defined by this
recurrence.

**Theorem.** For $n \geq 2$, the operator $T_n$ maps every real-rooted
polynomial of degree at most $n/2$ to zero or a real-rooted polynomial. For
every $n \geq 2$ and all real $a$ and $b$, the polynomial $a U_n + b V_n$ is
real-rooted (we count the zero polynomial as real-rooted here), and
$U_n \ll V_n$.

## Proof idea

The map $x \mapsto x/(1+x)^2$ sends $(-\infty, 0]$ onto $(-\infty, 1/4]$,
except that $-1$ goes to infinity, and
$\Gamma_d(\gamma)(x) = (1+x)^d \gamma(x/(1+x)^2)$. Each nonpositive zero $y$
of $\gamma$ therefore pulls back to two nonpositive zeros of
$\Gamma_d(\gamma)$, which are real since $y \leq 0 < 1/4$, and the factor
$(1+x)^{d - 2\deg\gamma}$ supplies the remaining zeros. We prove both
directions by induction on $\deg \gamma$, splitting off one quadratic factor
at a time. The Hoster–Stump equivalence follows by comparing the sorted root
lists through the same monotone root map.

For the pencil, the operator $T_n$ has a stable algebraic symbol, so the
finite Borcea–Brändén theorem shows that it preserves real-rootedness on its
degree box. It therefore maps the real pencil spanned by $U_n$ and $V_n$ into
the next one, starting from the linear pencil $a + bx$. By Obreschkoff's
theorem, the pencil property makes $U_n$ and $V_n$ interlace, and the
constant terms $U_n(0) = 1$ and $V_n(0) = 0$ fix the orientation.

## References

T. K. Petersen, *Eulerian Numbers*, Birkhäuser, 2015, Section 4.6;
Hoster and Stump, [arXiv:2508.15538](https://arxiv.org/abs/2508.15538) (2025),
Proposition 2.5; P. Brändén, “Unimodality, log-concavity,
real-rootedness and beyond,” *Handbook of Enumerative Combinatorics*, CRC
Press, 2015. See the
[gamma polynomial on symmetricfunctions.com](https://www.symmetricfunctions.com/gammaPositivity.htm#gammaPolynomial).
<!-- /realrooted-catalog-content -->

This module exposes the real-rootedness transfer for the gamma transform, the
Hoster–Stump interlacing equivalence, and the all-rank gamma-pencil theorem.
The gamma transform lives in `RealRooted.GammaTransform`; the pencil lives in
`RealRooted.GammaPencil`.
-/

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
