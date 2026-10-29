module

public import RealRooted.NarayanaTransformation.Interlacing
public import RealRooted.OperatorInterlacingUpgrade.ImplicitRoot
import RealRooted.OperatorInterlacingUpgrade.RootOrder
public import RealRooted.OperatorInterlacingUpgrade.StablePencil
public import RealRooted.PFPolynomial

/-!
# Monomial-chain operator challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "monomial-chain-operator"
formalized = "2026-05-12"
references = [
  "Branden2011b",
]

[[theorems]]
name = "RealRooted.Challenges.MonomialChainOperator.preservesInterlacing"
label = "The monomial chain gives interlacing preservation"
headline = true

[[theorems]]
name = "RealRooted.rootwiseLE_monomialChain_rootPolynomial_list_set"
module = "RealRooted.OperatorInterlacingUpgrade.RootOrder"
label = "Moving one input root right moves every output root right"

[[theorems]]
name = "RealRooted.rootwiseLE_monomialChain_component_bounds"
module = "RealRooted.OperatorInterlacingUpgrade.RootOrder"
label = "Output roots are bounded by the images of (x + a)^D and (x + b)^D"

[[theorems]]
name = "RealRooted.strictInterl_narayanaTransform"
module = "RealRooted.NarayanaTransformation.Interlacing"
label = "The Mao–Wang Narayana transform preserves interlacing"
headline = true

[[theorems]]
name = "RealRooted.exists_hasDerivAt_finRootPolynomial_shift"
module = "RealRooted.OperatorInterlacingUpgrade.ImplicitRoot"
label = "Implicit derivative of a simple output root in one input root"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_bivariatePencil_map_of_monomialChain"
module = "RealRooted.OperatorInterlacingUpgrade.StablePencil"
label = "Monomial-chain operators preserve nonnegative stable pencils"
-->

<!-- realrooted-catalog-content -->
# Interlacing from a monomial chain

Let $T$ be a real-linear operator on $\mathbb R[x]$ and let $D\in\mathbb N$.
Suppose that $T$ maps polynomials with nonnegative coefficients to polynomials
with nonnegative coefficients, sends every nonzero PF polynomial of degree at
most $D$ to a nonzero real-rooted polynomial, and its monomial images form the
oriented chain

$$
T(1) \ll T(X) \ll \dotsb \ll T(X^D).
$$

Then $f\ll g$ with nonnegative coefficients and $\deg g\leq D$ implies
$Tf\ll Tg$. The quadratic interlacing closure lemma propagates the monomial
chain through each nonpositive linear factor.

The proof first propagates the monomial chain through all PF factors, and then
uses the Garloff–Wagner Krein expansion to pass from one-root deletions to every
oriented interlacing pair.

## Consequences

Under the corresponding degree and nonvanishing hypotheses, moving one
nonpositive input root to the right moves every output root weakly to the
right. If $\rho$ is a simple root of $Tp$ and $r_i$ is the input root being
moved, the derivative of the resulting root branch is
$$
\frac{T(p/(x-r_i))(\rho)}{(Tp)'(\rho)}.
$$
The operator also preserves stability of nonnegative bivariate pencils
$f(z)+wg(z)$ under the hypotheses of the listed stable-pencil theorem. The
Mao–Wang Narayana transform is an instance; see the
[Narayana page](/RealRooted/families/narayana/).

## References

The decomposition step uses the Krein expansion for interlacing polynomials;
the operator perspective is related to [@Branden2011b].
<!-- /realrooted-catalog-content -->

This module exposes the fully checked monomial-chain upgrade.
-/

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace MonomialChainOperator

/-- A PF-preserving linear operator whose consecutive monomial images form an
oriented interlacing chain preserves every oriented PF interlacing pair. -/
theorem preservesInterlacing
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hgdeg : g.natDegree ≤ D)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1)))) :
    StrictInterl (T f) (T g) :=
  strictInterl_map_of_monomialChain hfg hf hg hgdeg hTnn hTrr hmono

end MonomialChainOperator
end Challenges
end RealRooted
