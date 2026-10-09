import RealRooted.NarayanaTransformation.Interlacing
import RealRooted.OperatorInterlacingUpgrade.RootOrder

/-!
# Monomial-chain operator challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "monomial-chain-operator"

[[theorems]]
name = "RealRooted.Challenges.MonomialChainOperator.preservesInterlacing"
label = "The monomial chain gives interlacing preservation"

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
-->

<!-- realrooted-catalog-content -->
# Interlacing from a monomial chain

Let $T$ be a real-linear operator on polynomials of degree at most $D$.
Suppose that $T$ preserves nonnegative coefficients, sends every nonzero PF
polynomial in the degree box to a nonzero real-rooted polynomial, and its
monomial images form the oriented chain

$$T(1) \ll T(X) \ll \dotsb \ll T(X^D).$$

Then $T$ preserves oriented interlacing of nonnegative-coefficient
real-rooted inputs in the same degree box.  The quadratic tangent theorem
propagates the monomial chain through each nonpositive linear factor.

The proof first propagates the monomial chain through all PF factors, and then
uses the Garloff–Wagner Krein expansion to pass from one-root deletions to every
oriented interlacing pair.

## References

The decomposition step uses the Krein expansion for interlacing polynomials;
the operator perspective is related to P. Brändén, “Iterated sequences and
the geometry of zeros,” *Journal für die reine und angewandte Mathematik* 658
(2011), 115–131.
<!-- /realrooted-catalog-content -->

This module exposes the fully checked monomial-chain upgrade.
-/

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
