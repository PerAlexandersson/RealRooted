import RealRooted.OperatorInterlacingUpgrade

/-!
# Monomial-chain operator challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "monomial-chain-operator"

[[definitions]]
name = "RealRooted.PreservesPFShiftInterlacingOnDegree"
module = "RealRooted.OperatorInterlacingUpgrade"

[[theorems]]
name = "RealRooted.Challenges.MonomialChainOperator.preservesInterlacing"
-->

<!-- realrooted-catalog-content -->
# Interlacing from a monomial chain

Let `T` be a real-linear operator on polynomials of degree at most `D`.
Suppose that `T` preserves nonnegative coefficients, sends every nonzero PF
polynomial in the degree box to a nonzero real-rooted polynomial, and its
monomial images form the oriented chain

```text
T(1) ≪ T(X) ≪ ⋯ ≪ T(X^D).
```

Then `T` preserves oriented interlacing of nonnegative-coefficient
real-rooted inputs in the same degree box, provided the quadratic tangent
closure used to propagate the monomial chain through a nonpositive linear
factor holds. The theorem below keeps that final analytic closure explicit;
issue #1013 tracks its formal proof.

The checked operator argument first propagates the monomial chain through all
PF factors and then uses the Garloff--Wagner Krein expansion to pass from
one-root deletions to every oriented interlacing pair.

## References

The decomposition step uses the Krein expansion for interlacing polynomials;
the operator perspective is related to P. Brändén, “Iterated sequences and
the geometry of zeros,” *Journal für die reine und angewandte Mathematik* 658
(2011), 115–131.
<!-- /realrooted-catalog-content -->

This module exposes the checked monomial-chain reduction. The quadratic
tangent hypothesis is intentionally visible until the analytic crossing
argument in issue #1013 is formalized.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace MonomialChainOperator

/-- A PF-preserving linear operator whose consecutive monomial images form an
oriented interlacing chain preserves every oriented PF interlacing pair,
assuming the quadratic tangent closure needed for the factor induction. -/
theorem preservesInterlacing
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hfdeg : f.natDegree ≤ D) (hgdeg : g.natDegree ≤ D)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1))))
    (hquadTangent : ∀ ⦃F G H : ℝ[X]⦄,
      HasNonnegCoeffs F → HasNonnegCoeffs G → HasNonnegCoeffs H →
      StrictInterl F G → StrictInterl G H →
      (∀ b : ℝ, 0 ≤ b →
        (H + C (2 * b) * G + C (b ^ 2) * F).Splits) →
      ∀ a : ℝ, 0 ≤ a →
        StrictInterl (quadraticInterlacingTangent F G a)
          (quadraticInterlacingPencil F G H a)) :
    StrictInterl (T f) (T g) :=
  strictInterl_map_of_pfShift hfg hf hg hfdeg hgdeg hTnn hTrr
    (preservesPFShiftInterlacingOnDegree_of_monomials
      hTnn hTrr hmono hquadTangent)

end MonomialChainOperator
end Challenges
end RealRooted
