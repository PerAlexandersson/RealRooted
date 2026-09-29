import RealRooted.BalancedRunTransformation.Preservation
import RealRooted.OperatorInterlacingUpgrade

/-!
# Interlacing preservation for the balanced run transformation

This file specializes the monomial-chain operator upgrade to the balanced run
kernel.  The only remaining hypothesis is the general quadratic-tangent
closure isolated by `OperatorInterlacingUpgrade`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The balanced run transform preserves oriented interlacing on its
increasing-degree range, assuming the general quadratic-tangent closure. -/
theorem strictInterl_balancedRunTransform
    {n : ℕ} (hn : 2 ≤ n) {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hfdeg : f.natDegree ≤ (n + 1) / 2)
    (hgdeg : g.natDegree ≤ (n + 1) / 2)
    (hquadTangent : ∀ ⦃F G H : ℝ[X]⦄,
      HasNonnegCoeffs F → HasNonnegCoeffs G → HasNonnegCoeffs H →
      StrictInterl F G → StrictInterl G H →
      (∀ b : ℝ, 0 ≤ b →
        (H + C (2 * b) * G + C (b ^ 2) * F).Splits) →
      ∀ a : ℝ, 0 ≤ a →
        StrictInterl (quadraticInterlacingTangent F G a)
          (quadraticInterlacingPencil F G H a)) :
    StrictInterl (balancedRunTransform n f) (balancedRunTransform n g) := by
  let T := balancedRunTransformLinearMap n
  let D := (n + 1) / 2
  have hTnn : ∀ ⦃p : ℝ[X]⦄,
      HasNonnegCoeffs p → HasNonnegCoeffs (T p) := by
    intro p hp
    simpa [T] using hp.balancedRunTransform (n := n)
  have hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits := by
    intro p hp hp0 hpdeg
    have hpdegN : p.natDegree ≤ n := hpdeg.trans (by
      dsimp [D]
      grind)
    constructor
    · simpa [T] using balancedRunTransform_ne_zero
        hp.hasNonnegCoeffs hp0 hpdegN
    · simpa [T] using
        (IsPFPolynomial.balancedRunTransform hn hp (by simpa [D] using hpdeg)).2.1.resolve_left
          (balancedRunTransform_ne_zero hp.hasNonnegCoeffs hp0 hpdegN)
  have hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1))) := by
    intro m hm
    have hmid : 2 * m + 1 ≤ n := by
      dsimp [D] at hm
      grind
    simpa [T] using
      strictInterl_balancedRunPolynomial_succ_of_two_mul_add_one_le n m hmid
  have hshift : PreservesPFShiftInterlacingOnDegree T D :=
    preservesPFShiftInterlacingOnDegree_of_monomials
      hTnn hTrr hmono hquadTangent
  simpa [T, D] using strictInterl_map_of_pfShift
    hfg hf hg hfdeg hgdeg hTnn hTrr hshift

end RealRooted
