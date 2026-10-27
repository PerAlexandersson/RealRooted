module

public import RealRooted.Hermite.Poulain

/-!
# Hermite--Poulain tactic frontends

Thin wrappers around the finite constant-coefficient differential-operator
preservation theorem.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

namespace HermitePoulain

/-- The Hermite--Poulain differential-operator image of two nonzero splitting polynomials splits
when the image is nonzero. -/
theorem splits_of_nonzero {f g : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits)
    (hout :
      RealRooted.HermitePoulain.applyAsDifferentialOperator f g ≠ 0) :
    (RealRooted.HermitePoulain.applyAsDifferentialOperator f g).Splits := by
  rcases
    RealRooted.HermitePoulain.differential_operator_preserves_real_rooted
      hf hg with hzero | hsplits
  · exact (hout hzero).elim
  · exact hsplits

/-- Applying each nonzero splitting polynomial in `F` as a differential operator to the
corresponding nonzero splitting polynomial in `G` gives zero or a splitting polynomial. -/
theorem sequence_zero_or_splits {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hG : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits) :
    ∀ n : Nat,
      RealRooted.HermitePoulain.applyAsDifferentialOperator (F n) (G n)
          = 0 ∨
        (RealRooted.HermitePoulain.applyAsDifferentialOperator
          (F n) (G n)).Splits := fun n =>
  RealRooted.HermitePoulain.differential_operator_preserves_real_rooted
    (hF n) (hG n)

/-- Under the hypotheses of `sequence_zero_or_splits`, pointwise nonvanishing of the images
implies that every image splits. -/
theorem sequence_splits_of_nonzero {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, F n ≠ 0 ∧ (F n).Splits)
    (hG : ∀ n : Nat, G n ≠ 0 ∧ (G n).Splits)
    (hout :
      ∀ n : Nat,
        RealRooted.HermitePoulain.applyAsDifferentialOperator (F n) (G n)
          ≠ 0) :
    ∀ n : Nat,
      (RealRooted.HermitePoulain.applyAsDifferentialOperator
        (F n) (G n)).Splits := fun n =>
  splits_of_nonzero (hF n) (hG n) (hout n)

end HermitePoulain

end Tactic
end RealRooted
