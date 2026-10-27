module

public import RealRooted.StaircaseSum

/-!
# Staircase-sum tactic frontends

Thin wrappers for staircase-weighted sums of interlacing nonnegative
sequences.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- At every index, the staircase sum at zero equals the ordinary list sum. -/
theorem staircaseSum_sequence_zero {FS : Nat → List ℝ[X]} :
    ∀ i : Nat, staircaseSum (FS i) 0 = (FS i).sum := fun i =>
  RealRooted.staircaseSum_zero (FS i)

/-- At every index, the staircase sum at the list length equals `X` times the ordinary sum. -/
theorem staircaseSum_sequence_length {FS : Nat → List ℝ[X]} :
    ∀ i : Nat, staircaseSum (FS i) (FS i).length = X * (FS i).sum := fun i =>
  RealRooted.staircaseSum_length (FS i)

/-- For pointwise nonnegative interlacing lists and valid indices `M i`, the selected entry
strictly interlaces the corresponding staircase sum. -/
theorem staircaseSum_sequence_strictInterl
    {FS : Nat → List ℝ[X]} {M : Nat → Nat}
    (hFS : ∀ i : Nat, IsInterlacingSeqNonneg (FS i))
    (hM : ∀ i : Nat, M i < (FS i).length) :
    ∀ i : Nat, StrictInterl ((FS i).get ⟨M i, hM i⟩) (staircaseSum (FS i) (M i)) :=
  fun i =>
    RealRooted.strictInterl_get_staircaseSum_of_isInterlacingSeqNonneg
      (hFS i) (hM i)

/-- For pointwise nonnegative interlacing lists and valid indices `M i`, every corresponding
staircase sum is nonzero and splits. -/
theorem staircaseSum_sequence_realrooted
    {FS : Nat → List ℝ[X]} {M : Nat → Nat}
    (hFS : ∀ i : Nat, IsInterlacingSeqNonneg (FS i))
    (hM : ∀ i : Nat, M i < (FS i).length) :
    ∀ i : Nat, staircaseSum (FS i) (M i) ≠ 0 ∧
      (staircaseSum (FS i) (M i)).Splits := fun i =>
  RealRooted.isRealRooted_staircaseSum_of_isInterlacingSeqNonneg
    (hFS i) (hM i)

end Tactic
end RealRooted
namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
