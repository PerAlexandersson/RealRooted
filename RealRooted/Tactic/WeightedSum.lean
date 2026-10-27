module

public import RealRooted.WeightedSum

/-!
# Weighted-sum family lemmas

Pointwise lifts of the finite Wagner weighted-sum APIs.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- A pointwise weighted sum vanishes when every weight vanishes. -/
theorem weightedSum_sequence_zero
    {L : Nat → List (ℝ × ℝ[X])}
    (hzero : ∀ i : Nat, ∀ ap ∈ L i, ap.1 = 0) :
    ∀ i : Nat, weightedSum (L i) = 0 := fun i =>
  RealRooted.weightedSum_eq_zero_of_forall_coeff_zero _ (hzero i)

/-- A pointwise weighted sum has positive leading coefficient when its weights
are nonnegative, its terms have positive leading coefficients, and some weight
is positive. -/
theorem weightedSum_sequence_pos_lc
    {L : Nat → List (ℝ × ℝ[X])}
    (hnonneg : ∀ i : Nat, ∀ ap ∈ L i, 0 ≤ ap.1)
    (hpos : ∀ i : Nat, ∀ ap ∈ L i, HasPosLeadingCoeff ap.2)
    (hex : ∀ i : Nat, ∃ ap ∈ L i, 0 < ap.1) :
    ∀ i : Nat, HasPosLeadingCoeff (weightedSum (L i)) := fun i =>
  RealRooted.hasPosLeadingCoeff_weightedSum _ (hnonneg i) (hpos i) (hex i)

/-- A positive singleton weight, a strict interlacing, and a positive leading
coefficient give pointwise left weighted compatibility. -/
theorem weightedCompatibleLeft_sequence_singleton
    {H P : Nat → ℝ[X]} {a : Nat → ℝ}
    (ha : ∀ i : Nat, 0 < a i)
    (hstrictInterl : ∀ i : Nat, StrictInterl (H i) (P i))
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, WeightedCompatibleLeft (H i) [(a i, P i)] := fun i =>
  RealRooted.WeightedCompatibleLeft.singleton (ha i) (hstrictInterl i) (hpos i)

/-- A zero-weight head satisfying the interlacing and positivity conditions may
be added to a pointwise left-compatible tail. -/
theorem weightedCompatibleLeft_sequence_cons_zero
    {H P : Nat → ℝ[X]} {a : Nat → ℝ} {L : Nat → List (ℝ × ℝ[X])}
    (ha : ∀ i : Nat, a i = 0)
    (hstrictInterl : ∀ i : Nat, StrictInterl (H i) (P i))
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i)) :
    ∀ i : Nat, WeightedCompatibleLeft (H i) ((a i, P i) :: L i) := fun i =>
  RealRooted.WeightedCompatibleLeft.cons_zero (ha i) (hstrictInterl i) (hpos i) (hl i)

/-- A positive-weight head satisfying the interlacing and positivity conditions
may be added to a pointwise left-compatible tail. -/
theorem weightedCompatibleLeft_sequence_cons_pos
    {H P : Nat → ℝ[X]} {a : Nat → ℝ} {L : Nat → List (ℝ × ℝ[X])}
    (ha : ∀ i : Nat, 0 < a i)
    (hstrictInterl : ∀ i : Nat, StrictInterl (H i) (P i))
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i)) :
    ∀ i : Nat, WeightedCompatibleLeft (H i) ((a i, P i) :: L i) := fun i =>
  RealRooted.WeightedCompatibleLeft.cons_pos (ha i) (hstrictInterl i) (hpos i) (hl i)

/-- A pointwise left-compatible weighted family is strictly interlaced by its
common left polynomial. -/
theorem weightedCompatibleLeft_sequence_strictInterl
    {H : Nat → ℝ[X]} {L : Nat → List (ℝ × ℝ[X])}
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i)) :
    ∀ i : Nat, StrictInterl (H i) (weightedSum (L i)) := fun i =>
  RealRooted.WeightedCompatibleLeft.toStrictInterl (hl i)

/-- Unit-weight pointwise left compatibility makes each common left polynomial
strictly interlace the corresponding unweighted sum. -/
theorem sum_sequence_left_strictInterl
    {H : Nat → ℝ[X]} {L : Nat → List ℝ[X]}
    (hl : ∀ i : Nat,
      WeightedCompatibleLeft (H i) ((L i).map (fun p => ((1 : ℝ), p)))) :
    ∀ i : Nat, StrictInterl (H i) (L i).sum := fun i =>
  RealRooted.WeightedCompatibleLeft.toStrictInterl_sum (hl i)

/-- Pointwise nonnegative weighted sums strictly interlace a common right
polynomial when every term does, all terms have positive leading coefficient,
and some weight is positive. -/
theorem weightedSum_sequence_right_strictInterl
    {L : Nat → List (ℝ × ℝ[X])} {H : Nat → ℝ[X]}
    (hnonneg : ∀ i : Nat, ∀ ap ∈ L i, 0 ≤ ap.1)
    (hstrictInterl : ∀ i : Nat, ∀ ap ∈ L i, StrictInterl ap.2 (H i))
    (hpos : ∀ i : Nat, ∀ ap ∈ L i, HasPosLeadingCoeff ap.2)
    (hex : ∀ i : Nat, ∃ ap ∈ L i, 0 < ap.1) :
    ∀ i : Nat, StrictInterl (weightedSum (L i)) (H i) := fun i =>
  RealRooted.StrictInterl.weightedSum_right_of_nonneg
    _ _ (hnonneg i) (hstrictInterl i) (hpos i) (hex i)

/-- A nonempty pointwise sum strictly interlaces a common right polynomial when
every positive-leading term does. -/
theorem sum_sequence_right_strictInterl
    {L : Nat → List ℝ[X]} {H : Nat → ℝ[X]}
    (hstrictInterl : ∀ i : Nat, ∀ p ∈ L i, StrictInterl p (H i))
    (hpos : ∀ i : Nat, ∀ p ∈ L i, HasPosLeadingCoeff p)
    (hne : ∀ i : Nat, L i ≠ []) :
    ∀ i : Nat, StrictInterl (L i).sum (H i) := fun i =>
  RealRooted.StrictInterl.sum_right _ _ (hstrictInterl i) (hpos i) (hne i)

end Tactic
end RealRooted

