import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount

open Polynomial

namespace RealRooted

open LiuOppositeSigns

noncomputable section

/-- A positive-leading strictly interlacing pair is a normalized Liu root-count
pair.  This bridges the project's usual `StrictInterl` invariants to the proved
opposite-sign `X * p - μ * q` endpoint theorems. -/
theorem positiveSplitRootCountPair_of_strictInterl
    {p q : ℝ[X]} (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (h : StrictInterl p q) : PositiveSplitRootCountPair p q := by
  refine ⟨hp, hq, h.1.2, h.2.1.2, ?_⟩
  apply RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
    hp.ne_zero hq.ne_zero
  intro x _ _
  rcases h.natDegree_eq_or_eq_succ with hdeg | hsucc
  · have hlower := sameDegreeRootCountOriented_of_strictInterl h hdeg x
    exact
      (sameDegreeRootCountAbove_nonRoot_iff_rootCount_nonRoot_pointwise
        h.1.2 h.2.1.2 hdeg x).2 ⟨by linarith, by linarith⟩
  · exact succDegreeRootCountAbove_of_strictInterl h hsucc x

/-- Liu's proved `X`-subtraction theorem in the ordinary `StrictInterl` interface.
The degree split required by the backend follows automatically from `StrictInterl`. -/
theorem xSub_splits_of_strictInterl_of_nonneg
    {p q : ℝ[X]} (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hstrictInterl : StrictInterl p q) (hpnn : HasNonnegCoeffs p)
    (hqnn : HasNonnegCoeffs q) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  have hpair := positiveSplitRootCountPair_of_strictInterl hp hq hstrictInterl
  rcases hstrictInterl.natDegree_eq_or_eq_succ with hdeg | hsucc
  · exact hpair.xSub_splits_of_same_degree_nonneg hpnn hqnn hdeg.symm hμ
  · exact hpair.xSub_splits_of_right_successor_nonneg hpnn hqnn hsucc hμ

@[deprecated positiveSplitRootCountPair_of_strictInterl (since := "2026-09-26")]
alias positiveSplitRootCountPair_of_prec := positiveSplitRootCountPair_of_strictInterl

@[deprecated xSub_splits_of_strictInterl_of_nonneg (since := "2026-09-26")]
alias xSub_splits_of_prec_of_nonneg := xSub_splits_of_strictInterl_of_nonneg

end

end RealRooted
