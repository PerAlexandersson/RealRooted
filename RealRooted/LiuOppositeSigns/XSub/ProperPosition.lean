import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount

open Polynomial

namespace RealRooted

open LiuOppositeSigns

noncomputable section

/-- A positive-leading proper-position pair is a normalized Liu root-count
pair.  This bridges the project's usual `Prec` invariants to the proved
opposite-sign `X * p - μ * q` endpoint theorems. -/
theorem positiveSplitRootCountPair_of_prec
    {p q : ℝ[X]} (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (h : Prec p q) : PositiveSplitRootCountPair p q := by
  refine ⟨hp, hq, h.1.2, h.2.1.2, ?_⟩
  apply RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
    hp.ne_zero hq.ne_zero
  intro x _ _
  rcases h.natDegree_eq_or_eq_succ with hdeg | hsucc
  · have hlower := sameDegreeRootCountOriented_of_prec h hdeg x
    exact
      (sameDegreeRootCountAbove_nonRoot_iff_rootCount_nonRoot_pointwise
        h.1.2 h.2.1.2 hdeg x).2 ⟨by linarith, by linarith⟩
  · exact succDegreeRootCountAbove_of_prec h hsucc x

/-- Liu's proved `X`-subtraction theorem in the ordinary `Prec` interface.
The degree split required by the backend follows automatically from `Prec`. -/
theorem xSub_splits_of_prec_of_nonneg
    {p q : ℝ[X]} (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hprec : Prec p q) (hpnn : HasNonnegCoeffs p)
    (hqnn : HasNonnegCoeffs q) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  have hpair := positiveSplitRootCountPair_of_prec hp hq hprec
  rcases hprec.natDegree_eq_or_eq_succ with hdeg | hsucc
  · exact hpair.xSub_splits_of_same_degree_nonneg hpnn hqnn hdeg.symm hμ
  · exact hpair.xSub_splits_of_right_successor_nonneg hpnn hqnn hsucc hμ

end

end RealRooted
