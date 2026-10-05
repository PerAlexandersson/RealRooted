import RealRooted.CommonInterleaver.PairBridge.Reduction.CommonRoot
import RealRooted.CommonInterleaver.PairBridge.SuccDegree.SlotData

/-!
# Pair bridge reduction: shared degree-split core

Shared no-common degree-split, all-combinations, and affine-family reductions.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Internal all-combinations orientation bridge for the endpoint layer. -/
protected lemma CommonInterleaver.PairBridge.strictInterl_or_reverse_of_allComboRealRooted_ordered
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hall : AllComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    StrictInterl f g ∨ StrictInterl g f := by
  have hf0 : f ≠ 0 := hf_pos.ne_zero
  have hg0 : g ≠ 0 := hg_pos.ne_zero
  have hf_rr : (f ≠ 0 ∧ f.Splits) := hall.isRealRooted_left hf0
  have hg_rr : (g ≠ 0 ∧ g.Splits) := hall.isRealRooted_right hg0
  have hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by lia
  exact strictInterl_of_allComboRealRooted hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hall hdeg

end RealRooted
