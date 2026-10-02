import RealRooted.CommonInterleaver.PairBridge.SuccDegree.RootCount

/-!
# Pair bridge succ-degree closed-segment consequences

Closed-segment, endpoint-sign, and no-gap consequences of succ-degree root counts.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The exact gap-two obstruction closes the compatible common-non-root
root-count target.  The proof is by strong induction on the lower endpoint
degree: low degrees are explicit, while degree at least two uses derivative
induction for the gap-at-most-two bound and the no-gap hypothesis to rule out
the remaining exact gap. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo
    (hgap : CompatibleSuccDegreeRootCountAboveNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  have hmain :
      ∀ n : ℕ, ∀ {f g : ℝ[X]},
        f.natDegree = n →
        Compatible f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        g.natDegree = f.natDegree + 1 →
        f.Splits →
        ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
          ((f.roots.filter (x < ·)).card : ℤ) -
              (g.roots.filter (x < ·)).card ≤ 1 ∧
          ((g.roots.filter (x < ·)).card : ℤ) -
              (f.roots.filter (x < ·)).card ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f g hfdeg_eq hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
      by_cases hfdeg : 2 ≤ f.natDegree
      · have hf'_pos : HasPosLeadingCoeff f.derivative :=
          hf_pos.derivative (by lia)
        have hg'_pos : HasPosLeadingCoeff g.derivative :=
          hg_pos.derivative (by rw [hdeg]; lia)
        have hdeg' : g.derivative.natDegree = f.derivative.natDegree + 1 :=
          succDegree_derivative_natDegree_eq hdeg (by lia)
        have hf'_split : f.derivative.Splits :=
          (derivative_interlaces hf_split hfdeg).2.1.2
        have hfder_lt_self : f.derivative.natDegree < f.natDegree := by
          rw [f.natDegree_derivative]
          lia
        have hfder_lt : f.derivative.natDegree < n := by rwa [hfdeg_eq] at hfder_lt_self
        have hder_bound :
            ∀ y : ℝ,
              ¬ f.derivative.IsRoot y → ¬ g.derivative.IsRoot y →
                ((f.derivative.roots.filter (y < ·)).card : ℤ) -
                    (g.derivative.roots.filter (y < ·)).card ≤ 1 ∧
                ((g.derivative.roots.filter (y < ·)).card : ℤ) -
                    (f.derivative.roots.filter (y < ·)).card ≤ 1 :=
          fun y hyf hyg => ih f.derivative.natDegree hfder_lt rfl hcomp.derivative
            hf'_pos hg'_pos hdeg' hf'_split y hyf hyg
        obtain ⟨hfg_le2, hgf_le2⟩ :=
          compatibleSuccDegreeRootCountAbove_le_two_of_derivative_bound
            hcomp hf_pos hg_pos hdeg hf_split hfdeg hder_bound x
        obtain ⟨hfg_ne2, hgf_ne2⟩ :=
          hgap hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
        exact ⟨int_le_one_of_le_two_ne_two hfg_le2 hfg_ne2,
          int_le_one_of_le_two_ne_two hgf_le2 hgf_ne2⟩
      · have hfdeg_le_one : f.natDegree ≤ 1 :=
          Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hfdeg)
        exact compatibleSuccDegreeRootCountAbove_of_natDegree_le_one
          hcomp hf_pos hg_pos hdeg hf_split hfdeg_le_one x
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
  exact hmain f.natDegree rfl hcomp hf_pos hg_pos hdeg hf_split x hxf hxg

/-- The closed-segment no-gap-two theorem closes the compatible succ-degree
common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegment
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_noGapTwo
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment hclosed)

/-- Closed-segment endpoint count equality closes the compatible succ-degree
common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegment
    (compatibleSuccDegreeClosedSegmentNoGapTwo_of_countEq hcount)

/-- Closed-segment endpoint count equality also supplies the positive-combo
succ-degree common-non-root upper root-count leaf used by the repaired #42
pair-interleaver route. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
    (compatibleSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq hcount)

end RealRooted
