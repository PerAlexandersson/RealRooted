import RealRooted.Compatibility.InterleaverBridge
import RealRooted.CommonInterleaver.SuccDegreeLowDegree
import RealRooted.GammaRealRoots
import RealRooted.DegreeIncreasingLocalLowerCount
import RealRooted.SmallPositiveParameterCount

/-!
# Succ-degree root counts along the closed segment

For a compatible successor-degree pair, the upper root counts agree at any
threshold that the closed segment from `f` to `g` never crosses.  This rules
out exact upper-count gaps of two, and derivative induction then bounds the
upper-count difference by one at every common non-root threshold.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Closed-segment count stability for a compatible successor-degree pair: if a
threshold is never a root along the closed segment from the lower-degree
endpoint `f` to the higher-degree endpoint `g`, then the endpoint upper root
counts at that threshold agree. -/
theorem Compatible.succDegree_card_roots_gt_eq_of_closedSegment
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  have hx_roots : x ∉ f.roots :=
    fun hx => hxf ((Polynomial.mem_roots hf_pos.ne_zero).mp hx)
  have hlt : f.natDegree < g.natDegree := by simp [hdeg]
  have hfg_split_pos : ∀ μ : ℝ, 0 < μ → (f + C μ * g).Splits := fun μ hμ ↦ by
    rcases hcomp 1 μ zero_le_one hμ.le with hzero | hrr
    · simp [show f + C μ * g = 0 by grind]
    · grind
  have hgf_split : ∀ ν ∈ Set.Icc (0 : ℝ) 1, (g + C ν * f).Splits := fun ν hν ↦ by
    rcases hcomp.comm 1 ν zero_le_one hν.1 with hzero | hrr
    · simp [show g + C ν * f = 0 by grind]
    · grind
  refine card_filter_gt_endpoint_eq_of_local_lower_counts
    hf_pos hg_pos hdeg hf_split hx_roots
    ?_
    ?_ ?_ ?_ ?_
  · intro ρ hρ
    obtain ⟨δ, hδ_pos, hδ⟩ := degreeIncreasing_local_lower_count hf_split hlt ρ hρ
    grind
  · simp_all
  · exact fun μ hμ _ ↦ closedSegment_not_isRoot_add_right_of_nonneg hμ.le hseg
  · simp_all
  · intro ν hν
    refine closedSegment_not_isRoot_add_right_of_nonneg
      (f := g) (g := f) (x := x) hν.1 ?_
    grind

/-- A compatible successor-degree pair has no exact upper root-count gap of two
at a common non-root threshold: such a gap would keep the threshold off the
closed segment, where the endpoint counts agree. -/
theorem Compatible.succDegree_rootCountAbove_sub_ne_two
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≠ 2 := by
  constructor
  · intro hgap
    have hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x := by
      intro β hβ0 hβ1
      exact
        compatibleSuccDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
          hcomp hf_pos hg_pos hdeg hf_split hβ0 hβ1 hxf hxg hgap
    have hcard :
        ((f.roots.filter (x < ·)).card : ℤ) = (g.roots.filter (x < ·)).card := by
      exact_mod_cast
        hcomp.succDegree_card_roots_gt_eq_of_closedSegment
          hf_pos hg_pos hdeg hf_split hxf hseg
    linarith
  · intro hgap
    have hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x := by
      intro β hβ0 hβ1
      exact
        compatibleSuccDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
          hcomp hf_pos hg_pos hdeg hf_split hβ0 hβ1 hxf hxg hgap
    have hcard :
        ((f.roots.filter (x < ·)).card : ℤ) = (g.roots.filter (x < ·)).card := by
      exact_mod_cast
        hcomp.succDegree_card_roots_gt_eq_of_closedSegment
          hf_pos hg_pos hdeg hf_split hxf hseg
    linarith

/-- For a compatible successor-degree pair with positive leading coefficients
and split lower-degree endpoint, the upper root counts at every common non-root
threshold differ by at most one.  The proof is by strong induction on the lower
endpoint degree: low degrees are explicit, while degree at least two uses
derivative induction for the gap-at-most-two bound and
`Compatible.succDegree_rootCountAbove_sub_ne_two` to rule out the remaining
exact gap. -/
theorem compatibleSuccDegree_rootCountAbove_diff_le_one_of_nonRoot
    ⦃f g : ℝ[X]⦄ (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits) :
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
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
          hcomp.succDegree_rootCountAbove_sub_ne_two hf_pos hg_pos hdeg hf_split hxf hxg
        exact ⟨int_le_one_of_le_two_ne_two hfg_le2 hfg_ne2,
          int_le_one_of_le_two_ne_two hgf_le2 hgf_ne2⟩
      · have hfdeg_le_one : f.natDegree ≤ 1 :=
          Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hfdeg)
        exact compatibleSuccDegreeRootCountAbove_of_natDegree_le_one
          hcomp hf_pos hg_pos hdeg hf_split hfdeg_le_one x
  intro x hxf hxg
  exact hmain f.natDegree rfl hcomp hf_pos hg_pos hdeg hf_split x hxf hxg

end RealRooted
