import RealRooted.LiuOppositeSigns.Theorem21Statements
import RealRooted.ReflectedRootCountLocalConstancy

/-!
# Liu's bounded-interval continuity argument

This module implements the continuity step in the forward direction of Liu's
Theorem 2.1.  A same-owned combined-root gap is followed from the endpoint
polynomial that is root-free on the closed gap.  Fixed-degree reflection lets
the root count stay constant even when the original affine pencil drops degree.
-/

open Polynomial

namespace RealRooted

private theorem false_of_rightFamily_root_of_boundedIntervalContinuity
    {p q : ℝ[X]} {a b x μ : ℝ} (hax : a < x) (hxb : x < b) (hμ : 0 < μ)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (ha_no : ∀ η ∈ Set.Icc (0 : ℝ) μ, ¬ (p + C η * q).IsRoot a)
    (hsplit : ∀ η ∈ Set.Icc (0 : ℝ) μ, (p + C η * q).Splits)
    (hb_no : ∀ η ∈ Set.Icc (0 : ℝ) μ, ¬ (p + C η * q).IsRoot b)
    (hxroot : (p + C μ * q).IsRoot x) : False := by
  have hcount := rightFamily_card_roots_Ioo_eq_zero_param
    (f := p) (g := q) (lt_trans hax hxb) hμ ha_no hsplit hb_no
  have hp_card_zero : (p.roots.filter (fun r ↦ a < r ∧ r < b)).card = 0 := by
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro z hz hzab
    exact hp_no z hzab.1 hzab.2 (Polynomial.isRoot_of_mem_roots hz)
  have hfamily_card_zero :
      ((p + C μ * q).roots.filter (fun r ↦ a < r ∧ r < b)).card = 0 :=
    hcount.trans hp_card_zero
  have hμ_mem : μ ∈ Set.Icc (0 : ℝ) μ := ⟨hμ.le, le_rfl⟩
  have hfamily_ne : p + C μ * q ≠ 0 := by
    intro hzero
    apply ha_no μ hμ_mem
    simp [hzero, Polynomial.IsRoot.def]
  have hx_mem : x ∈ (p + C μ * q).roots :=
    (Polynomial.mem_roots hfamily_ne).mpr hxroot
  have hx_filter : x ∈ (p + C μ * q).roots.filter (fun r ↦ a < r ∧ r < b) :=
    Multiset.mem_filter.mpr ⟨hx_mem, hax, hxb⟩
  have hfilter_zero :
      (p + C μ * q).roots.filter (fun r ↦ a < r ∧ r < b) = 0 :=
    Multiset.card_eq_zero.mp hfamily_card_zero
  rw [hfilter_zero] at hx_filter
  simp at hx_filter

/-- Liu's bounded-interval continuity argument forces every parity-relevant
finite combined-root gap to have endpoints owned by opposite polynomials. -/
theorem OppositeLeadingSigns.crossOwnedNotOddGaps_of_boundedIntervalContinuity
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) :
    CrossOwnedNotOddGaps f g := by
  intro a b x hax hxb ha_root hb_root hgap hnot_odd
  have hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z :=
    fun z haz hzb ↦ (hgap z haz hzb).1
  have hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z :=
    fun z haz hzb ↦ (hgap z haz hzb).2
  obtain ⟨μ, hμ_pos, hμ_root, _⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_of_not_odd_intCard_roots_gt_sub
      hfg hno hf hg (hf_no x hax hxb) (hg_no x hax hxb) hnot_odd
  rcases ha_root with hfa | hga
  · rcases hb_root with hfb | hgb
    · exact False.elim <| false_of_rightFamily_root_of_boundedIntervalContinuity
        (p := g) (q := f) hax hxb (inv_pos.mpr hμ_pos) hg_no
        (fun _ _ ↦ hno.symm.rightFamily_not_isRoot_of_right_root hfa)
        (fun _ hη ↦ PosComboRealRooted.splits_add_right_of_nonneg
          (PosComboRealRooted.comm hfg) hg hη.1)
        (fun _ _ ↦ hno.symm.rightFamily_not_isRoot_of_right_root hfb)
        ((add_right_isRoot_iff_add_left_inv hμ_pos.ne').mp hμ_root)
    · exact Or.inl ⟨hfa, hgb⟩
  · rcases hb_root with hfb | hgb
    · exact Or.inr ⟨hga, hfb⟩
    · exact False.elim <| false_of_rightFamily_root_of_boundedIntervalContinuity
        (p := f) (q := g) hax hxb hμ_pos hf_no
        (fun _ _ ↦ hno.rightFamily_not_isRoot_of_right_root hga)
        (fun _ hη ↦ PosComboRealRooted.splits_add_right_of_nonneg hfg hf hη.1)
        (fun _ _ ↦ hno.rightFamily_not_isRoot_of_right_root hgb) hμ_root

/-- Liu's forward implication in the no-common, nonconstant, simple-root regime.

This is the rigorous part of the reduction used in the proof of Theorem 2.1:
compatibility supplies positive-combination real-rootedness, bounded root-count
continuity rules out same-owner odd gaps, and the finite descent gives the Liu
branch. The paper's assertion that no common zeros imply simple zeros is false
without an additional perturbation argument, so simplicity remains explicit
here rather than being inferred from `hno`. -/
theorem LiuOppositeSigns.theorem21RootCountBranches_of_compatible_noCommon_nonconstant_of_simple
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g := by
  have hfg : PosComboRealRooted f g :=
    posComboRealRooted_of_compatible_noCommon_nonconstant
      hcompat hno hg hg_deg
  exact theorem21RootCountBranches_of_crossOwned hsgn hf hg
    hf_deg hg_deg hsimple_f hsimple_g hno
    (hsgn.crossOwnedNotOddGaps_of_boundedIntervalContinuity hfg hno hf hg)

end RealRooted
