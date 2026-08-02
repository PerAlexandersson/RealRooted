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

private theorem natDegree_add_C_mul_le_max (p q : ℝ[X]) (eta : ℝ) :
    (p + C eta * q).natDegree ≤ max p.natDegree q.natDegree := by
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (le_max_left _ _)
      ((Polynomial.natDegree_C_mul_le eta q).trans (le_max_right _ _)))

private theorem false_of_rightFamily_root_of_Ioo_count_eq_zero_param
    {p q : ℝ[X]} {a b x mu : ℝ} (hax : a < x) (hxb : x < b)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (ha_no : ¬ (p + C mu * q).IsRoot a)
    (hxroot : (p + C mu * q).IsRoot x)
    (hcount : ((p + C mu * q).roots.filter (fun r ↦ a < r ∧ r < b)).card =
      (p.roots.filter (fun r ↦ a < r ∧ r < b)).card) : False := by
  have hp_card_zero : (p.roots.filter (fun r ↦ a < r ∧ r < b)).card = 0 := by
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro z hz hzab
    exact hp_no z hzab.1 hzab.2 (Polynomial.isRoot_of_mem_roots hz)
  have hfamily_card_zero :
      ((p + C mu * q).roots.filter (fun r ↦ a < r ∧ r < b)).card = 0 :=
    hcount.trans hp_card_zero
  have hfamily_ne : p + C mu * q ≠ 0 := by
    intro hzero
    apply ha_no
    simp [hzero, Polynomial.IsRoot.def]
  have hx_mem : x ∈ (p + C mu * q).roots :=
    (Polynomial.mem_roots hfamily_ne).mpr hxroot
  have hx_filter : x ∈ (p + C mu * q).roots.filter (fun r ↦ a < r ∧ r < b) :=
    Multiset.mem_filter.mpr ⟨hx_mem, hax, hxb⟩
  have hfilter_zero :
      (p + C mu * q).roots.filter (fun r ↦ a < r ∧ r < b) = 0 :=
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
  obtain ⟨mu, hmu_pos, hmu_root, _⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_of_not_odd_intCard_roots_gt_sub
      hfg hno hf hg (hf_no x hax hxb) (hg_no x hax hxb) hnot_odd
  rcases ha_root with hfa | hga
  · rcases hb_root with hfb | hgb
    · have hmu_inv_pos : 0 < mu⁻¹ := inv_pos.mpr hmu_pos
      have hmu_inv_root : (g + C mu⁻¹ * f).IsRoot x :=
        (add_right_isRoot_iff_add_left_inv hmu_pos.ne').mp hmu_root
      have hcount :
          ((g + C mu⁻¹ * f).roots.filter (fun r ↦ a < r ∧ r < b)).card =
            (g.roots.filter (fun r ↦ a < r ∧ r < b)).card := by
        apply rightFamily_card_roots_Ioo_eq_zero_param_of_degree_bound
          (f := g) (g := f) (N := max g.natDegree f.natDegree)
          (lt_trans hax hxb) hmu_inv_pos
        · intro eta _
          exact natDegree_add_C_mul_le_max g f eta
        · intro eta _
          exact hno.symm.rightFamily_not_isRoot_of_right_root hfa
        · intro eta heta
          exact PosComboRealRooted.splits_add_right_of_nonneg
            (PosComboRealRooted.comm hfg) hg heta.1
        · intro eta _
          exact hno.symm.rightFamily_not_isRoot_of_right_root hfb
      exact False.elim <| false_of_rightFamily_root_of_Ioo_count_eq_zero_param
        hax hxb hg_no
        (hno.symm.rightFamily_not_isRoot_of_right_root (mu := mu⁻¹) hfa)
        hmu_inv_root hcount
    · exact Or.inl ⟨hfa, hgb⟩
  · rcases hb_root with hfb | hgb
    · exact Or.inr ⟨hga, hfb⟩
    · have hcount :
          ((f + C mu * g).roots.filter (fun r ↦ a < r ∧ r < b)).card =
            (f.roots.filter (fun r ↦ a < r ∧ r < b)).card := by
        apply rightFamily_card_roots_Ioo_eq_zero_param_of_degree_bound
          (f := f) (g := g) (N := max f.natDegree g.natDegree)
          (lt_trans hax hxb) hmu_pos
        · intro eta _
          exact natDegree_add_C_mul_le_max f g eta
        · intro eta _
          exact hno.rightFamily_not_isRoot_of_right_root hga
        · intro eta heta
          exact PosComboRealRooted.splits_add_right_of_nonneg hfg hf heta.1
        · intro eta _
          exact hno.rightFamily_not_isRoot_of_right_root hgb
      exact False.elim <| false_of_rightFamily_root_of_Ioo_count_eq_zero_param
        hax hxb hf_no (hno.rightFamily_not_isRoot_of_right_root (mu := mu) hga)
        hmu_root hcount

end RealRooted
