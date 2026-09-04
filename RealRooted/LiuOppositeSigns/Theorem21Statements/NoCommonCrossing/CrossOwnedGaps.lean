import RealRooted.LiuOppositeSigns.Theorem21Statements.NoCommonCrossing.Witnesses

/-!
# Cross-owned gaps for Liu's no-common-root argument

This module assembles the local crossing witnesses into Liu's cross-owned
finite-gap invariant.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Endpoint-count-difference form of the Liu odd-interval ownership argument.
If a root-free interval has both endpoints in the combined root set and the
strict-upper root-count difference is not odd at a sample point, then the
endpoints are cross-owned, provided the same-owner endpoint count differences
are stable across the two endpoints. -/
theorem OppositeLeadingSigns.cross_owner_roots_of_not_odd_of_endpoint_count_diffs
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x νL νR : ℝ}
    (hgap : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b)
    (ha_root : f.IsRoot a ∨ g.IsRoot a)
    (hb_root : f.IsRoot b ∨ g.IsRoot b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hνL_pos : 0 < νL)
    (hνL_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → μ ≤ νL)
    (hdegL : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ νL,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hleft_count_sub : f.IsRoot a → f.IsRoot b →
      (((g + C νL⁻¹ * f).roots.filter (a < ·)).card : ℤ) -
          (g.roots.filter (a < ·)).card =
        (((g + C νL⁻¹ * f).roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card)
    (hνR_pos : 0 < νR)
    (hνR_small : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → νR ≤ μ)
    (hdegR : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc νR μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hright_count_sub : g.IsRoot a → g.IsRoot b →
      (((f + C νR * g).roots.filter (a < ·)).card : ℤ) -
          (f.roots.filter (a < ·)).card =
        (((f + C νR * g).roots.filter (b < ·)).card : ℤ) -
          (f.roots.filter (b < ·)).card) :
    (f.IsRoot a ∧ g.IsRoot b) ∨ (g.IsRoot a ∧ f.IsRoot b) := by
  have hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z :=
    fun z hz₁ hz₂ => (hgap z hz₁ hz₂).1
  have hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z :=
    fun z hz₁ hz₂ => (hgap z hz₁ hz₂).2
  rcases ha_root with hfa | hga
  · rcases hb_root with hfb | hgb
    · exact False.elim <|
        hsgn.false_of_left_roots_add_left_inv_count_sub_eq_right
          hfg hno hf hg hfa hfb hf_no hg_no hax hxb hax hxb hnot_odd
          hνL_pos hνL_large hdegL (hleft_count_sub hfa hfb)
    · exact Or.inl ⟨hfa, hgb⟩
  · rcases hb_root with hfb | hgb
    · exact Or.inr ⟨hga, hfb⟩
    · exact False.elim <|
        hsgn.false_of_right_roots_add_right_small_count_sub_eq_left
          hfg hno hf hg hga hgb hf_no hg_no hax hxb hax hxb hnot_odd
          hνR_pos hνR_small hdegR (hright_count_sub hga hgb)

/-- Endpoint-count form of the Liu odd-interval ownership argument.  If a
root-free interval has both endpoints in the combined root set and the
strict-upper root-count difference is not odd at a sample point, then the
endpoints are cross-owned, provided the same-owner endpoint count equalities
are already available. -/
theorem OppositeLeadingSigns.cross_owner_roots_of_not_odd_of_endpoint_counts
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x νL νR : ℝ}
    (hgap : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b)
    (ha_root : f.IsRoot a ∨ g.IsRoot a)
    (hb_root : f.IsRoot b ∨ g.IsRoot b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hνL_pos : 0 < νL)
    (hνL_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → μ ≤ νL)
    (hdegL : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ νL,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hleft_count_a : f.IsRoot a →
      ((g + C νL⁻¹ * f).roots.filter (a < ·)).card =
        (g.roots.filter (a < ·)).card)
    (hleft_count_b : f.IsRoot b →
      ((g + C νL⁻¹ * f).roots.filter (b < ·)).card =
        (g.roots.filter (b < ·)).card)
    (hνR_pos : 0 < νR)
    (hνR_small : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → νR ≤ μ)
    (hdegR : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc νR μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hright_count_a : g.IsRoot a →
      ((f + C νR * g).roots.filter (a < ·)).card =
        (f.roots.filter (a < ·)).card)
    (hright_count_b : g.IsRoot b →
      ((f + C νR * g).roots.filter (b < ·)).card =
        (f.roots.filter (b < ·)).card) :
    (f.IsRoot a ∧ g.IsRoot b) ∨ (g.IsRoot a ∧ f.IsRoot b) := by
  exact hsgn.cross_owner_roots_of_not_odd_of_endpoint_count_diffs
    hfg hno hf hg hgap hax hxb ha_root hb_root hnot_odd
    hνL_pos hνL_large hdegL
    (fun hfa hfb => by rw [hleft_count_a hfa, hleft_count_b hfb]; simp)
    hνR_pos hνR_small hdegR
    (fun hga hgb => by rw [hright_count_a hga, hright_count_b hgb]; simp)

/-- Endpoint-ownership form of the Liu odd-interval argument.  If a root-free
interval has both endpoints in the combined root set and the strict-upper
root-count difference is not odd at a sample point, then the endpoints are
cross-owned: one belongs to `f` and the other to `g`.

The analytic interval hypotheses discharge endpoint count equalities, then the
same-owner cases are routed through
`OppositeLeadingSigns.cross_owner_roots_of_not_odd_of_endpoint_counts` and the
endpoint count-difference form
`OppositeLeadingSigns.cross_owner_roots_of_not_odd_of_endpoint_count_diffs`. -/
theorem OppositeLeadingSigns.cross_owner_roots_of_not_odd
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x νL νR : ℝ}
    (hgap : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b)
    (ha_root : f.IsRoot a ∨ g.IsRoot a)
    (hb_root : f.IsRoot b ∨ g.IsRoot b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hνL_pos : 0 < νL)
    (hνL_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → μ ≤ νL)
    (hdegL : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ νL,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hdegL_inv : ∀ η ∈ Set.Icc (0 : ℝ) νL⁻¹,
      (g + C η * f).natDegree = (g + C (0 : ℝ) * f).natDegree)
    (hνR_pos : 0 < νR)
    (hνR_small : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → νR ≤ μ)
    (hdegR : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc νR μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hdegR_zero : ∀ η ∈ Set.Icc (0 : ℝ) νR,
      (f + C η * g).natDegree = (f + C (0 : ℝ) * g).natDegree) :
    (f.IsRoot a ∧ g.IsRoot b) ∨ (g.IsRoot a ∧ f.IsRoot b) := by
  have hsplitL_inv : ∀ η ∈ Set.Icc (0 : ℝ) νL⁻¹, (g + C η * f).Splits :=
    fun η hη =>
      PosComboRealRooted.splits_add_right_of_nonneg (PosComboRealRooted.comm hfg) hg hη.1
  have hsplitR : ∀ η ∈ Set.Icc (0 : ℝ) νR, (f + C η * g).Splits :=
    fun η hη => PosComboRealRooted.splits_add_right_of_nonneg hfg hf hη.1
  have hleft_count : ∀ c : ℝ, f.IsRoot c →
      ((g + C νL⁻¹ * f).roots.filter (c < ·)).card =
        (g.roots.filter (c < ·)).card := by
    intro c hfc
    exact
      rightFamily_card_roots_gt_eq_zero_param_of_constant_degree
        (f := g) (g := f) (μ := νL⁻¹) (x := c) (inv_pos.mpr hνL_pos)
        hdegL_inv hsplitL_inv
        (fun η _ => hno.symm.rightFamily_not_isRoot_of_right_root hfc)
  have hright_count : ∀ c : ℝ, g.IsRoot c →
      ((f + C νR * g).roots.filter (c < ·)).card =
        (f.roots.filter (c < ·)).card := by
    intro c hgc
    exact
      rightFamily_card_roots_gt_eq_zero_param_of_constant_degree
        (f := f) (g := g) (μ := νR) (x := c) hνR_pos hdegR_zero hsplitR
        (fun η _ => hno.rightFamily_not_isRoot_of_right_root hgc)
  exact hsgn.cross_owner_roots_of_not_odd_of_endpoint_counts
    hfg hno hf hg hgap hax hxb ha_root hb_root hnot_odd
    hνL_pos hνL_large hdegL
    (hleft_count a) (hleft_count b)
    hνR_pos hνR_small hdegR
    (hright_count a) (hright_count b)

/-- Supplier for the parity-guarded consecutive-root ownership input from
endpoint count-difference stability.  This is the weaker analytic boundary:
same-owner cases only need the transported strict-upper count offset to be the
same at the two endpoint roots. -/
theorem OppositeLeadingSigns.crossOwnedNotOddGaps_of_endpoint_count_diffs
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) (νL νR : ℝ → ℝ)
    (hνL_pos : ∀ x : ℝ, 0 < νL x)
    (hνL_large : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → μ ≤ νL x)
    (hdegL : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ (νL x),
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hleft_count_sub : ∀ x a b : ℝ, f.IsRoot a → f.IsRoot b →
      (((g + C (νL x)⁻¹ * f).roots.filter (a < ·)).card : ℤ) -
          (g.roots.filter (a < ·)).card =
        (((g + C (νL x)⁻¹ * f).roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card)
    (hνR_pos : ∀ x : ℝ, 0 < νR x)
    (hνR_small : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → νR x ≤ μ)
    (hdegR : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc (νR x) μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hright_count_sub : ∀ x a b : ℝ, g.IsRoot a → g.IsRoot b →
      (((f + C (νR x) * g).roots.filter (a < ·)).card : ℤ) -
          (f.roots.filter (a < ·)).card =
        (((f + C (νR x) * g).roots.filter (b < ·)).card : ℤ) -
          (f.roots.filter (b < ·)).card) :
    CrossOwnedNotOddGaps f g := by
  intro a b x hax hxb ha_root hb_root hgap hnot_odd
  exact hsgn.cross_owner_roots_of_not_odd_of_endpoint_count_diffs
    hfg hno hf hg hgap hax hxb ha_root hb_root hnot_odd
    (hνL_pos x) (hνL_large x) (hdegL x)
    (hleft_count_sub x a b)
    (hνR_pos x) (hνR_small x) (hdegR x)
    (hright_count_sub x a b)

/-- Supplier for the parity-guarded consecutive-root ownership input from an
open-gap no-root hypothesis for the endpoint families.  This is the finite
bridge from the analytic goal "the transported family has no roots in the
finite open gap" to the count-difference boundary.  The right endpoint is
discharged internally from `NoCommonRoots`, so the analytic input only needs
open-gap root-freeness for the transported families. -/
theorem OppositeLeadingSigns.crossOwnedNotOddGaps_of_no_isRoot_Ioo
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) (νL νR : ℝ → ℝ)
    (hνL_pos : ∀ x : ℝ, 0 < νL x)
    (hνL_large : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → μ ≤ νL x)
    (hdegL : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ (νL x),
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hleft_no : ∀ x a b : ℝ, a < x → x < b → f.IsRoot a → f.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ z : ℝ, a < z → z < b → ¬ (g + C (νL x)⁻¹ * f).IsRoot z)
    (hνR_pos : ∀ x : ℝ, 0 < νR x)
    (hνR_small : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → νR x ≤ μ)
    (hdegR : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc (νR x) μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hright_no : ∀ x a b : ℝ, a < x → x < b → g.IsRoot a → g.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ z : ℝ, a < z → z < b → ¬ (f + C (νR x) * g).IsRoot z) :
    CrossOwnedNotOddGaps f g := by
  intro a b x hax hxb ha_root hb_root hgap hnot_odd
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  have hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z :=
    fun z hz₁ hz₂ => (hgap z hz₁ hz₂).1
  have hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z :=
    fun z hz₁ hz₂ => (hgap z hz₁ hz₂).2
  have count_sub_eq_of_same_owner {p q r : ℝ[X]}
      (hpq : NoCommonRoots p q) (hpa : p.IsRoot a) (hpb : p.IsRoot b)
      (hq_no : ∀ z : ℝ, a < z → z < b → ¬ q.IsRoot z)
      (hr_no : ∀ z : ℝ, a < z → z < b → ¬ r.IsRoot z)
      (hrb : ¬ r.IsRoot b) :
      ((r.roots.filter (a < ·)).card : ℤ) - (q.roots.filter (a < ·)).card =
        ((r.roots.filter (b < ·)).card : ℤ) -
          (q.roots.filter (b < ·)).card := by
    have hq_no_Ioc : ∀ z : ℝ, a < z → z ≤ b → ¬ q.IsRoot z := by
      intro z haz hzb
      exact hpq.right_not_isRoot_Icc_of_left_roots hpa hpb hq_no z
        ⟨le_of_lt haz, hzb⟩
    have hr_no_Ioc : ∀ z : ℝ, a < z → z ≤ b → ¬ r.IsRoot z := by
      intro z haz hzb
      by_cases hzb_eq : z = b
      · simpa [hzb_eq] using hrb
      · exact hr_no z haz (lt_of_le_of_ne hzb hzb_eq)
    exact card_roots_filter_gt_sub_eq_of_no_isRoot_Ioc hab
      hr_no_Ioc hq_no_Ioc
  exact hsgn.cross_owner_roots_of_not_odd_of_endpoint_count_diffs
    hfg hno hf hg hgap hax hxb ha_root hb_root hnot_odd
    (hνL_pos x) (hνL_large x) (hdegL x)
    (fun hfa hfb =>
      count_sub_eq_of_same_owner hno hfa hfb hg_no
        (hleft_no x a b hax hxb hfa hfb hgap)
        (hno.symm.rightFamily_not_isRoot_of_right_root hfb))
    (hνR_pos x) (hνR_small x) (hdegR x)
    (fun hga hgb =>
      count_sub_eq_of_same_owner hno.symm hga hgb hf_no
        (hright_no x a b hax hxb hga hgb hgap)
        (hno.rightFamily_not_isRoot_of_right_root hgb))

/-- Supplier for the parity-guarded consecutive-root ownership input from
endpoint count equalities.  This is a convenient specialization of
`OppositeLeadingSigns.crossOwnedNotOddGaps_of_endpoint_count_diffs`; later
analytic proofs should target the count-difference boundary directly unless
they naturally produce exact endpoint counts. -/
theorem OppositeLeadingSigns.crossOwnedNotOddGaps_of_endpoint_counts
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) (νL νR : ℝ → ℝ)
    (hνL_pos : ∀ x : ℝ, 0 < νL x)
    (hνL_large : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → μ ≤ νL x)
    (hdegL : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ (νL x),
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hleft_count : ∀ x c : ℝ, f.IsRoot c →
      ((g + C (νL x)⁻¹ * f).roots.filter (c < ·)).card =
        (g.roots.filter (c < ·)).card)
    (hνR_pos : ∀ x : ℝ, 0 < νR x)
    (hνR_small : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → νR x ≤ μ)
    (hdegR : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc (νR x) μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hright_count : ∀ x c : ℝ, g.IsRoot c →
      ((f + C (νR x) * g).roots.filter (c < ·)).card =
        (f.roots.filter (c < ·)).card) :
    CrossOwnedNotOddGaps f g := by
  exact hsgn.crossOwnedNotOddGaps_of_endpoint_count_diffs
    hfg hno hf hg νL νR hνL_pos hνL_large hdegL
    (fun x a b hfa hfb => by rw [hleft_count x a hfa, hleft_count x b hfb]; simp)
    hνR_pos hνR_small hdegR
    (fun x a b hga hgb => by rw [hright_count x a hga, hright_count x b hgb]; simp)

/-- Local-gap supplier for the parity-guarded consecutive-root ownership input
from open-gap root-freeness of endpoint families.  Unlike
`OppositeLeadingSigns.crossOwnedNotOddGaps_of_no_isRoot_Ioo`, this theorem lets
the large or small parameter be chosen from the concrete root-free gap rather
than from a global function of the sample point. -/
theorem OppositeLeadingSigns.crossOwnedNotOddGaps_of_local_no_isRoot_Ioo
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits)
    (hleft_local : ∀ x a b : ℝ, a < x → x < b →
      f.IsRoot a → f.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∃ ν : ℝ, 0 < ν ∧
        (∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → μ ≤ ν) ∧
        (∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
          ∀ τ ∈ Set.Icc μ ν,
            (f + C τ * g).natDegree = (f + C μ * g).natDegree) ∧
        ∀ z : ℝ, a < z → z < b → ¬ (g + C ν⁻¹ * f).IsRoot z)
    (hright_local : ∀ x a b : ℝ, a < x → x < b →
      g.IsRoot a → g.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∃ ν : ℝ, 0 < ν ∧
        (∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → ν ≤ μ) ∧
        (∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
          ∀ τ ∈ Set.Icc ν μ,
            (f + C τ * g).natDegree = (f + C μ * g).natDegree) ∧
        ∀ z : ℝ, a < z → z < b → ¬ (f + C ν * g).IsRoot z) :
    CrossOwnedNotOddGaps f g := by
  intro a b x hax hxb ha_root hb_root hgap hnot_odd
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  have hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z :=
    fun z hz₁ hz₂ => (hgap z hz₁ hz₂).1
  have hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z :=
    fun z hz₁ hz₂ => (hgap z hz₁ hz₂).2
  have count_sub_eq_of_same_owner {p q r : ℝ[X]}
      (hpq : NoCommonRoots p q) (hpa : p.IsRoot a) (hpb : p.IsRoot b)
      (hq_no : ∀ z : ℝ, a < z → z < b → ¬ q.IsRoot z)
      (hr_no : ∀ z : ℝ, a < z → z < b → ¬ r.IsRoot z)
      (hrb : ¬ r.IsRoot b) :
      ((r.roots.filter (a < ·)).card : ℤ) - (q.roots.filter (a < ·)).card =
        ((r.roots.filter (b < ·)).card : ℤ) -
          (q.roots.filter (b < ·)).card := by
    have hq_no_Ioc : ∀ z : ℝ, a < z → z ≤ b → ¬ q.IsRoot z := by
      intro z haz hzb
      exact hpq.right_not_isRoot_Icc_of_left_roots hpa hpb hq_no z
        ⟨le_of_lt haz, hzb⟩
    have hr_no_Ioc : ∀ z : ℝ, a < z → z ≤ b → ¬ r.IsRoot z := by
      intro z haz hzb
      by_cases hzb_eq : z = b
      · simpa [hzb_eq] using hrb
      · exact hr_no z haz (lt_of_le_of_ne hzb hzb_eq)
    exact card_roots_filter_gt_sub_eq_of_no_isRoot_Ioc hab
      hr_no_Ioc hq_no_Ioc
  rcases ha_root with hfa | hga
  · rcases hb_root with hfb | hgb
    · obtain ⟨ν, hν_pos, hν_large, hdeg_large, hν_no⟩ :=
        hleft_local x a b hax hxb hfa hfb hgap
      exact False.elim <|
        hsgn.false_of_left_roots_add_left_inv_count_sub_eq_right
          hfg hno hf hg hfa hfb hf_no hg_no hax hxb hax hxb hnot_odd
          hν_pos hν_large hdeg_large
          (count_sub_eq_of_same_owner hno hfa hfb hg_no hν_no
            (hno.symm.rightFamily_not_isRoot_of_right_root hfb))
    · exact Or.inl ⟨hfa, hgb⟩
  · rcases hb_root with hfb | hgb
    · exact Or.inr ⟨hga, hfb⟩
    · obtain ⟨ν, hν_pos, hν_small, hdeg_small, hν_no⟩ :=
        hright_local x a b hax hxb hga hgb hgap
      exact False.elim <|
        hsgn.false_of_right_roots_add_right_small_count_sub_eq_left
          hfg hno hf hg hga hgb hf_no hg_no hax hxb hax hxb hnot_odd
          hν_pos hν_small hdeg_small
          (count_sub_eq_of_same_owner hno.symm hga hgb hf_no hν_no
            (hno.rightFamily_not_isRoot_of_right_root hgb))

/-- Distinct-degree local supplier for the parity-guarded consecutive-root
ownership input.  The local compactness lemmas choose the large/small
parameters, and inequality of endpoint degrees supplies the
positive-parameter degree constancy needed by the local-gap theorem. -/
theorem OppositeLeadingSigns.crossOwnedNotOddGaps_of_natDegree_ne
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree ≠ g.natDegree) :
    CrossOwnedNotOddGaps f g := by
  refine hsgn.crossOwnedNotOddGaps_of_local_no_isRoot_Ioo
    hfg hno hf hg ?_ ?_
  · intro x a b hax hxb hfa hfb hgap
    have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
    have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hax, le_of_lt hxb⟩
    obtain ⟨ν, hν_pos, hν_large, hν_no⟩ :=
      hno.exists_large_add_left_inv_not_isRoot_Icc_of_left_roots
        hab hxIcc hfa hfb (fun z hz₁ hz₂ => (hgap z hz₁ hz₂).2)
    refine ⟨ν, hν_pos, hν_large, ?_, ?_⟩
    · intro μ hμ_pos _ τ hτ
      exact forall_mem_Icc_natDegree_add_C_mul_eq_of_natDegree_ne
        hdeg hμ_pos τ hτ
    · intro z hz₁ hz₂
      exact hν_no z ⟨le_of_lt hz₁, le_of_lt hz₂⟩
  · intro x a b hax hxb hga hgb hgap
    have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
    have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hax, le_of_lt hxb⟩
    obtain ⟨ν, hν_pos, hν_small, hν_no⟩ :=
      hno.exists_small_add_right_not_isRoot_Icc_of_right_roots
        hab hxIcc hga hgb (fun z hz₁ hz₂ => (hgap z hz₁ hz₂).1)
    refine ⟨ν, hν_pos, hν_small, ?_, ?_⟩
    · intro μ hμ_pos _ τ hτ
      exact forall_mem_natDegree_add_C_mul_eq_of_natDegree_ne_of_ne_zero
        (s := Set.Icc ν μ) (κ := μ) hdeg (ne_of_gt hμ_pos)
        (fun σ hσ => ne_of_gt (lt_of_lt_of_le hν_pos hσ.1)) τ hτ
    · intro z hz₁ hz₂
      exact hν_no z ⟨le_of_lt hz₁, le_of_lt hz₂⟩

/-- Equal-degree local supplier for the parity-guarded consecutive-root
ownership input, under explicit crossing-side hypotheses.  The cancellation
parameter `-f.leadingCoeff / g.leadingCoeff` is positive under
`OppositeLeadingSigns f g`.  In an `f`/`f` gap the positive crossing parameters
are assumed to lie above that value; in a `g`/`g` gap they are assumed to lie
below it.  Later analytic work should discharge these directional hypotheses
or replace them with a more natural condition. -/
theorem OppositeLeadingSigns.crossOwnedNotOddGaps_of_natDegree_eq_of_crossing_cancel_sides
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree = g.natDegree)
    (hleft_cancel_lt : ∀ x a b : ℝ, a < x → x < b →
      f.IsRoot a → f.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
        -f.leadingCoeff / g.leadingCoeff < μ)
    (hright_lt_cancel : ∀ x a b : ℝ, a < x → x < b →
      g.IsRoot a → g.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
        μ < -f.leadingCoeff / g.leadingCoeff) :
    CrossOwnedNotOddGaps f g := by
  refine hsgn.crossOwnedNotOddGaps_of_local_no_isRoot_Ioo
    hfg hno hf hg ?_ ?_
  · intro x a b hax hxb hfa hfb hgap
    have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
    have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hax, le_of_lt hxb⟩
    obtain ⟨ν, hν_pos, hν_large, hν_no⟩ :=
      hno.exists_large_add_left_inv_not_isRoot_Icc_of_left_roots
        hab hxIcc hfa hfb (fun z hz₁ hz₂ => (hgap z hz₁ hz₂).2)
    refine ⟨ν, hν_pos, hν_large, ?_, ?_⟩
    · intro μ hμ_pos hμ_root τ hτ
      have hcancel_lt : -f.leadingCoeff / g.leadingCoeff < μ :=
        hleft_cancel_lt x a b hax hxb hfa hfb hgap μ hμ_pos hμ_root
      exact
        forall_mem_Icc_natDegree_add_C_mul_eq_of_natDegree_eq_of_cancel_lt_lower
          (p := f) (q := g) (a := μ) (b := ν) (κ := μ)
          hdeg hsgn.right_ne_zero hcancel_lt hcancel_lt τ hτ
    · intro z hz₁ hz₂
      exact hν_no z ⟨le_of_lt hz₁, le_of_lt hz₂⟩
  · intro x a b hax hxb hga hgb hgap
    have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
    have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hax, le_of_lt hxb⟩
    obtain ⟨ν, hν_pos, hν_small, hν_no⟩ :=
      hno.exists_small_add_right_not_isRoot_Icc_of_right_roots
        hab hxIcc hga hgb (fun z hz₁ hz₂ => (hgap z hz₁ hz₂).1)
    refine ⟨ν, hν_pos, hν_small, ?_, ?_⟩
    · intro μ hμ_pos hμ_root τ hτ
      have hlt_cancel : μ < -f.leadingCoeff / g.leadingCoeff :=
        hright_lt_cancel x a b hax hxb hga hgb hgap μ hμ_pos hμ_root
      exact
        forall_mem_Icc_natDegree_add_C_mul_eq_of_natDegree_eq_of_upper_lt_cancel
          (p := f) (q := g) (a := ν) (b := μ) (κ := μ)
          hdeg hsgn.right_ne_zero hlt_cancel hlt_cancel τ hτ
    · intro z hz₁ hz₂
      exact hν_no z ⟨le_of_lt hz₁, le_of_lt hz₂⟩

/-- Analytic supplier for the parity-guarded consecutive-root ownership input
used by the finite Liu count descent.  This corollary proves the endpoint count
equalities from constant-degree data; later proof work should target
`OppositeLeadingSigns.crossOwnedNotOddGaps_of_endpoint_count_diffs` directly. -/
theorem OppositeLeadingSigns.crossOwnedNotOddGaps_of_parameter_bounds
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) (νL νR : ℝ → ℝ)
    (hνL_pos : ∀ x : ℝ, 0 < νL x)
    (hνL_large : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → μ ≤ νL x)
    (hdegL : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ (νL x),
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hdegL_inv : ∀ x η : ℝ, η ∈ Set.Icc (0 : ℝ) (νL x)⁻¹ →
      (g + C η * f).natDegree = (g + C (0 : ℝ) * f).natDegree)
    (hνR_pos : ∀ x : ℝ, 0 < νR x)
    (hνR_small : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → νR x ≤ μ)
    (hdegR : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc (νR x) μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hdegR_zero : ∀ x η : ℝ, η ∈ Set.Icc (0 : ℝ) (νR x) →
      (f + C η * g).natDegree = (f + C (0 : ℝ) * g).natDegree) :
    CrossOwnedNotOddGaps f g := by
  intro a b x hax hxb ha_root hb_root hgap hnot_odd
  exact hsgn.cross_owner_roots_of_not_odd
    hfg hno hf hg hgap hax hxb ha_root hb_root hnot_odd
    (hνL_pos x) (hνL_large x) (hdegL x) (hdegL_inv x)
    (hνR_pos x) (hνR_small x) (hdegR x) (hdegR_zero x)

end LiuOppositeSigns
end RealRooted
