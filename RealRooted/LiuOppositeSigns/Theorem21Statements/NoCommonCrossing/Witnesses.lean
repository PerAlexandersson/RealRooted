import RealRooted.CommonInterleaver.RightPencil
import RealRooted.CommonInterleaver.SuccDegreeLowDegree
import RealRooted.LiuOppositeSigns
import RealRooted.LiuOppositeSigns.NoCommonRoots
import RealRooted.PositiveParameterLocalLowerCount
import RealRooted.RootContinuity
import RealRooted.RootCountLocalConstancy

/-!
# Crossing witnesses for Liu's no-common-root argument

This module contains the affine-pencil root witnesses, root-count transport,
and same-owner endpoint contradictions used by the cross-owned-gap layer.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

theorem RootCountCompatible.exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots
    {p q : ℝ[X]} (hcount : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hp : p.Splits) (hq : q.Splits)
    (hp_pos : 0 < p.leadingCoeff) (hq_pos : 0 < q.leadingCoeff)
    {a b y μ : ℝ} (hay : a < y) (hyb : y < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hy : q.IsRoot y)
    (hμ : 0 < μ) (hy_neg : y < 0)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (hqa : ¬ q.IsRoot a) (hqb : ¬ q.IsRoot b)
    (heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card) :
    ∃ c₁ c₂ : ℝ,
      a < c₁ ∧ c₁ < y ∧ y < c₂ ∧ c₂ < b ∧
        (X * p - C μ * q).IsRoot c₁ ∧ (X * p - C μ * q).IsRoot c₂ := by
  have hab : a < b := lt_trans hay hyb
  have htwo := two_le_card_roots_filter_Ioo_of_even_of_isRoot
    hq_ne hy hay hyb heven
  have hodd_a :=
    hcount.odd_card_roots_gt_add_of_left_no_isRoot_Ioo
      hp_ne hq_ne hab hp_no hqb htwo
  have hp_count_eq :
      (p.roots.filter (a < ·)).card = (p.roots.filter (y < ·)).card := by
    refine card_filter_lt_eq_of_no_mem_Ioc p.roots (le_of_lt hay) ?_
    intro r hr
    by_cases hra : r ≤ a
    · exact Or.inl hra
    · right
      by_contra hyr
      have har : a < r := lt_of_not_ge hra
      have hry : r ≤ y := le_of_not_gt hyr
      exact hp_no r har (lt_of_le_of_lt hry hyb)
        ((Polynomial.mem_roots hp_ne).mp hr)
  have hodd_y :
      Odd ((p.roots.filter (y < ·)).card +
        (q.roots.filter (a < ·)).card) := by
    simpa [hp_count_eq] using hodd_a
  have hp_not_y : ¬ p.IsRoot y := hp_no y hay hyb
  have hp_y_q_a_neg : p.eval y * q.eval a < 0 :=
    hp.eval_mul_eval_neg_of_odd_card_roots_gt_add
      hq hp_pos hq_pos hp_not_y hqa hodd_y
  have hq_a_p_y_neg : q.eval a * p.eval y < 0 := by simpa [mul_comm] using hp_y_q_a_neg
  exact exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots_left_sign
    hq_ne hq hay hyb ha hb hy hμ hy_neg heven hqb hq_a_p_y_neg

/-- Positive-split, no-common-root corollary for the even right-polynomial root
case.  The no-common-root hypothesis supplies the endpoint nonroot facts for
`q`, and nonnegative coefficients on the left polynomial force the interior
right-polynomial root `y` to be negative because it lies left of the right
left-polynomial endpoint `b`. -/
theorem
    PositiveSplitRootCountPair.exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b y μ : ℝ} (hay : a < y) (hyb : y < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hy : q.IsRoot y)
    (hμ : 0 < μ)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card) :
    ∃ c₁ c₂ : ℝ,
      a < c₁ ∧ c₁ < y ∧ y < c₂ ∧ c₂ < b ∧
        (X * p - C μ * q).IsRoot c₁ ∧ (X * p - C μ * q).IsRoot c₂ := by
  have hy_neg : y < 0 :=
    lt_zero_of_lt_isRoot_of_hasNonnegCoeffs hp_nonneg hpair.left_pos.ne_zero hb hyb
  exact hpair.count.exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots
    hpair.left_pos.ne_zero hpair.right_pos.ne_zero
    hpair.left_splits hpair.right_splits hpair.left_pos hpair.right_pos
    hay hyb ha hb hy hμ hy_neg hp_no (hno a ha) (hno b hb) heven

/-- If the endpoints of `[a, b]` are roots of `f`, the polynomials have no
common roots, and `g` is root-free in `(a, b)`, then all sufficiently small
right-family perturbations `g + C μ * f` are root-free on `[a, b]`. -/
theorem NoCommonRoots.exists_forall_abs_lt_not_isRoot_add_right_Icc_of_left_roots
    {f g : ℝ[X]} (h : NoCommonRoots f g) {a b : ℝ}
    (hab : a ≤ b) (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ μ : ℝ, |μ| < ε → ∀ z ∈ Set.Icc a b, ¬ (g + C μ * f).IsRoot z :=
  exists_forall_abs_lt_not_isRoot_add_right_of_left_not_isRoot_Icc hab
    (h.right_not_isRoot_Icc_of_left_roots hfa hfb hg_no)

/-- Same-`f` gap parameter choice for the Liu odd-interval argument.  If the
endpoints of `[a, b]` are roots of `f` and `g` is root-free in the open gap,
then there is a large positive parameter `ν` which bounds all positive crossings
of `f + C μ * g` at a sample point in the interval, while the reciprocal family
`g + C ν⁻¹ * f` is root-free on the whole closed gap. -/
theorem NoCommonRoots.exists_large_add_left_inv_not_isRoot_Icc_of_left_roots
    {f g : ℝ[X]} (h : NoCommonRoots f g) {a b x : ℝ}
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b)
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z) :
    ∃ ν : ℝ, 0 < ν ∧
      (∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → μ ≤ ν) ∧
      ∀ z ∈ Set.Icc a b, ¬ (g + C ν⁻¹ * f).IsRoot z := by
  obtain ⟨ν, hν_pos, hν_bound, hν_no⟩ :=
    exists_large_add_left_inv_not_isRoot_Icc_of_right_not_isRoot_Icc hab
      (h.right_not_isRoot_Icc_of_left_roots hfa hfb hg_no)
  refine ⟨ν, hν_pos, ?_, hν_no⟩
  intro μ hμ_pos hμ_root
  exact le_of_lt (by simpa [abs_of_pos hμ_pos] using hν_bound μ x hx hμ_root)

/-- Same-`g` gap parameter choice for the Liu odd-interval argument.  If the
endpoints of `[a, b]` are roots of `g` and `f` is root-free in the open gap,
then there is a small positive parameter `ν` which is below every positive
crossing parameter at a sample point in the interval, while `f + C ν * g` is
root-free on the whole closed gap. -/
theorem NoCommonRoots.exists_small_add_right_not_isRoot_Icc_of_right_roots
    {f g : ℝ[X]} (h : NoCommonRoots f g) {a b x : ℝ}
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b)
    (hga : g.IsRoot a) (hgb : g.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z) :
    ∃ ν : ℝ, 0 < ν ∧
      (∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x → ν ≤ μ) ∧
      ∀ z ∈ Set.Icc a b, ¬ (f + C ν * g).IsRoot z := by
  obtain ⟨ν, hν_pos, hν_bound, hν_no⟩ :=
    exists_small_add_right_not_isRoot_Icc_of_left_not_isRoot_Icc (g := g) hab
      (h.symm.right_not_isRoot_Icc_of_left_roots hga hgb hf_no)
  refine ⟨ν, hν_pos, ?_, hν_no⟩
  intro μ hμ_pos hμ_root
  exact le_of_lt (by simpa [abs_of_pos hμ_pos] using hν_bound μ x hx hμ_root)

/-- For splitting polynomials with opposite leading signs, odd upper
root-count difference at a common non-root is equivalent to the absence of a
positive right-pencil member through that threshold. -/
theorem OppositeLeadingSigns.odd_intCard_roots_gt_sub_iff_not_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  have hfx_eval : f.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero f x).mp hxf
  have hgx_eval : g.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero g x).mp hxg
  rw [hsgn.odd_intCard_roots_gt_sub_iff_eval_pos_iff hf hg hxf hxg]
  exact (not_exists_pos_isRoot_add_right_iff_eval_pos_iff hfx_eval hgx_eval).symm

/-- Positive-parameter no-crossing form of
`OppositeLeadingSigns.odd_intCard_roots_gt_sub_iff_not_exists_pos_isRoot_add_right`.
This is the shape consumed by local root-count constancy on positive parameter
intervals. -/
theorem OppositeLeadingSigns.odd_intCard_roots_gt_sub_iff_forall_pos_not_isRoot
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot x) := by
  rw [hsgn.odd_intCard_roots_gt_sub_iff_not_exists_pos_isRoot_add_right
    hf hg hxf hxg]
  simp [not_exists]

/-- If a finite open interval contains no roots of either endpoint polynomial,
then oddness at one sample point gives positive-parameter no-crossing at any
other sample point in that interval. -/
theorem OppositeLeadingSigns.forall_pos_not_isRoot_of_odd_roots_gt_sub_of_no_isRoot_Ioo
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hodd : Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot y := by
  have hodd_y : Odd (((f.roots.filter (y < ·)).card : ℤ) -
      (g.roots.filter (y < ·)).card) :=
    (odd_card_roots_filter_gt_sub_iff_of_no_isRoot_Ioo
      hf_no hg_no hax hxb hay hyb).mp hodd
  exact
    (hsgn.odd_intCard_roots_gt_sub_iff_forall_pos_not_isRoot
      hf hg (hf_no y hay hyb) (hg_no y hay hyb)).mp hodd_y

/-- If a finite open interval contains no roots of either endpoint polynomial,
then oddness at one sample point forces same-sign endpoint evaluations at any
other sample point in that interval. -/
theorem OppositeLeadingSigns.eval_mul_pos_of_odd_roots_gt_sub_Ioo
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hodd : Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    0 < f.eval y * g.eval y := by
  have hno_pos :=
    hsgn.forall_pos_not_isRoot_of_odd_roots_gt_sub_of_no_isRoot_Ioo
      hf hg hf_no hg_no hax hxb hay hyb hodd
  exact eval_mul_pos_of_no_pos_rightFamily_isRoot
    (hf_no y hay hyb) (hg_no y hay hyb) hno_pos

/-- If a finite open interval contains no roots of either endpoint polynomial,
then oddness at one sample point rules out closed-segment roots at any other
sample point in that interval. -/
theorem OppositeLeadingSigns.closedSegment_not_isRoot_of_odd_roots_gt_sub_Ioo
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y β : ℝ}
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hodd : Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ¬ (C (1 - β) * f + C β * g).IsRoot y := by
  exact closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1
    (hsgn.eval_mul_pos_of_odd_roots_gt_sub_Ioo
      hf hg hf_no hg_no hax hxb hay hyb hodd)

/-- On a positive parameter interval with constant degree and a fixed
threshold root-free for every positive member, the right-family strict-upper
count is constant between the interval endpoints. -/
theorem rightFamily_card_roots_gt_eq_of_forall_pos_not_isRoot
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    {x μ₀ μ₁ : ℝ}
    (hno_pos : ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot x)
    (hμ₀_pos : 0 < μ₀) (hμ₀μ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  have hpos_interval : ∀ μ ∈ Set.Icc μ₀ μ₁, 0 < μ :=
    fun _ hμ => lt_of_lt_of_le hμ₀_pos hμ.1
  have hsplit : ∀ μ ∈ Set.Icc μ₀ μ₁, (f + C μ * g).Splits :=
    fun μ hμ => (hfg.isRealRooted_add_right (hpos_interval μ hμ)).2
  refine rightFamily_card_roots_gt_eq_of_local_lower_counts
    (f := f) (g := g) (μ₀ := μ₀) (μ₁ := μ₁) (x := x)
    hμ₀μ₁ hdeg ?_ ?_ ?_
  · intro μ hμ
    exact hsplit μ hμ
  · intro μ hμ
    exact hno_pos μ (hpos_interval μ hμ)
  · intro μ hμ ρ hρ
    exact positiveParameter_local_lower_count hsplit hdeg hμ hρ

/-- On a positive parameter interval with constant degree, odd opposite-leading
strict-upper root-count difference at a common non-root makes the right-family
strict-upper count locally constant between the interval endpoints. -/
theorem OppositeLeadingSigns.rightFamily_card_roots_gt_eq_of_odd_intCard_roots_gt_sub
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hf : f.Splits) (hg : g.Splits)
    {x μ₀ μ₁ : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hodd : Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hμ₀_pos : 0 < μ₀) (hμ₀μ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  have hno_pos : ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot x :=
    (hsgn.odd_intCard_roots_gt_sub_iff_forall_pos_not_isRoot
      hf hg hxf hxg).mp hodd
  exact rightFamily_card_roots_gt_eq_of_forall_pos_not_isRoot
    hfg hno_pos hμ₀_pos hμ₀μ₁ hdeg

/-- Open-interval sample-point form of
`OppositeLeadingSigns.rightFamily_card_roots_gt_eq_of_odd_intCard_roots_gt_sub`.
Oddness at one point in a root-free open interval gives right-family strict
upper-count constancy at any other point in that interval. -/
theorem OppositeLeadingSigns.rightFamily_card_roots_gt_eq_of_odd_roots_gt_sub_Ioo
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hf : f.Splits) (hg : g.Splits)
    {a b x y μ₀ μ₁ : ℝ}
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hodd : Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hμ₀_pos : 0 < μ₀) (hμ₀μ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree) :
    ((f + C μ₀ * g).roots.filter (y < ·)).card =
      ((f + C μ₁ * g).roots.filter (y < ·)).card := by
  have hno_pos :=
    hsgn.forall_pos_not_isRoot_of_odd_roots_gt_sub_of_no_isRoot_Ioo
      hf hg hf_no hg_no hax hxb hay hyb hodd
  exact rightFamily_card_roots_gt_eq_of_forall_pos_not_isRoot
    hfg hno_pos hμ₀_pos hμ₀μ₁ hdeg

private theorem rightFamily_count_drop_two_iff_of_forall_pos_not_isRoot
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    {a b μ₀ μ₁ : ℝ}
    (ha_no : ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot a)
    (hb_no : ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot b)
    (hμ₀_pos : 0 < μ₀) (hμ₀μ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree) :
    (((f + C μ₀ * g).roots.filter (b < ·)).card + 2 ≤
      ((f + C μ₀ * g).roots.filter (a < ·)).card) ↔
    (((f + C μ₁ * g).roots.filter (b < ·)).card + 2 ≤
      ((f + C μ₁ * g).roots.filter (a < ·)).card) := by
  have ha_eq :=
    rightFamily_card_roots_gt_eq_of_forall_pos_not_isRoot
      hfg ha_no hμ₀_pos hμ₀μ₁ hdeg
  have hb_eq :=
    rightFamily_card_roots_gt_eq_of_forall_pos_not_isRoot
      hfg hb_no hμ₀_pos hμ₀μ₁ hdeg
  constructor
  · intro hdrop
    simpa [← ha_eq, ← hb_eq] using hdrop
  · intro hdrop
    simpa [ha_eq, hb_eq] using hdrop

/-- Contrapositive crossing form of
`OppositeLeadingSigns.odd_intCard_roots_gt_sub_iff_not_exists_pos_isRoot_add_right`. -/
theorem OppositeLeadingSigns.not_odd_intCard_roots_gt_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  simpa using
    (not_congr
      (hsgn.odd_intCard_roots_gt_sub_iff_not_exists_pos_isRoot_add_right
        hf hg hxf hxg))

/-- In a no-common positive-combination family with opposite leading signs,
failure of odd upper root-count difference at a common non-root gives the
unique positive right-pencil crossing through that threshold. -/
theorem OppositeLeadingSigns.exists_unique_pos_crossing_add_right_of_not_odd_intCard_roots_gt_sub
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x ∧
      μ = -f.eval x / g.eval x ∧
      (f + C μ * g).derivative.eval x ≠ 0 ∧
      (∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot x → ν = μ) := by
  have hcross :=
    (hsgn.not_odd_intCard_roots_gt_sub_iff_exists_pos_isRoot_add_right
      hf hg hxf hxg).mp hnot_odd
  have hfx_eval : f.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero f x).mp hxf
  have hsign : f.eval x * g.eval x < 0 :=
    (exists_pos_isRoot_add_right_iff_eval_mul_neg hfx_eval).mp hcross
  exact hfg.exists_unique_pos_parameter_crossing_add_right_of_sign hno hsign

/-- Open-interval sample-point form of
`OppositeLeadingSigns.exists_unique_pos_crossing_add_right_of_not_odd_intCard_roots_gt_sub`.
On a root-free interval, failure of odd strict-upper root-count difference at
one sample point gives the unique positive right-family crossing at any other
sample point in the interval. -/
theorem OppositeLeadingSigns.exists_unique_pos_crossing_add_right_of_not_odd_roots_gt_sub_Ioo
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot y ∧
      μ = -f.eval y / g.eval y ∧
      (f + C μ * g).derivative.eval y ≠ 0 ∧
      (∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot y → ν = μ) := by
  have hnot_odd_y : ¬ Odd (((f.roots.filter (y < ·)).card : ℤ) -
      (g.roots.filter (y < ·)).card) :=
    mt ((odd_card_roots_filter_gt_sub_iff_of_no_isRoot_Ioo
      hf_no hg_no hax hxb hay hyb).mpr) hnot_odd
  exact hsgn.exists_unique_pos_crossing_add_right_of_not_odd_intCard_roots_gt_sub
    hfg hno hf hg (hf_no y hay hyb) (hg_no y hay hyb) hnot_odd_y

/-- Endpoint-shaped `f`/`f` interval package for Liu's odd-indexed interval
argument.  If both finite endpoints are roots of `f`, then a `not Odd`
strict-upper count sample gives the unique positive right-family crossing in
the interval together with same-sign endpoint values for that crossing
polynomial. -/
theorem OppositeLeadingSigns.exists_unique_pos_crossing_add_right_Ioo_left_roots_endpoint_sign
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot y ∧
      μ = -f.eval y / g.eval y ∧
      (f + C μ * g).derivative.eval y ≠ 0 ∧
      (∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot y → ν = μ) ∧
      0 < (f + C μ * g).eval a * (f + C μ * g).eval b := by
  obtain ⟨μ, hμ_pos, hμ_root, hμ_eq, hμ_der, hμ_unique⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_of_not_odd_roots_gt_sub_Ioo
      hfg hno hf hg hf_no hg_no hax hxb hay hyb hnot_odd
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  have hg_no_Icc : ∀ z ∈ Set.Icc a b, ¬ g.IsRoot z :=
    hno.right_not_isRoot_Icc_of_left_roots hfa hfb hg_no
  refine ⟨μ, hμ_pos, hμ_root, hμ_eq, hμ_der, hμ_unique, ?_⟩
  exact rightFamily_eval_endpoint_mul_pos_of_left_roots_of_right_no_isRoot_Icc
    hab hfa hfb hg_no_Icc hμ_pos

/-- Same-owner `f`/`f` local parity package for Liu's odd-indexed interval
argument.  Under the endpoint-shaped hypotheses, the unique positive
right-family crossing polynomial has an even number of roots in `(a, b)`. -/
theorem OppositeLeadingSigns.exists_unique_pos_crossing_add_right_Ioo_left_roots_even_roots
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot y ∧
      μ = -f.eval y / g.eval y ∧
      (f + C μ * g).derivative.eval y ≠ 0 ∧
      (∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot y → ν = μ) ∧
      Even ((f + C μ * g).roots.filter (fun r => a < r ∧ r < b)).card := by
  obtain ⟨μ, hμ_pos, hμ_root, hμ_eq, hμ_der, hμ_unique, hendpoint⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_Ioo_left_roots_endpoint_sign
      hfg hno hf hg hfa hfb hf_no hg_no hax hxb hay hyb hnot_odd
  have hq_rr : (f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits :=
    hfg.isRealRooted_add_right hμ_pos
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  have heven := even_card_roots_filter_Ioo_of_eval_mul_pos
    hq_rr.1 hq_rr.2 hab hendpoint
  exact ⟨μ, hμ_pos, hμ_root, hμ_eq, hμ_der, hμ_unique, heven⟩

/-- Same-owner `f`/`f` local lower-bound package for Liu's odd-indexed
interval argument.  Under the endpoint-shaped hypotheses, the unique positive
right-family crossing polynomial has at least two roots in `(a, b)`, counted
with multiplicity. -/
theorem OppositeLeadingSigns.exists_unique_pos_crossing_add_right_Ioo_left_roots_two_roots
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot y ∧
      μ = -f.eval y / g.eval y ∧
      (f + C μ * g).derivative.eval y ≠ 0 ∧
      (∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot y → ν = μ) ∧
      2 ≤ ((f + C μ * g).roots.filter (fun r => a < r ∧ r < b)).card := by
  obtain ⟨μ, hμ_pos, hμ_root, hμ_eq, hμ_der, hμ_unique, heven⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_Ioo_left_roots_even_roots
      hfg hno hf hg hfa hfb hf_no hg_no hax hxb hay hyb hnot_odd
  have hq_ne : (f + C μ * g) ≠ 0 :=
    (hfg.isRealRooted_add_right hμ_pos).1
  have htwo := two_le_card_roots_filter_Ioo_of_even_of_isRoot
    hq_ne hμ_root hay hyb heven
  exact ⟨μ, hμ_pos, hμ_root, hμ_eq, hμ_der, hμ_unique, htwo⟩

private theorem crossing_count_drop_of_endpoint_sign
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    {a b y μ : ℝ}
    (hμ_pos : 0 < μ) (hμ_root : (f + C μ * g).IsRoot y)
    (hμ_eq : μ = -f.eval y / g.eval y)
    (hμ_der : (f + C μ * g).derivative.eval y ≠ 0)
    (hμ_unique : ∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot y → ν = μ)
    (hay : a < y) (hyb : y < b) (hab : a ≤ b)
    (hendpoint : 0 < (f + C μ * g).eval a * (f + C μ * g).eval b)
    (hnot_b : ¬ (f + C μ * g).IsRoot b) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot y ∧
      μ = -f.eval y / g.eval y ∧
      (f + C μ * g).derivative.eval y ≠ 0 ∧
      (∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot y → ν = μ) ∧
      ((f + C μ * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C μ * g).roots.filter (a < ·)).card := by
  have hq_rr : (f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits :=
    hfg.isRealRooted_add_right hμ_pos
  have heven := even_card_roots_filter_Ioo_of_eval_mul_pos
    hq_rr.1 hq_rr.2 hab hendpoint
  have htwo := two_le_card_roots_filter_Ioo_of_even_of_isRoot
    hq_rr.1 hμ_root hay hyb heven
  have hdrop := card_roots_filter_gt_add_two_le_of_two_le_card_filter_Ioo
    hq_rr.1 hab hnot_b htwo
  exact ⟨μ, hμ_pos, hμ_root, hμ_eq, hμ_der, hμ_unique, hdrop⟩

/-- Same-owner `f`/`f` local count-drop package for Liu's odd-indexed
interval argument.  Under the endpoint-shaped hypotheses, the unique positive
right-family crossing polynomial has strict-upper root count drop at least two
from `a` to `b`. -/
theorem OppositeLeadingSigns.exists_unique_pos_crossing_add_right_Ioo_left_roots_gt_drop_two
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot y ∧
      μ = -f.eval y / g.eval y ∧
      (f + C μ * g).derivative.eval y ≠ 0 ∧
      (∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot y → ν = μ) ∧
      ((f + C μ * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C μ * g).roots.filter (a < ·)).card := by
  obtain ⟨μ, hμ_pos, hμ_root, hμ_eq, hμ_der, hμ_unique, hendpoint⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_Ioo_left_roots_endpoint_sign
      hfg hno hf hg hfa hfb hf_no hg_no hax hxb hay hyb hnot_odd
  have hq_not_b : ¬ (f + C μ * g).IsRoot b :=
    hno.rightFamily_not_isRoot_of_left_root (ne_of_gt hμ_pos) hfb
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  exact crossing_count_drop_of_endpoint_sign hfg hμ_pos hμ_root hμ_eq hμ_der
    hμ_unique hay hyb hab hendpoint hq_not_b

/-- Same-owner `f`/`f` count-drop obstruction for Liu's odd-indexed interval
argument.  A `not Odd` sample in such an interval gives a unique positive
crossing parameter, but exposes only the positive crossing and the transported
count-drop data needed by the endpoint-ownership argument. -/
theorem OppositeLeadingSigns.exists_pos_crossing_add_right_Ioo_left_roots_gt_drop_two_le
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot y ∧
      ((f + C μ * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C μ * g).roots.filter (a < ·)).card ∧
      (∀ ν : ℝ, μ ≤ ν →
        (∀ τ ∈ Set.Icc μ ν,
          (f + C τ * g).natDegree = (f + C μ * g).natDegree) →
        ((f + C ν * g).roots.filter (b < ·)).card + 2 ≤
          ((f + C ν * g).roots.filter (a < ·)).card) := by
  obtain ⟨μ, hμ_pos, hμ_root, _hμ_eq, _hμ_der, _hμ_unique, hdrop⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_Ioo_left_roots_gt_drop_two
      hfg hno hf hg hfa hfb hf_no hg_no hax hxb hay hyb hnot_odd
  refine ⟨μ, hμ_pos, hμ_root, hdrop, ?_⟩
  intro ν hμν hdeg
  have ha_no : ∀ τ : ℝ, 0 < τ → ¬ (f + C τ * g).IsRoot a :=
    fun τ hτ => hno.rightFamily_not_isRoot_of_left_root (ne_of_gt hτ) hfa
  have hb_no : ∀ τ : ℝ, 0 < τ → ¬ (f + C τ * g).IsRoot b :=
    fun τ hτ => hno.rightFamily_not_isRoot_of_left_root (ne_of_gt hτ) hfb
  exact (rightFamily_count_drop_two_iff_of_forall_pos_not_isRoot
    hfg ha_no hb_no hμ_pos hμν hdeg).mp hdrop

theorem false_of_add_right_count_drop_of_count_sub_eq_no_isRoot_Icc
    {f g q : ℝ[X]} {a b ν : ℝ} (hab : a ≤ b)
    (hq_no : ∀ z ∈ Set.Icc a b, ¬ q.IsRoot z)
    (hdrop :
      ((f + C ν * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C ν * g).roots.filter (a < ·)).card)
    (hsub : (((f + C ν * g).roots.filter (a < ·)).card : ℤ) -
        (q.roots.filter (a < ·)).card =
      (((f + C ν * g).roots.filter (b < ·)).card : ℤ) -
        (q.roots.filter (b < ·)).card) :
    False := by
  have hq_no_Ioc : ∀ z : ℝ, a < z → z ≤ b → ¬ q.IsRoot z := by
    intro z haz hzb
    exact hq_no z ⟨le_of_lt haz, hzb⟩
  exact
    (not_card_roots_filter_gt_add_two_le_of_sub_eq_no_isRoot_Ioc
      (p := f + C ν * g) (q := q) hab hq_no_Ioc hsub) hdrop

/-- Same-owner `g`/`g` local count-drop package for Liu's odd-indexed
interval argument.  Under the endpoint-shaped hypotheses, the unique positive
right-family crossing polynomial has strict-upper root count drop at least two
from `a` to `b`. -/
theorem OppositeLeadingSigns.exists_unique_pos_crossing_add_right_Ioo_right_roots_gt_drop_two
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hga : g.IsRoot a) (hgb : g.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot y ∧
      μ = -f.eval y / g.eval y ∧
      (f + C μ * g).derivative.eval y ≠ 0 ∧
      (∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot y → ν = μ) ∧
      ((f + C μ * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C μ * g).roots.filter (a < ·)).card := by
  obtain ⟨μ, hμ_pos, hμ_root, hμ_eq, hμ_der, hμ_unique⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_of_not_odd_roots_gt_sub_Ioo
      hfg hno hf hg hf_no hg_no hax hxb hay hyb hnot_odd
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  have hf_no_Icc : ∀ z ∈ Set.Icc a b, ¬ f.IsRoot z :=
    hno.symm.right_not_isRoot_Icc_of_left_roots hga hgb hf_no
  have hf_endpoint : 0 < f.eval a * f.eval b :=
    eval_mul_pos_of_forall_not_isRoot_Icc hab hf_no_Icc
  have hga_eval : g.eval a = 0 := by simpa [Polynomial.IsRoot.def] using hga
  have hgb_eval : g.eval b = 0 := by simpa [Polynomial.IsRoot.def] using hgb
  have hendpoint :
      0 < (f + C μ * g).eval a * (f + C μ * g).eval b := by
    simpa [eval_add, eval_mul, eval_C, hga_eval, hgb_eval] using hf_endpoint
  have hq_not_b : ¬ (f + C μ * g).IsRoot b :=
    hno.rightFamily_not_isRoot_of_right_root hgb
  exact crossing_count_drop_of_endpoint_sign hfg hμ_pos hμ_root hμ_eq hμ_der
    hμ_unique hay hyb hab hendpoint hq_not_b

/-- Same-owner `g`/`g` count-drop obstruction for Liu's odd-indexed interval
argument.  A `not Odd` sample in such an interval gives a unique positive
crossing parameter, but exposes only the positive crossing and the transported
count-drop data needed by the endpoint-ownership argument. -/
theorem OppositeLeadingSigns.exists_pos_crossing_add_right_Ioo_right_roots_gt_drop_two_le
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y : ℝ}
    (hga : g.IsRoot a) (hgb : g.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot y ∧
      ((f + C μ * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C μ * g).roots.filter (a < ·)).card ∧
      (∀ ν : ℝ, μ ≤ ν →
        (∀ τ ∈ Set.Icc μ ν,
          (f + C τ * g).natDegree = (f + C μ * g).natDegree) →
        ((f + C ν * g).roots.filter (b < ·)).card + 2 ≤
          ((f + C ν * g).roots.filter (a < ·)).card) := by
  obtain ⟨μ, hμ_pos, hμ_root, _hμ_eq, _hμ_der, _hμ_unique, hdrop⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_Ioo_right_roots_gt_drop_two
      hfg hno hf hg hga hgb hf_no hg_no hax hxb hay hyb hnot_odd
  refine ⟨μ, hμ_pos, hμ_root, hdrop, ?_⟩
  intro ν hμν hdeg
  have ha_no : ∀ τ : ℝ, 0 < τ → ¬ (f + C τ * g).IsRoot a :=
    fun _ _ => hno.rightFamily_not_isRoot_of_right_root hga
  have hb_no : ∀ τ : ℝ, 0 < τ → ¬ (f + C τ * g).IsRoot b :=
    fun _ _ => hno.rightFamily_not_isRoot_of_right_root hgb
  exact (rightFamily_count_drop_two_iff_of_forall_pos_not_isRoot
    hfg ha_no hb_no hμ_pos hμν hdeg).mp hdrop

/-- Endpoint-shaped `f`/`f` contradiction for Liu's odd-indexed interval
argument.  If the transported right-family count drop reaches a parameter
whose endpoint strict-upper count difference against `g` is stable, then
same-owner `f`-endpoints contradict the fact that `g` has no roots in
`(a, b]`. -/
private theorem OppositeLeadingSigns.false_of_left_roots_add_right_count_sub_eq_right
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y ν : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hν_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y → μ ≤ ν)
    (hdeg_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y →
      ∀ τ ∈ Set.Icc μ ν,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hsub_eq : (((f + C ν * g).roots.filter (a < ·)).card : ℤ) -
        (g.roots.filter (a < ·)).card =
      (((f + C ν * g).roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card) :
    False := by
  obtain ⟨μ, hμ_pos, hμ_root, _hdrop, hdrop_le⟩ :=
    hsgn.exists_pos_crossing_add_right_Ioo_left_roots_gt_drop_two_le
      hfg hno hf hg hfa hfb hf_no hg_no hax hxb hay hyb hnot_odd
  have hdropν :
      ((f + C ν * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C ν * g).roots.filter (a < ·)).card :=
    hdrop_le ν (hν_large μ hμ_pos hμ_root) (hdeg_large μ hμ_pos hμ_root)
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  have hg_no_Icc : ∀ z ∈ Set.Icc a b, ¬ g.IsRoot z :=
    hno.right_not_isRoot_Icc_of_left_roots hfa hfb hg_no
  exact false_of_add_right_count_drop_of_count_sub_eq_no_isRoot_Icc
    hab hg_no_Icc hdropν hsub_eq

/-- Endpoint-shaped `f`/`f` contradiction for Liu's odd-indexed interval
argument.  If the transported right-family count drop reaches a parameter
whose endpoint strict-upper counts agree with those of `g`, then same-owner
`f`-endpoints contradict the fact that `g` has no roots in `(a, b]`. -/
theorem OppositeLeadingSigns.false_of_left_roots_add_right_count_eq_right
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y ν : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hν_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y → μ ≤ ν)
    (hdeg_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y →
      ∀ τ ∈ Set.Icc μ ν,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (ha_eq : ((f + C ν * g).roots.filter (a < ·)).card =
      (g.roots.filter (a < ·)).card)
    (hb_eq : ((f + C ν * g).roots.filter (b < ·)).card =
      (g.roots.filter (b < ·)).card) :
    False := by
  exact hsgn.false_of_left_roots_add_right_count_sub_eq_right
    hfg hno hf hg hfa hfb hf_no hg_no hax hxb hay hyb hnot_odd
    hν_large hdeg_large (by rw [ha_eq, hb_eq]; simp)

/-- Endpoint-shaped `f`/`f` contradiction using the reciprocal small
right-family.  This is the large-parameter form of
`OppositeLeadingSigns.false_of_left_roots_add_right_count_sub_eq_right`: the
endpoint count-difference stability is supplied for `g + C ν⁻¹ * f`, then
transferred to `f + C ν * g` by reciprocal scaling. -/
theorem OppositeLeadingSigns.false_of_left_roots_add_left_inv_count_sub_eq_right
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y ν : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hν_pos : 0 < ν)
    (hν_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y → μ ≤ ν)
    (hdeg_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y →
      ∀ τ ∈ Set.Icc μ ν,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hinv_sub_eq : (((g + C ν⁻¹ * f).roots.filter (a < ·)).card : ℤ) -
        (g.roots.filter (a < ·)).card =
      (((g + C ν⁻¹ * f).roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card) :
    False := by
  have hν_ne : ν ≠ 0 := ne_of_gt hν_pos
  have ha_eq : ((f + C ν * g).roots.filter (a < ·)).card =
      ((g + C ν⁻¹ * f).roots.filter (a < ·)).card :=
    add_right_roots_gt_card_eq_add_left_inv
      (f := f) (g := g) (μ := ν) (x := a) hν_ne
  have hb_eq : ((f + C ν * g).roots.filter (b < ·)).card =
      ((g + C ν⁻¹ * f).roots.filter (b < ·)).card :=
    add_right_roots_gt_card_eq_add_left_inv
      (f := f) (g := g) (μ := ν) (x := b) hν_ne
  exact hsgn.false_of_left_roots_add_right_count_sub_eq_right
    hfg hno hf hg hfa hfb hf_no hg_no hax hxb hay hyb hnot_odd
    hν_large hdeg_large (by rw [ha_eq, hb_eq]; exact hinv_sub_eq)

/-- Endpoint-shaped `f`/`f` contradiction using the reciprocal small
right-family.  This is the large-parameter form of
`OppositeLeadingSigns.false_of_left_roots_add_right_count_eq_right`: the
endpoint count equalities are supplied for `g + C ν⁻¹ * f`, then transferred
to `f + C ν * g` by reciprocal scaling. -/
theorem OppositeLeadingSigns.false_of_left_roots_add_left_inv_count_eq_right
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y ν : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hν_pos : 0 < ν)
    (hν_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y → μ ≤ ν)
    (hdeg_large : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y →
      ∀ τ ∈ Set.Icc μ ν,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (ha_inv_eq : ((g + C ν⁻¹ * f).roots.filter (a < ·)).card =
      (g.roots.filter (a < ·)).card)
    (hb_inv_eq : ((g + C ν⁻¹ * f).roots.filter (b < ·)).card =
      (g.roots.filter (b < ·)).card) :
    False := by
  exact hsgn.false_of_left_roots_add_left_inv_count_sub_eq_right
    hfg hno hf hg hfa hfb hf_no hg_no hax hxb hay hyb hnot_odd
    hν_pos hν_large hdeg_large (by rw [ha_inv_eq, hb_inv_eq]; simp)

/-- Endpoint-shaped `g`/`g` contradiction using a small positive right-family
parameter.  If the transported count drop reaches a small parameter whose
endpoint strict-upper count difference against `f` is stable, then same-owner
`g`-endpoints contradict the fact that `f` has no roots in `(a, b]`. -/
theorem OppositeLeadingSigns.false_of_right_roots_add_right_small_count_sub_eq_left
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y ν : ℝ}
    (hga : g.IsRoot a) (hgb : g.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hν_pos : 0 < ν)
    (hν_small : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y → ν ≤ μ)
    (hdeg_small : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y →
      ∀ τ ∈ Set.Icc ν μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hsub_eq : (((f + C ν * g).roots.filter (a < ·)).card : ℤ) -
        (f.roots.filter (a < ·)).card =
      (((f + C ν * g).roots.filter (b < ·)).card : ℤ) -
        (f.roots.filter (b < ·)).card) :
    False := by
  obtain ⟨μ, hμ_pos, hμ_root, _hμ_eq, _hμ_der, _hμ_unique, hdrop⟩ :=
    hsgn.exists_unique_pos_crossing_add_right_Ioo_right_roots_gt_drop_two
      hfg hno hf hg hga hgb hf_no hg_no hax hxb hay hyb hnot_odd
  have ha_no : ∀ τ : ℝ, 0 < τ → ¬ (f + C τ * g).IsRoot a :=
    fun _ _ => hno.rightFamily_not_isRoot_of_right_root hga
  have hb_no : ∀ τ : ℝ, 0 < τ → ¬ (f + C τ * g).IsRoot b :=
    fun _ _ => hno.rightFamily_not_isRoot_of_right_root hgb
  have hνμ : ν ≤ μ := hν_small μ hμ_pos hμ_root
  have hdegν : ∀ τ ∈ Set.Icc ν μ,
      (f + C τ * g).natDegree = (f + C ν * g).natDegree := by
    intro τ hτ
    exact (hdeg_small μ hμ_pos hμ_root τ hτ).trans
      (hdeg_small μ hμ_pos hμ_root ν ⟨le_rfl, hνμ⟩).symm
  have hdropν :
      ((f + C ν * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C ν * g).roots.filter (a < ·)).card :=
    (rightFamily_count_drop_two_iff_of_forall_pos_not_isRoot
      hfg ha_no hb_no hν_pos hνμ hdegν).mpr hdrop
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  have hf_no_Icc : ∀ z ∈ Set.Icc a b, ¬ f.IsRoot z :=
    hno.symm.right_not_isRoot_Icc_of_left_roots hga hgb hf_no
  exact false_of_add_right_count_drop_of_count_sub_eq_no_isRoot_Icc
    hab hf_no_Icc hdropν hsub_eq

/-- Endpoint-shaped `g`/`g` contradiction using a small positive right-family
parameter.  If the transported count drop reaches a small parameter whose
endpoint strict-upper counts agree with those of `f`, then same-owner
`g`-endpoints contradict the fact that `f` has no roots in `(a, b]`. -/
theorem OppositeLeadingSigns.false_of_right_roots_add_right_small_count_eq_left
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y ν : ℝ}
    (hga : g.IsRoot a) (hgb : g.IsRoot b)
    (hf_no : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card))
    (hν_pos : 0 < ν)
    (hν_small : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y → ν ≤ μ)
    (hdeg_small : ∀ μ : ℝ, 0 < μ → (f + C μ * g).IsRoot y →
      ∀ τ ∈ Set.Icc ν μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (ha_eq : ((f + C ν * g).roots.filter (a < ·)).card =
      (f.roots.filter (a < ·)).card)
    (hb_eq : ((f + C ν * g).roots.filter (b < ·)).card =
      (f.roots.filter (b < ·)).card) :
    False := by
  exact hsgn.false_of_right_roots_add_right_small_count_sub_eq_left
    hfg hno hf hg hga hgb hf_no hg_no hax hxb hay hyb hnot_odd
    hν_pos hν_small hdeg_small (by rw [ha_eq, hb_eq]; simp)

end LiuOppositeSigns
end RealRooted
