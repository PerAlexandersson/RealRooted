import RealRooted.CommonInterleaverTwo
import RealRooted.LiuOppositeSigns
import RealRooted.PositiveParameterLocalLowerCount
import RealRooted.RootContinuity
import RealRooted.RootCountLocalConstancy

/-!
# Liu opposite-sign compatibility theorem targets

This module connects the lightweight root-count scaffolding in
`RealRooted.LiuOppositeSigns` to the existing `Compatible` API.  The hard
mathematical content of Lily L. Liu's Theorem 2.1 is kept as a named statement
so later proof work can target a stable interface.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The two polynomials have no common real root.  This is the reduction
regime used explicitly in Liu's proof of Theorem 2.1 before the largest-root
case split. -/
def NoCommonRoots (f g : ℝ[X]) : Prop :=
  ∀ r : ℝ, f.IsRoot r → ¬ g.IsRoot r

theorem NoCommonRoots.symm {f g : ℝ[X]} (h : NoCommonRoots f g) :
    NoCommonRoots g f := by
  intro r hgr hfr
  exact (h r hfr) hgr

/-- A nonzero right-family member has no root at a left endpoint root when the
endpoint polynomials have no common root. -/
theorem NoCommonRoots.rightFamily_not_isRoot_of_left_root
    {f g : ℝ[X]} (h : NoCommonRoots f g) {μ x : ℝ}
    (hμ : μ ≠ 0) (hf : f.IsRoot x) :
    ¬ (f + C μ * g).IsRoot x := by
  have hg : ¬ g.IsRoot x := h x hf
  have hf_eval : f.eval x = 0 := by
    simpa [Polynomial.IsRoot.def] using hf
  have hg_eval_ne : g.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero g x).mp hg
  have hq_eval_ne : (f + C μ * g).eval x ≠ 0 := by
    simpa [eval_add, eval_mul, eval_C, hf_eval] using
      mul_ne_zero hμ hg_eval_ne
  exact
    (Polynomial.not_isRoot_iff_eval_ne_zero (f + C μ * g) x).mpr hq_eval_ne

/-- A right-family member has no root at a right endpoint root when the
endpoint polynomials have no common root. -/
theorem NoCommonRoots.rightFamily_not_isRoot_of_right_root
    {f g : ℝ[X]} (h : NoCommonRoots f g) {μ x : ℝ}
    (hg : g.IsRoot x) :
    ¬ (f + C μ * g).IsRoot x := by
  have hf : ¬ f.IsRoot x := h.symm x hg
  have hf_eval_ne : f.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero f x).mp hf
  have hg_eval : g.eval x = 0 := by
    simpa [Polynomial.IsRoot.def] using hg
  have hq_eval_ne : (f + C μ * g).eval x ≠ 0 := by
    simpa [eval_add, eval_mul, eval_C, hg_eval] using hf_eval_ne
  exact
    (Polynomial.not_isRoot_iff_eval_ne_zero (f + C μ * g) x).mpr hq_eval_ne

/-- If the endpoints of `[a, b]` are roots of `f`, the polynomials have no
common roots, and `g` has no roots in `(a, b)`, then `g` has no roots on the
closed interval `[a, b]`. -/
theorem NoCommonRoots.right_not_isRoot_Icc_of_left_roots
    {f g : ℝ[X]} (h : NoCommonRoots f g) {a b : ℝ}
    (hfa : f.IsRoot a) (hfb : f.IsRoot b)
    (hg_no : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z) :
    ∀ z ∈ Set.Icc a b, ¬ g.IsRoot z := by
  intro z hz hgz
  by_cases hza : z = a
  · exact (h a hfa) (by simpa [hza] using hgz)
  have haz : a < z := lt_of_le_of_ne hz.1 (Ne.symm hza)
  by_cases hzb : z = b
  · exact (h b hfb) (by simpa [hzb] using hgz)
  have hzb_lt : z < b := lt_of_le_of_ne hz.2 hzb
  exact hg_no z haz hzb_lt hgz

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

private theorem false_of_add_right_count_drop_of_count_sub_eq_no_isRoot_Icc
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
  have hga_eval : g.eval a = 0 := by
    simpa [Polynomial.IsRoot.def] using hga
  have hgb_eval : g.eval b = 0 := by
    simpa [Polynomial.IsRoot.def] using hgb
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
private theorem OppositeLeadingSigns.false_of_left_roots_add_left_inv_count_sub_eq_right
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
private theorem OppositeLeadingSigns.false_of_right_roots_add_right_small_count_sub_eq_left
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

/-- Opposite-sign caller boundary for the finite Liu count descent from the
cross-owned finite-gap input.  This avoids asking for the stronger original
one-sided `≤ 1` strict-upper bounds, which do not hold in every deletion
orientation. -/
theorem theorem21RootCountBranches_of_crossOwned
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ := exists_largestRoots hf hg hsgn hf_deg hg_deg
  exact theorem21RootCountBranches_of_crossOwned_consecutive_roots
    hsgn.left_ne_zero hsgn.right_ne_zero hr hs
    (fun _ hc => hsimple_f.roots_count_eq_one hc)
    (fun _ hc => hsimple_g.roots_count_eq_one hc)
    hno hcross

/-- Caller boundary for Liu's finite count descent from open-gap
root-freeness data for the endpoint families.  This composes the analytic
`CrossOwnedNotOddGaps` supplier with the existing finite root-count branch
theorem, without introducing a new branch hierarchy. -/
theorem theorem21RootCountBranches_of_no_isRoot_Ioo
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (νL νR : ℝ → ℝ)
    (hνL_pos : ∀ x : ℝ, 0 < νL x)
    (hνL_large : ∀ x μ : ℝ, 0 < μ →
      (f + C μ * g).IsRoot x → μ ≤ νL x)
    (hdegL : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ (νL x),
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hleft_no : ∀ x a b : ℝ, a < x → x < b →
      f.IsRoot a → f.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ z : ℝ, a < z → z < b →
        ¬ (g + C (νL x)⁻¹ * f).IsRoot z)
    (hνR_pos : ∀ x : ℝ, 0 < νR x)
    (hνR_small : ∀ x μ : ℝ, 0 < μ →
      (f + C μ * g).IsRoot x → νR x ≤ μ)
    (hdegR : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc (νR x) μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hright_no : ∀ x a b : ℝ, a < x → x < b →
      g.IsRoot a → g.IsRoot b →
      (∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z ∧ ¬ g.IsRoot z) →
      ∀ z : ℝ, a < z → z < b →
        ¬ (f + C (νR x) * g).IsRoot z) :
    theorem21RootCountBranches f g := by
  exact theorem21RootCountBranches_of_crossOwned hsgn hf hg
    hf_deg hg_deg hsimple_f hsimple_g hno
    (hsgn.crossOwnedNotOddGaps_of_no_isRoot_Ioo
      hfg hno hf hg νL νR hνL_pos hνL_large hdegL hleft_no
      hνR_pos hνR_small hdegR hright_no)

/-- A distinct-degree compatible pair is strictly positive-combination
real-rooted.  The usual positive-leading hypothesis is not needed here:
distinct endpoint degrees rule out the zero-polynomial branch for positive
weights by comparing the degrees of the two scaled summands. -/
theorem posComboRealRooted_of_compatible_natDegree_ne
    {f g : ℝ[X]} (hcompat : Compatible f g)
    (hdeg : f.natDegree ≠ g.natDegree) :
    PosComboRealRooted f g := by
  intro α β hα hβ
  rcases hcompat α β hα.le hβ.le with hzero | hrr
  · exfalso
    have hαdeg : (C α * f).natDegree = f.natDegree :=
      Polynomial.natDegree_C_mul (ne_of_gt hα)
    have hβdeg : (C β * g).natDegree = g.natDegree :=
      Polynomial.natDegree_C_mul (ne_of_gt hβ)
    rcases lt_or_gt_of_ne hdeg with hlt | hgt
    · have hscaled : (C α * f).natDegree < (C β * g).natDegree := by
        simpa [hαdeg, hβdeg] using hlt
      have hsum_deg :
          (C α * f + C β * g).natDegree = (C β * g).natDegree :=
        Polynomial.natDegree_add_eq_right_of_natDegree_lt hscaled
      have hg_deg_zero : g.natDegree = 0 := by
        simpa [hzero, hβdeg, Polynomial.natDegree_zero] using hsum_deg.symm
      have hg_deg_pos : 0 < g.natDegree :=
        lt_of_le_of_lt (Nat.zero_le _) hlt
      lia
    · have hscaled : (C β * g).natDegree < (C α * f).natDegree := by
        simpa [hαdeg, hβdeg] using hgt
      have hsum_deg :
          (C α * f + C β * g).natDegree = (C α * f).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt hscaled
      have hf_deg_zero : f.natDegree = 0 := by
        simpa [hzero, hαdeg, Polynomial.natDegree_zero] using hsum_deg.symm
      have hf_deg_pos : 0 < f.natDegree :=
        lt_of_le_of_lt (Nat.zero_le _) hgt
      lia
  · exact hrr

/-- In the no-common, nonconstant splitting regime, compatibility supplies the
strictly positive-combination real-rootedness hypothesis.  A zero positive
combination would make every root of `g` a root of `f`, contradicting the
no-common-root hypothesis. -/
theorem posComboRealRooted_of_compatible_noCommon_nonconstant
    {f g : ℝ[X]} (hcompat : Compatible f g) (hno : NoCommonRoots f g)
    (hg : g.Splits) (hg_deg : g.natDegree ≠ 0) :
    PosComboRealRooted f g := by
  intro α β hα hβ
  rcases hcompat α β hα.le hβ.le with hzero | hrr
  · exfalso
    have hg_ne : g ≠ 0 := by
      intro hg_zero
      exact hg_deg (by simp [hg_zero])
    obtain ⟨r, hr_mem⟩ :=
      Multiset.exists_mem_of_ne_zero (hg.roots_ne_zero hg_deg)
    have hgr : g.IsRoot r := (Polynomial.mem_roots hg_ne).mp hr_mem
    have hsum_eval : (C α * f + C β * g).eval r = 0 := by
      simp [hzero]
    have hgr_eval : g.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hgr
    have hfr_eval : f.eval r = 0 := by
      have hα_eval : α * f.eval r = 0 := by
        simpa [eval_add, eval_mul, eval_C, hgr_eval] using hsum_eval
      exact (mul_eq_zero.mp hα_eval).resolve_left (ne_of_gt hα)
    have hfr : f.IsRoot r := by
      simpa [Polynomial.IsRoot.def] using hfr_eval
    exact (hno r hfr) hgr
  · exact hrr

/-- Caller boundary for Liu's finite count descent in the distinct-degree
case.  This is the preferred entry point when the endpoint degrees differ:
the local compactness and degree-constancy supplier proves the cross-owned
finite-gap input internally. -/
theorem theorem21RootCountBranches_of_natDegree_ne
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hdeg : f.natDegree ≠ g.natDegree) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_crossOwned hsgn hf hg
    hf_deg hg_deg hsimple_f hsimple_g hno
    (hsgn.crossOwnedNotOddGaps_of_natDegree_ne hfg hno hf hg hdeg)

/-- Compatible caller boundary for Liu's finite count descent in the
distinct-degree case.  Compatibility supplies the positive-combination
real-rootedness hypothesis because unequal endpoint degrees prevent positive
linear combinations from vanishing. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_ne
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcompat : Compatible f g)
    (hdeg : f.natDegree ≠ g.natDegree) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_natDegree_ne hsgn
    (posComboRealRooted_of_compatible_noCommon_nonconstant hcompat hno hg hg_deg)
    hf hg hf_deg hg_deg hsimple_f hsimple_g hno hdeg

/-- Caller boundary for Liu's finite count descent in the equal-degree case,
provided the positive crossing parameters stay on the appropriate side of the
unique leading-term cancellation parameter in same-owner gaps. -/
theorem theorem21RootCountBranches_of_natDegree_eq_of_crossing_cancel_sides
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hdeg : f.natDegree = g.natDegree)
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
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_crossOwned hsgn hf hg
    hf_deg hg_deg hsimple_f hsimple_g hno
    (hsgn.crossOwnedNotOddGaps_of_natDegree_eq_of_crossing_cancel_sides
      hfg hno hf hg hdeg hleft_cancel_lt hright_lt_cancel)

/-- Compatible caller boundary for the equal-degree crossing-side
case.  Compatibility supplies positive-combination real-rootedness in the
no-common nonconstant regime; the two local cancellation-side hypotheses remain
explicit. -/
theorem theorem21RootCountBranches_of_compatible_natDegree_eq_of_crossing_cancel_sides
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcompat : Compatible f g)
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
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_natDegree_eq_of_crossing_cancel_sides hsgn
    (posComboRealRooted_of_compatible_noCommon_nonconstant hcompat hno hg hg_deg)
    hf hg hf_deg hg_deg hsimple_f hsimple_g hno hdeg
    hleft_cancel_lt hright_lt_cancel

/-- Caller boundary for Liu's finite count descent from parameter-bound and
zero-end degree-constancy data.  This is a convenience wrapper for callers
already living at `OppositeLeadingSigns.crossOwnedNotOddGaps_of_parameter_bounds`;
new analytic proofs should usually target the endpoint count-difference or
open-gap no-root boundaries directly. -/
theorem theorem21RootCountBranches_of_parameter_bounds
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (νL νR : ℝ → ℝ)
    (hνL_pos : ∀ x : ℝ, 0 < νL x)
    (hνL_large : ∀ x μ : ℝ, 0 < μ →
      (f + C μ * g).IsRoot x → μ ≤ νL x)
    (hdegL : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc μ (νL x),
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hdegL_inv : ∀ x η : ℝ, η ∈ Set.Icc (0 : ℝ) (νL x)⁻¹ →
      (g + C η * f).natDegree = (g + C (0 : ℝ) * f).natDegree)
    (hνR_pos : ∀ x : ℝ, 0 < νR x)
    (hνR_small : ∀ x μ : ℝ, 0 < μ →
      (f + C μ * g).IsRoot x → νR x ≤ μ)
    (hdegR : ∀ x μ : ℝ, 0 < μ → (f + C μ * g).IsRoot x →
      ∀ τ ∈ Set.Icc (νR x) μ,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree)
    (hdegR_zero : ∀ x η : ℝ, η ∈ Set.Icc (0 : ℝ) (νR x) →
      (f + C η * g).natDegree = (f + C (0 : ℝ) * g).natDegree) :
    theorem21RootCountBranches f g := by
  exact theorem21RootCountBranches_of_crossOwned hsgn hf hg
    hf_deg hg_deg hsimple_f hsimple_g hno
    (hsgn.crossOwnedNotOddGaps_of_parameter_bounds
      hfg hno hf hg νL νR hνL_pos hνL_large hdegL hdegL_inv
      hνR_pos hνR_small hdegR hdegR_zero)

/-- Caller boundary for the finite Liu count descent from stronger one-sided
strict-upper `≤ 1` root-count bounds.  The raw largest-root witnesses and
multiplicity-one root-count assumptions are supplied from nonconstant splitting
endpoints and `HasSimpleRoots`.  Prefer `theorem21RootCountBranches_of_crossOwned`
when the available input is the cross-owned finite-gap predicate. -/
theorem theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hupper_fg : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1)
    (hupper_gf : ∀ x : ℝ, ¬ g.IsRoot x → ¬ f.IsRoot x →
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g := by
  obtain ⟨r, s, hr, hs⟩ := exists_largestRoots hf hg hsgn hf_deg hg_deg
  exact theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned_consecutive_roots
    hsgn.left_ne_zero hsgn.right_ne_zero hr hs hupper_fg hupper_gf
    (fun _ hc => hsimple_f.roots_count_eq_one hc)
    (fun _ hc => hsimple_g.roots_count_eq_one hc)
    hno hcross

/-- Opposite-sign caller boundary for the finite Liu count descent.  Compatible
root counts supply the two one-sided strict-upper bounds needed by the direct
one-sided theorem. -/
theorem theorem21RootCountBranches_of_rootCountCompatible_of_crossOwned
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcount : RootCountCompatible f g)
    (hsimple_f : HasSimpleRoots f) (hsimple_g : HasSimpleRoots g)
    (hno : NoCommonRoots f g) (hcross : CrossOwnedNotOddGaps f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_left_sub_le_one_of_crossOwned hsgn hf hg
    hf_deg hg_deg
    (fun _ hfx hgx => hcount.rootCountAbove_left_sub_le_one_of_nonRoot
      hsgn.left_ne_zero hsgn.right_ne_zero hfx hgx)
    (fun _ hgx hfx => hcount.symm.rootCountAbove_left_sub_le_one_of_nonRoot
      hsgn.right_ne_zero hsgn.left_ne_zero hgx hfx)
    hsimple_f hsimple_g hno hcross

/-- Explicit large-parameter fallback for the endpoint-shaped `g`/`g`
contradiction in Liu's odd-indexed interval argument.  If the transported
right-family count drop reaches a parameter whose endpoint strict-upper counts
agree with those of `f`, then same-owner `g`-endpoints contradict the fact that
`f` has no roots in `(a, b]`.

The paper-route proof should normally use a small-parameter/downward-transport
version of this statement instead; this theorem keeps the already-proved
large-parameter form available under explicit hypotheses. -/
theorem OppositeLeadingSigns.false_of_right_roots_add_right_large_count_eq_left
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits) {a b x y ν : ℝ}
    (hga : g.IsRoot a) (hgb : g.IsRoot b)
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
      (f.roots.filter (a < ·)).card)
    (hb_eq : ((f + C ν * g).roots.filter (b < ·)).card =
      (f.roots.filter (b < ·)).card) :
    False := by
  obtain ⟨μ, hμ_pos, hμ_root, _hdrop, hdrop_le⟩ :=
    hsgn.exists_pos_crossing_add_right_Ioo_right_roots_gt_drop_two_le
      hfg hno hf hg hga hgb hf_no hg_no hax hxb hay hyb hnot_odd
  have hdropν :
      ((f + C ν * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C ν * g).roots.filter (a < ·)).card :=
    hdrop_le ν (hν_large μ hμ_pos hμ_root) (hdeg_large μ hμ_pos hμ_root)
  have hab : a ≤ b := le_of_lt (lt_trans hax hxb)
  have hf_no_Icc : ∀ z ∈ Set.Icc a b, ¬ f.IsRoot z :=
    hno.symm.right_not_isRoot_Icc_of_left_roots hga hgb hf_no
  exact false_of_add_right_count_drop_of_count_sub_eq_no_isRoot_Icc
    hab hf_no_Icc hdropν (by rw [ha_eq, hb_eq]; simp)

/-- Multiplying both entries by the same splitting factor preserves
compatibility. -/
theorem compatible_mul_common_factor {d f g : ℝ[X]}
    (hd : d.Splits) (h : Compatible f g) :
    Compatible (d * f) (d * g) := by
  intro α β hα hβ
  have hfactor :
      C α * (d * f) + C β * (d * g) = d * (C α * f + C β * g) := by
    ring
  rcases h α β hα hβ with hzero | hrr
  · exact Or.inl (by rw [hfactor, hzero, mul_zero])
  · by_cases hprod_zero : C α * (d * f) + C β * (d * g) = 0
    · exact Or.inl hprod_zero
    · exact Or.inr ⟨hprod_zero, by rw [hfactor]; exact hd.mul hrr.2⟩

/-- If two compatible polynomials have a common root, deleting that shared
linear factor preserves compatibility. -/
theorem compatible_deleteRootFactor_of_common_root {f g : ℝ[X]} {r : ℝ}
    (h : Compatible f g) (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    Compatible (deleteRootFactor f r) (deleteRootFactor g r) := by
  intro α β hα hβ
  let df : ℝ[X] := deleteRootFactor f r
  let dg : ℝ[X] := deleteRootFactor g r
  let combo : ℝ[X] :=
    C α * df + C β * dg
  change combo = 0 ∨ (combo ≠ 0 ∧ combo.Splits)
  have hf_def : f = (X - C r) * df := by
    simpa [df] using (factor_deleteRootFactor_of_isRoot hrf).symm
  have hg_def : g = (X - C r) * dg := by
    simpa [dg] using (factor_deleteRootFactor_of_isRoot hrg).symm
  have hfactor :
      C α * f + C β * g = (X - C r) * combo := by
    dsimp [combo]
    rw [hf_def, hg_def]
    ring_nf
  have hcase :
      (X - C r) * combo = 0 ∨
        ((X - C r) * combo ≠ 0 ∧ ((X - C r) * combo).Splits) := by
    simpa [hfactor] using h α β hα hβ
  rcases hcase with hzero | hrr
  · rcases mul_eq_zero.mp hzero with hlinear_zero | hcombo_zero
    · exact False.elim (X_sub_C_ne_zero r hlinear_zero)
    · exact Or.inl hcombo_zero
  · refine Or.inr ⟨?_, ?_⟩
    · intro hcombo_zero
      exact hrr.1 (by rw [hcombo_zero, mul_zero])
    · exact
        (splits_mul_iff_right (X_sub_C_ne_zero r)
          (Polynomial.Splits.X_sub_C r)).mp hrr.2

/-- Failure of the no-common-root predicate produces an explicit common root. -/
theorem exists_common_root_of_not_noCommonRoots {f g : ℝ[X]}
    (hno : ¬ NoCommonRoots f g) :
    ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r := by
  by_contra hmissing
  exact hno (by
    intro r hfr hgr
    exact hmissing ⟨r, hfr, hgr⟩)

/-- Common-root branch for the unreduced Liu statement: peel one common
linear factor and require compatibility of the cofactors. -/
def CommonRootDeletionCompatibleBranch (f g : ℝ[X]) : Prop :=
  ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r ∧
    Compatible (deleteRootFactor f r) (deleteRootFactor g r)

namespace CommonRootDeletionCompatibleBranch

theorem compatible {f g : ℝ[X]}
    (h : CommonRootDeletionCompatibleBranch f g) :
    Compatible f g := by
  rcases h with ⟨r, hfr, hgr, hcompat⟩
  have hmul :=
    compatible_mul_common_factor
      (d := X - C r)
      (Polynomial.Splits.X_sub_C r)
      hcompat
  have hf_def : (X - C r) * deleteRootFactor f r = f :=
    factor_deleteRootFactor_of_isRoot hfr
  have hg_def : (X - C r) * deleteRootFactor g r = g :=
    factor_deleteRootFactor_of_isRoot hgr
  simpa [hf_def, hg_def] using hmul

/-- Compatible polynomials with a common root satisfy the common-root deletion
branch. -/
theorem of_compatible_of_not_noCommonRoots {f g : ℝ[X]}
    (hcompat : Compatible f g) (hno : ¬ NoCommonRoots f g) :
    CommonRootDeletionCompatibleBranch f g := by
  rcases exists_common_root_of_not_noCommonRoots hno with ⟨r, hfr, hgr⟩
  exact ⟨r, hfr, hgr,
    compatible_deleteRootFactor_of_common_root hcompat hfr hgr⟩

end CommonRootDeletionCompatibleBranch

/-- Corrected unreduced branch predicate: either Liu's no-common largest-root
branch holds, or a common root can be peeled and the cofactors are compatible.
-/
def theorem21RootCountBranchesWithCommon (f g : ℝ[X]) : Prop :=
  theorem21RootCountBranches f g ∨ CommonRootDeletionCompatibleBranch f g

/-- Reduced common-root branch predicate.  In the ordinary root-count branch we
remember the no-common-root hypothesis, so no-common reverse statements can be
used after splitting off the common-root case. -/
def theorem21RootCountBranchesReduced (f g : ℝ[X]) : Prop :=
  (NoCommonRoots f g ∧ theorem21RootCountBranches f g) ∨
    CommonRootDeletionCompatibleBranch f g

namespace theorem21RootCountBranchesReduced

/-- Forget the extra no-common-root witness in the reduced branch predicate. -/
theorem withCommon {f g : ℝ[X]}
    (h : theorem21RootCountBranchesReduced f g) :
    theorem21RootCountBranchesWithCommon f g := by
  rcases h with hbranches | hcommon
  · exact Or.inl hbranches.2
  · exact Or.inr hcommon

end theorem21RootCountBranchesReduced

/-- Full unreduced target for Liu Theorem 2.1, stated against the project's
`Compatible` predicate.  The two branch predicate below is the no-common
largest-root case split, so proving this full statement also requires a
common-root reduction outside the branch predicate.  For the theorem shape
matching Liu's reduced proof stage, use
`theorem21CompatibleRootCountNoCommonStatement`.  For an explicit tracker for
the missing common-root interface, see GitHub issue #98.

for two real-rooted polynomials with opposite leading signs, compatibility is
equivalent to the appropriate largest-root deletion branch satisfying Liu's
closed-at-or-above root-count condition. -/
def theorem21CompatibleRootCountStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant form of Liu Theorem 2.1.  This is the induction-friendly
version of the statement because the root-count branches delete a largest root
from each polynomial. -/
def theorem21CompatibleRootCountNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Forward half of Liu Theorem 2.1, isolated as a statement target. -/
def theorem21CompatibleToRootCountBranchesStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g → theorem21RootCountBranches f g

/-- Nonconstant forward half of Liu Theorem 2.1, isolated as a statement
target. -/
def theorem21CompatibleToRootCountBranchesNonconstantStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        Compatible f g → theorem21RootCountBranches f g

/-- Reverse half of Liu Theorem 2.1, isolated as a statement target. -/
def theorem21RootCountBranchesToCompatibleStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      theorem21RootCountBranches f g → Compatible f g

/-- Nonconstant reverse half of Liu Theorem 2.1, isolated as a statement
target. -/
def theorem21RootCountBranchesToCompatibleNonconstantStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        theorem21RootCountBranches f g → Compatible f g

/-- No-common-root form of Liu Theorem 2.1, matching the reduced case in the
paper's proof. -/
def theorem21CompatibleRootCountNoCommonStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    NoCommonRoots f g → (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant no-common-root form of Liu Theorem 2.1. -/
def theorem21CompatibleRootCountNoCommonNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Forward half of the no-common-root form of Liu Theorem 2.1. -/
def theorem21CompatibleToRootCountBranchesNoCommonStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      NoCommonRoots f g → Compatible f g → theorem21RootCountBranches f g

/-- Nonconstant forward half of the no-common-root form of Liu Theorem 2.1. -/
def theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement :
    Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        Compatible f g → theorem21RootCountBranches f g

/-- Reverse half of the no-common-root form of Liu Theorem 2.1. -/
def theorem21RootCountBranchesToCompatibleNoCommonStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      NoCommonRoots f g → theorem21RootCountBranches f g → Compatible f g

/-- Nonconstant reverse half of the no-common-root form of Liu Theorem 2.1. -/
def theorem21RootCountBranchesToCompatibleNoCommonNonconstantStatement :
    Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      NoCommonRoots f g → f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        theorem21RootCountBranches f g → Compatible f g

/-- Reduced common-root Liu target.  The ordinary branch keeps the
no-common-root witness needed by no-common reverse theorems. -/
def theorem21CompatibleRootCountReducedStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g ↔ theorem21RootCountBranchesReduced f g)

/-- Forward half of the reduced common-root target. -/
def theorem21CompatibleToRootCountBranchesReducedStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g → theorem21RootCountBranchesReduced f g

/-- Reverse half of the reduced common-root target. -/
def theorem21RootCountBranchesReducedToCompatibleStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      theorem21RootCountBranchesReduced f g → Compatible f g

/-- Unreduced theorem target with an explicit common-root branch.  This is the
safe full-statement interface; the older `theorem21CompatibleRootCountStatement`
remains the branch-only target used by existing conditional wrappers. -/
def theorem21CompatibleRootCountWithCommonStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g ↔ theorem21RootCountBranchesWithCommon f g)

/-- Forward half of the corrected common-root-branch target. -/
def theorem21CompatibleToRootCountBranchesWithCommonStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g → theorem21RootCountBranchesWithCommon f g

/-- Reverse half of the corrected common-root-branch target. -/
def theorem21RootCountBranchesWithCommonToCompatibleStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      theorem21RootCountBranchesWithCommon f g → Compatible f g

/-- The paper-shaped statement implies its nonconstant restriction. -/
theorem theorem21CompatibleRootCountNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  fun f g hf hg hsgn _ _ => h f g hf hg hsgn

/-- The unreduced full statement implies the no-common-root restriction. -/
theorem theorem21CompatibleRootCountNoCommon_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21CompatibleRootCountNoCommonStatement :=
  fun f g hf hg hsgn _hno => h f g hf hg hsgn

/-- The unreduced nonconstant statement implies the nonconstant no-common-root
restriction. -/
theorem
    theorem21CompatibleRootCountNoCommonNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    theorem21CompatibleRootCountNoCommonNonconstantStatement :=
  fun f g hf hg hsgn _hno hf_deg hg_deg => h f g hf hg hsgn hf_deg hg_deg

/-- The no-common-root statement implies its nonconstant restriction. -/
theorem
    theorem21CompatibleRootCountNoCommonNonconstant_of_theorem21CompatibleRootCountNoCommon
    (h : theorem21CompatibleRootCountNoCommonStatement) :
    theorem21CompatibleRootCountNoCommonNonconstantStatement :=
  fun f g hf hg hsgn hno _ _ => h f g hf hg hsgn hno

/-- The corrected common-root-branch statement implies its branch-only
restriction in the no-common regime. -/
theorem theorem21CompatibleRootCountNoCommon_of_theorem21CompatibleRootCountWithCommon
    (h : theorem21CompatibleRootCountWithCommonStatement) :
    theorem21CompatibleRootCountNoCommonStatement := by
  intro f g hf hg hsgn hno
  constructor
  · intro hcompat
    rcases (h f g hf hg hsgn).1 hcompat with hbranches | hcommon
    · exact hbranches
    · rcases hcommon with ⟨r, hfr, hgr, _hcompat⟩
      exact False.elim ((hno r hfr) hgr)
  · intro hbranches
    exact (h f g hf hg hsgn).2 (Or.inl hbranches)

/-- Projection form of `theorem21CompatibleRootCountStatement`. -/
theorem compatible_iff_theorem21RootCountBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn

/-- Projection form of the nonconstant Liu Theorem 2.1 statement. -/
theorem compatible_iff_theorem21RootCountBranches_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn hf_deg hg_deg

/-- Projection form of the no-common-root Liu Theorem 2.1 statement. -/
theorem compatible_iff_theorem21RootCountBranches_noCommon
    (h : theorem21CompatibleRootCountNoCommonStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hno : NoCommonRoots f g) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn hno

/-- Projection form of the nonconstant no-common-root Liu statement. -/
theorem compatible_iff_theorem21RootCountBranches_noCommon_nonconstant
    (h : theorem21CompatibleRootCountNoCommonNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn hno hf_deg hg_deg

/-- Forward half extracted from the paper-shaped Liu Theorem 2.1 statement. -/
theorem theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21CompatibleToRootCountBranchesStatement := by
  intro f g hf hg hsgn
  exact (h f g hf hg hsgn).1

/-- Forward half extracted from the nonconstant Liu Theorem 2.1 statement. -/
theorem theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    theorem21CompatibleToRootCountBranchesNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg
  exact (h f g hf hg hsgn hf_deg hg_deg).1

/-- Forward half extracted from the no-common-root Liu statement. -/
theorem theorem21CompatibleToRootCountBranchesNoCommon_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNoCommonStatement) :
    theorem21CompatibleToRootCountBranchesNoCommonStatement := by
  intro f g hf hg hsgn hno
  exact (h f g hf hg hsgn hno).1

/-- Forward half extracted from the nonconstant no-common-root Liu statement.
-/
theorem
    theorem21CompatibleToRootCountBranchesNoCommonNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNoCommonNonconstantStatement) :
    theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno hf_deg hg_deg
  exact (h f g hf hg hsgn hno hf_deg hg_deg).1

/-- Reverse half extracted from the paper-shaped Liu Theorem 2.1 statement. -/
theorem theorem21RootCountBranchesToCompatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21RootCountBranchesToCompatibleStatement := by
  intro f g hf hg hsgn
  exact (h f g hf hg hsgn).2

/-- Reverse half extracted from the nonconstant Liu Theorem 2.1 statement. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg
  exact (h f g hf hg hsgn hf_deg hg_deg).2

/-- Reverse half extracted from the no-common-root Liu statement. -/
theorem theorem21RootCountBranchesToCompatibleNoCommon_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNoCommonStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonStatement := by
  intro f g hf hg hsgn hno
  exact (h f g hf hg hsgn hno).2

/-- Reverse half extracted from the nonconstant no-common-root Liu statement.
-/
theorem
    theorem21RootCountBranchesToCompatibleNoCommonNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNoCommonNonconstantStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno hf_deg hg_deg
  exact (h f g hf hg hsgn hno hf_deg hg_deg).2

/-- The ordinary forward half restricts to the nonconstant forward half. -/
theorem theorem21CompatibleToRootCountBranchesNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleToRootCountBranchesNonconstantStatement := by
  intro f g hf hg hsgn _hf_deg _hg_deg hcompat
  exact hforward hf hg hsgn hcompat

/-- The ordinary reverse half restricts to the nonconstant reverse half. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement := by
  intro f g hf hg hsgn _hf_deg _hg_deg hbranches
  exact hreverse hf hg hsgn hbranches

/-- The no-common-root forward half restricts to its nonconstant form. -/
theorem theorem21CompatibleToRootCountBranchesNoCommonNonconstant_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement) :
    theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno _hf_deg _hg_deg hcompat
  exact hforward hf hg hsgn hno hcompat

/-- The ordinary forward half implies the no-common-root forward half. -/
theorem theorem21CompatibleToRootCountBranchesNoCommon_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement) :
    theorem21CompatibleToRootCountBranchesNoCommonStatement := by
  intro f g hf hg hsgn _hno hcompat
  exact hforward hf hg hsgn hcompat

/-- The ordinary nonconstant forward half implies the nonconstant
no-common-root forward half. -/
theorem theorem21CompatibleToRootCountBranchesNoCommonNonconstant_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement) :
    theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement := by
  intro f g hf hg hsgn _hno hf_deg hg_deg hcompat
  exact hforward hf hg hsgn hf_deg hg_deg hcompat

/-- The no-common-root reverse half restricts to its nonconstant form. -/
theorem theorem21RootCountBranchesToCompatibleNoCommonNonconstant_of_noCommonReverse
    (hreverse : theorem21RootCountBranchesToCompatibleNoCommonStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno _hf_deg _hg_deg hbranches
  exact hreverse hf hg hsgn hno hbranches

/-- The ordinary reverse half implies the no-common-root reverse half. -/
theorem theorem21RootCountBranchesToCompatibleNoCommon_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonStatement := by
  intro f g hf hg hsgn _hno hbranches
  exact hreverse hf hg hsgn hbranches

/-- The ordinary nonconstant reverse half implies the nonconstant
no-common-root reverse half. -/
theorem theorem21RootCountBranchesToCompatibleNoCommonNonconstant_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleNonconstantStatement) :
    theorem21RootCountBranchesToCompatibleNoCommonNonconstantStatement := by
  intro f g hf hg hsgn _hno hf_deg hg_deg hbranches
  exact hreverse hf hg hsgn hf_deg hg_deg hbranches

/-- Projection form of the isolated forward direction of Liu Theorem 2.1. -/
theorem theorem21RootCountBranches_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  hforward hf hg hsgn hcompat

/-- Projection form of the isolated nonconstant forward direction of
Liu Theorem 2.1. -/
theorem theorem21RootCountBranches_of_compatible_of_forward_nonconstant
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  hforward hf hg hsgn hf_deg hg_deg hcompat

/-- Projection form of the isolated no-common-root forward direction of
Liu Theorem 2.1. -/
theorem theorem21RootCountBranches_of_compatible_of_forward_noCommon
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  hforward hf hg hsgn hno hcompat

/-- Projection form of the isolated nonconstant no-common-root forward
direction of Liu Theorem 2.1. -/
theorem theorem21RootCountBranches_of_compatible_of_forward_noCommon_nonconstant
    (hforward :
      theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  hforward hf hg hsgn hno hf_deg hg_deg hcompat

/-- Forward direction of Liu Theorem 2.1 as a reusable projection. -/
theorem theorem21RootCountBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

/-- Forward direction of the nonconstant Liu Theorem 2.1 statement. -/
theorem theorem21RootCountBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_of_forward_nonconstant
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- Forward direction of the no-common-root Liu statement. -/
theorem theorem21RootCountBranches_of_compatible_noCommon
    (h : theorem21CompatibleRootCountNoCommonStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hno : NoCommonRoots f g) (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_of_forward_noCommon
    (theorem21CompatibleToRootCountBranchesNoCommon_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hno hcompat

/-- Forward direction of the nonconstant no-common-root Liu statement. -/
theorem theorem21RootCountBranches_of_compatible_noCommon_nonconstant
    (h : theorem21CompatibleRootCountNoCommonNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  theorem21RootCountBranches_of_compatible_of_forward_noCommon_nonconstant
    (theorem21CompatibleToRootCountBranchesNoCommonNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hno hf_deg hg_deg hcompat

/-- The no-common-root forward direction plus common-root deletion gives the
reduced common-root branch predicate. -/
theorem theorem21RootCountBranchesReduced_of_compatible_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranchesReduced f g := by
  by_cases hno : NoCommonRoots f g
  · exact Or.inl ⟨hno, hforward hf hg hsgn hno hcompat⟩
  · exact Or.inr
      (CommonRootDeletionCompatibleBranch.of_compatible_of_not_noCommonRoots
        hcompat hno)

/-- The no-common-root forward direction plus common-root deletion gives the
corrected full forward direction with an explicit common-root branch. -/
theorem theorem21RootCountBranchesWithCommon_of_compatible_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranchesWithCommon f g := by
  exact theorem21RootCountBranchesReduced.withCommon
    (theorem21RootCountBranchesReduced_of_compatible_of_noCommonForward
      hforward hf hg hsgn hcompat)

/-- The corrected reduced forward direction follows from the no-common forward
direction and the automatic common-root deletion branch. -/
theorem theorem21CompatibleToRootCountBranchesReduced_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement) :
    theorem21CompatibleToRootCountBranchesReducedStatement := by
  intro f g hf hg hsgn hcompat
  exact theorem21RootCountBranchesReduced_of_compatible_of_noCommonForward
    hforward hf hg hsgn hcompat

/-- The reduced common-root branch predicate forgets to the existing
with-common branch predicate. -/
theorem theorem21CompatibleToRootCountBranchesWithCommon_of_reduced
    (hreduced : theorem21CompatibleToRootCountBranchesReducedStatement) :
    theorem21CompatibleToRootCountBranchesWithCommonStatement := by
  intro f g hf hg hsgn hcompat
  exact theorem21RootCountBranchesReduced.withCommon
    (hreduced hf hg hsgn hcompat)

/-- No-common-root reverse direction plus factor multiplication proves the
reduced common-root-branch reverse direction. -/
theorem theorem21RootCountBranchesReducedToCompatible_of_noCommonReverse
    (hreverse : theorem21RootCountBranchesToCompatibleNoCommonStatement) :
    theorem21RootCountBranchesReducedToCompatibleStatement := by
  intro f g hf hg hsgn hbranches
  rcases hbranches with hbranches | hcommon
  · exact hreverse hf hg hsgn hbranches.1 hbranches.2
  · exact CommonRootDeletionCompatibleBranch.compatible hcommon

/-- Reassemble the reduced common-root Liu target from separately proved
reduced forward and reverse directions. -/
theorem theorem21CompatibleRootCountReduced_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesReducedStatement)
    (hreverse : theorem21RootCountBranchesReducedToCompatibleStatement) :
    theorem21CompatibleRootCountReducedStatement := by
  intro f g hf hg hsgn
  exact ⟨hforward hf hg hsgn, hreverse hf hg hsgn⟩

/-- Reassemble the reduced common-root Liu target from the no-common forward
and no-common reverse directions. -/
theorem theorem21CompatibleRootCountReduced_of_noCommon_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    (hreverse : theorem21RootCountBranchesToCompatibleNoCommonStatement) :
    theorem21CompatibleRootCountReducedStatement :=
  theorem21CompatibleRootCountReduced_of_forward_and_reverse
    (theorem21CompatibleToRootCountBranchesReduced_of_noCommonForward
      hforward)
    (theorem21RootCountBranchesReducedToCompatible_of_noCommonReverse
      hreverse)

/-- Projection form of the corrected full forward target. -/
theorem theorem21RootCountBranchesWithCommon_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesWithCommonStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranchesWithCommon f g :=
  hforward hf hg hsgn hcompat

/-- The corrected full forward direction follows from the no-common forward
direction and the automatic common-root deletion branch. -/
theorem theorem21CompatibleToRootCountBranchesWithCommon_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement) :
    theorem21CompatibleToRootCountBranchesWithCommonStatement := by
  exact theorem21CompatibleToRootCountBranchesWithCommon_of_reduced
    (theorem21CompatibleToRootCountBranchesReduced_of_noCommonForward hforward)

/-- Branch-only reverse direction plus factor multiplication proves the
corrected common-root-branch reverse direction. -/
theorem theorem21RootCountBranchesWithCommonToCompatible_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21RootCountBranchesWithCommonToCompatibleStatement := by
  intro f g hf hg hsgn hbranches
  rcases hbranches with hbranches | hcommon
  · exact hreverse hf hg hsgn hbranches
  · exact CommonRootDeletionCompatibleBranch.compatible hcommon

/-- Reassemble the corrected common-root-branch Liu target from the
no-common-root forward direction and the branch-only reverse direction. -/
theorem theorem21CompatibleRootCountWithCommon_of_noCommonForward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21CompatibleRootCountWithCommonStatement := by
  intro f g hf hg hsgn
  constructor
  · exact
      theorem21CompatibleToRootCountBranchesWithCommon_of_noCommonForward
        hforward hf hg hsgn
  · exact
      theorem21RootCountBranchesWithCommonToCompatible_of_reverse
        hreverse hf hg hsgn

/-- Projection form of the isolated reverse direction of Liu Theorem 2.1. -/
theorem compatible_of_theorem21RootCountBranches_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  hreverse hf hg hsgn hbranches

/-- Projection form of the isolated nonconstant reverse direction of
Liu Theorem 2.1. -/
theorem compatible_of_theorem21RootCountBranches_of_reverse_nonconstant
    (hreverse : theorem21RootCountBranchesToCompatibleNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  hreverse hf hg hsgn hf_deg hg_deg hbranches

/-- Reverse direction of Liu Theorem 2.1 as a reusable projection. -/
theorem compatible_of_theorem21RootCountBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  compatible_of_theorem21RootCountBranches_of_reverse
    (theorem21RootCountBranchesToCompatible_of_theorem21CompatibleRootCount h)
    hf hg hsgn hbranches

/-- Reverse direction of the nonconstant Liu Theorem 2.1 statement. -/
theorem compatible_of_theorem21RootCountBranches_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  compatible_of_theorem21RootCountBranches_of_reverse_nonconstant
    (theorem21RootCountBranchesToCompatibleNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hbranches

/-- Isolated forward direction with the branch predicate swapped. -/
theorem theorem21RootCountBranches_symm_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranches g f :=
  theorem21RootCountBranches_of_compatible_of_forward hforward
    hg hf hsgn.symm hcompat.comm

/-- Isolated nonconstant forward direction with the branch predicate swapped. -/
theorem theorem21RootCountBranches_symm_of_compatible_of_forward_nonconstant
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches g f :=
  theorem21RootCountBranches_of_compatible_of_forward_nonconstant
    hforward hg hf hsgn.symm hg_deg hf_deg hcompat.comm

/-- Forward direction of Liu Theorem 2.1 with the branch predicate swapped. -/
theorem theorem21RootCountBranches_symm_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches g f :=
  theorem21RootCountBranches_symm_of_compatible_of_forward
    (theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

/-- Forward direction of the nonconstant statement with the branch predicate
swapped. -/
theorem theorem21RootCountBranches_symm_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches g f :=
  theorem21RootCountBranches_symm_of_compatible_of_forward_nonconstant
    (theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- Isolated reverse direction with the branch predicate swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm_of_reverse
    (hreverse : theorem21RootCountBranchesToCompatibleStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  (compatible_of_theorem21RootCountBranches_of_reverse hreverse
    hg hf hsgn.symm hbranches).comm

/-- Isolated nonconstant reverse direction with the branch predicate swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm_of_reverse_nonconstant
    (hreverse : theorem21RootCountBranchesToCompatibleNonconstantStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  (compatible_of_theorem21RootCountBranches_of_reverse_nonconstant
    hreverse hg hf hsgn.symm hg_deg hf_deg hbranches).comm

/-- Reverse direction of Liu Theorem 2.1 with the branch predicate swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  compatible_of_theorem21RootCountBranches_symm_of_reverse
    (theorem21RootCountBranchesToCompatible_of_theorem21CompatibleRootCount h)
    hf hg hsgn hbranches

/-- Reverse direction of the nonconstant statement with the branch predicate
swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  compatible_of_theorem21RootCountBranches_symm_of_reverse_nonconstant
    (theorem21RootCountBranchesToCompatibleNonconstant_of_theorem21CompatibleRootCount
      h)
    hf hg hsgn hf_deg hg_deg hbranches

/-- Projection form of Liu Theorem 2.1 after swapping the two polynomials. -/
theorem compatible_iff_theorem21RootCountBranches_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21RootCountBranches g f :=
  ⟨theorem21RootCountBranches_symm_of_compatible h hf hg hsgn,
    compatible_of_theorem21RootCountBranches_symm h hf hg hsgn⟩

/-- Projection form of the nonconstant Liu Theorem 2.1 statement after
swapping the two polynomials. -/
theorem compatible_iff_theorem21RootCountBranches_symm_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21RootCountBranches g f :=
  ⟨theorem21RootCountBranches_symm_of_compatible_nonconstant h hf hg hsgn
      hf_deg hg_deg,
    compatible_of_theorem21RootCountBranches_symm_nonconstant h hf hg hsgn
      hf_deg hg_deg⟩

end LiuOppositeSigns
end RealRooted
