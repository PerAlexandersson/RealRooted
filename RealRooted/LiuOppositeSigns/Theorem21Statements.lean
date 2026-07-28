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

private theorem rightFamily_count_drop_two_of_forall_pos_not_isRoot_of_le
    {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    {a b μ₀ μ₁ : ℝ}
    (ha_no : ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot a)
    (hb_no : ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot b)
    (hμ₀_pos : 0 < μ₀) (hμ₀μ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree)
    (hdrop :
      ((f + C μ₀ * g).roots.filter (b < ·)).card + 2 ≤
        ((f + C μ₀ * g).roots.filter (a < ·)).card) :
    ((f + C μ₁ * g).roots.filter (b < ·)).card + 2 ≤
      ((f + C μ₁ * g).roots.filter (a < ·)).card := by
  have ha_eq :=
    rightFamily_card_roots_gt_eq_of_forall_pos_not_isRoot
      hfg ha_no hμ₀_pos hμ₀μ₁ hdeg
  have hb_eq :=
    rightFamily_card_roots_gt_eq_of_forall_pos_not_isRoot
      hfg hb_no hμ₀_pos hμ₀μ₁ hdeg
  simpa [← ha_eq, ← hb_eq] using hdrop

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
  exact rightFamily_count_drop_two_of_forall_pos_not_isRoot_of_le
    hfg ha_no hb_no hμ_pos hμν hdeg hdrop

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
  have hg_no_Ioc : ∀ z : ℝ, a < z → z ≤ b → ¬ g.IsRoot z := by
    intro z haz hzb
    exact hg_no_Icc z ⟨le_of_lt haz, hzb⟩
  exact
    (not_card_roots_filter_gt_add_two_le_of_eq_no_isRoot_Ioc
      (p := f + C ν * g) (q := g) hab hg_no_Ioc ha_eq hb_eq) hdropν

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
  exact rightFamily_count_drop_two_of_forall_pos_not_isRoot_of_le
    hfg ha_no hb_no hμ_pos hμν hdeg hdrop

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

end CommonRootDeletionCompatibleBranch

/-- Corrected unreduced branch predicate: either Liu's no-common largest-root
branch holds, or a common root can be peeled and the cofactors are compatible.
-/
def theorem21RootCountBranchesWithCommon (f g : ℝ[X]) : Prop :=
  theorem21RootCountBranches f g ∨ CommonRootDeletionCompatibleBranch f g

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
corrected full forward direction with an explicit common-root branch. -/
theorem theorem21RootCountBranchesWithCommon_of_compatible_of_noCommonForward
    (hforward : theorem21CompatibleToRootCountBranchesNoCommonStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21RootCountBranchesWithCommon f g := by
  by_cases hno : NoCommonRoots f g
  · exact Or.inl (hforward hf hg hsgn hno hcompat)
  · have hcommon : ∃ r : ℝ, f.IsRoot r ∧ g.IsRoot r := by
      by_contra hmissing
      apply hno
      intro r hfr hgr
      exact hmissing ⟨r, hfr, hgr⟩
    rcases hcommon with ⟨r, hfr, hgr⟩
    exact Or.inr
      ⟨r, hfr, hgr,
        compatible_deleteRootFactor_of_common_root hcompat hfr hgr⟩

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
  intro f g hf hg hsgn hcompat
  exact theorem21RootCountBranchesWithCommon_of_compatible_of_noCommonForward
    hforward hf hg hsgn hcompat

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
