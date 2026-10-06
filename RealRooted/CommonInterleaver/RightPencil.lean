/-
# Right-pencil and closed-segment theory for common interleavers

Succ-degree right-pencil, endpoint-sign, and closed-segment equivalences
extracted from `RealRooted.CommonInterleaverTwo`.
-/
import RealRooted.Compatibility.Basic
import RealRooted.CommonInterleaver.RootCountCombinatorics
import RealRooted.CommonInterleaver.SameDegreeRootCount
import RealRooted.Derivative
import RealRooted.RootContinuity
import RealRooted.RootCountJump
import RealRooted.RootOrderBridge
import RealRooted.WagnerX

open Polynomial

noncomputable section

namespace RealRooted

/-- Succ-degree right-pencil parity bridge for upper root counts. -/
theorem succDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact sameDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    hf_split hg_split hf_pos hg_pos hxf hxg

/-- Succ-degree upper root-count parity in endpoint-sign form. -/
theorem succDegree_odd_roots_gt_count_sub_iff_eval_mul_neg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔ f.eval x * g.eval x < 0) := by
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  exact (succDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hf_split hxf hxg).trans
    (exists_pos_isRoot_add_right_iff_eval_mul_neg hfx_eval)

/-- If the succ-degree upper root-count difference is not odd, then the
endpoint evaluations at that common non-root have the same sign. -/
theorem succDegree_eval_mul_pos_of_not_odd_roots_gt_count_sub
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    0 < f.eval x * g.eval x := by
  have hnot_neg : ¬ f.eval x * g.eval x < 0 := by
    intro hneg
    exact hnot_odd
      ((succDegree_odd_roots_gt_count_sub_iff_eval_mul_neg
        hf_pos hg_pos hfg hdeg hf_split hxf hxg).mpr hneg)
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  have hgx_eval : g.eval x ≠ 0 := by
    intro hgx
    exact hxg (by simpa [Polynomial.IsRoot.def] using hgx)
  have hprod_ne : f.eval x * g.eval x ≠ 0 := mul_ne_zero hfx_eval hgx_eval
  exact lt_of_le_of_ne (le_of_not_gt hnot_neg) hprod_ne.symm

/-- A gap of exactly two in the forward upper root count forces same-sign
endpoint evaluations at a common non-root threshold. -/
theorem succDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  succDegree_eval_mul_pos_of_not_odd_roots_gt_count_sub
    hf_pos hg_pos hfg hdeg hf_split hxf hxg (by rw [hcount]; norm_num)

/-- A gap of exactly two in the reverse upper root count forces same-sign
endpoint evaluations at a common non-root threshold. -/
theorem succDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x := by
  refine succDegree_eval_mul_pos_of_not_odd_roots_gt_count_sub
    hf_pos hg_pos hfg hdeg hf_split hxf hxg ?_
  rw [show ((f.roots.filter (x < ·)).card : ℤ) -
      (g.roots.filter (x < ·)).card = -2 by linarith]
  norm_num

/-- A forward upper root-count gap of two rules out roots at that threshold
throughout the closed segment between the endpoints. -/
theorem succDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 <|
    succDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
      hf_pos hg_pos hfg hdeg hf_split hxf hxg hcount

/-- A reverse upper root-count gap of two rules out roots at that threshold
throughout the closed segment between the endpoints. -/
theorem succDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 <|
    succDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
      hf_pos hg_pos hfg hdeg hf_split hxf hxg hcount

/-- Compatible-pair version of the forward gap-two closed-segment
nonvanishing lemma. -/
theorem compatibleSuccDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  succDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hβ0 hβ1 hxf hxg hcount

/-- Compatible-pair version of the reverse gap-two closed-segment
nonvanishing lemma. -/
theorem compatibleSuccDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {β x : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x :=
  succDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hβ0 hβ1 hxf hxg hcount

/-- Interior closed-segment members are nonzero scalar multiples of the right
pencil `f + μ g`, with `μ = β / (1 - β)`. -/
theorem closedSegment_eq_C_mul_add_right
    {f g : ℝ[X]} {β : ℝ} (hβ : β < 1) :
    C (1 - β) * f + C β * g =
      C (1 - β) * (f + C (β / (1 - β)) * g) := by
  have hden : 1 - β ≠ 0 := by linarith
  rw [mul_add, ← mul_assoc, ← C_mul]
  have hmul : (1 - β) * (β / (1 - β)) = β := by field_simp [hden]
  rw [hmul]

/-- Passing from an interior closed-segment member to the corresponding right
pencil preserves the root predicate at every threshold. -/
theorem closedSegment_isRoot_iff_add_right_of_lt_one
    {f g : ℝ[X]} {β x : ℝ} (hβ : β < 1) :
    (C (1 - β) * f + C β * g).IsRoot x ↔
      (f + C (β / (1 - β)) * g).IsRoot x := by
  rw [closedSegment_eq_C_mul_add_right hβ]
  simp [Polynomial.IsRoot.def, (by linarith : 1 - β ≠ 0)]

/-- Multiplying by a nonzero scalar preserves simple real roots. -/
theorem HasSimpleRoots.C_mul {p : ℝ[X]} {c : ℝ}
    (hp : HasSimpleRoots p) (hc : c ≠ 0) :
    HasSimpleRoots (C c * p) := by
  intro x hx
  have hp_ne : p ≠ 0 := hp.ne_zero
  have hcp_ne : C c * p ≠ 0 := mul_ne_zero (C_ne_zero.mpr hc) hp_ne
  rw [Polynomial.rootMultiplicity_mul hcp_ne, Polynomial.rootMultiplicity_C]
  have hroot_p : p.IsRoot x := by simpa [Polynomial.IsRoot.def, eval_mul, eval_C, hc] using hx
  rw [hp x hroot_p]

/-- The change of variables `β = μ / (μ + 1)` turns a nonnegative right-pencil
parameter into an interior closed-segment parameter and preserves the root
predicate. -/
theorem closedSegment_isRoot_iff_add_right_of_nonneg
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ) :
    (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).IsRoot x ↔
      (f + C μ * g).IsRoot x := by
  have hden_pos : 0 < μ + 1 := by linarith
  have hβlt : μ / (μ + 1) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have hratio : (μ / (μ + 1)) / (1 - μ / (μ + 1)) = μ := by
    field_simp [hden_pos.ne']
    ring
  rw [closedSegment_isRoot_iff_add_right_of_lt_one hβlt, hratio]

/-- A no-root hypothesis on the nonnegative right family also controls the
reciprocal family near the larger-degree endpoint. -/
theorem rightFamily_not_isRoot_add_left_of_pos
    {f g : ℝ[X]} {ν x : ℝ} (hν : 0 < ν)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    ¬ (g + C ν * f).IsRoot x := by
  intro hroot
  have hroot' : (f + C ν⁻¹ * g).IsRoot x :=
    (add_right_isRoot_iff_add_left_inv (f := g) (g := f)
      (μ := ν) (x := x) hν.ne').1 hroot
  exact hno (μ := ν⁻¹) (inv_nonneg.mpr hν.le) hroot'

/-- If a threshold is not a root anywhere on the closed segment, then it is
not a root of any nonnegative right-pencil member. -/
theorem closedSegment_not_isRoot_add_right_of_nonneg
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ)
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) :
    ¬ (f + C μ * g).IsRoot x := by
  have hden_pos : 0 < μ + 1 := by linarith
  have hβ0 : 0 ≤ μ / (μ + 1) := div_nonneg hμ hden_pos.le
  have hβ1 : μ / (μ + 1) ≤ 1 := by
    rw [div_le_one hden_pos]
    linarith
  intro hroot
  have hseg_root : (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).IsRoot x :=
    (closedSegment_isRoot_iff_add_right_of_nonneg (f := f) (g := g)
      (x := x) hμ).2 hroot
  exact hseg hβ0 hβ1 hseg_root

/-- Splitting descends through translation by `X + r`. -/
lemma splits_of_comp_X_add_C_splits
    {p : ℝ[X]} (r : ℝ) (hp : (p.comp (X + C r)).Splits) :
    p.Splits := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · have hq0 : p.comp (X + C r) ≠ 0 := (Polynomial.comp_X_add_C_ne_zero_iff).2 hp0
    have hback := isRealRooted_comp_X_add_C hq0 hp (-r)
    simpa [Polynomial.comp_assoc, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
      using hback.2

/-- If the threshold is never a root of a nonnegative right-pencil member, then
the forward upper root-count difference has even parity. -/
theorem succDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    Even (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) := by
  rw [← Int.not_odd_iff_even]
  intro hodd
  obtain ⟨μ, hμ, hroot⟩ :=
    (succDegree_odd_roots_gt_count_sub_iff_exists_pos_isRoot_add_right
      hf_pos hg_pos hfg hdeg hf_split hxf hxg).mp hodd
  exact hno hμ.le hroot

/-- Compatible-pair version of
`succDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot`. -/
theorem compatibleSuccDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    Even (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) :=
  succDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hxf hxg hno

end RealRooted
