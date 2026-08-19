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

/-- In the succ-degree positive-leading setting, the derivative of every
closed-segment member is nonzero as soon as the lower-degree endpoint has
positive degree.

For `β > 0`, the `g.derivative` term has strictly larger degree than the
`f.derivative` term; for `β = 0`, this is just nonvanishing of
`f.derivative`. -/
theorem succDegree_closedSegment_derivative_ne_zero
    {f g : ℝ[X]}
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hfdeg : f.natDegree ≠ 0)
    {β : ℝ} (hβ0 : 0 ≤ β) :
    C (1 - β) * f.derivative + C β * g.derivative ≠ 0 := by
  rcases lt_or_eq_of_le hβ0 with hβ_pos | hβ_zero
  · have hleft_lt :
        (C (1 - β) * f.derivative).natDegree <
          (C β * g.derivative).natDegree := by
      have hleft_le :
          (C (1 - β) * f.derivative).natDegree ≤ f.derivative.natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      have hf'_deg : f.derivative.natDegree = f.natDegree - 1 :=
        f.natDegree_derivative
      have hright_deg :
          (C β * g.derivative).natDegree = g.derivative.natDegree := by
        rw [Polynomial.natDegree_C_mul hβ_pos.ne']
      have hg'_deg : g.derivative.natDegree = g.natDegree - 1 :=
        g.natDegree_derivative
      rw [hright_deg, hg'_deg, hdeg]
      lia
    have hg'_pos : HasPosLeadingCoeff g.derivative :=
      hg_pos.derivative (by rw [hdeg]; lia)
    have hright_pos : HasPosLeadingCoeff (C β * g.derivative) :=
      hasPosLeadingCoeff_C_mul hβ_pos hg'_pos
    exact (hasPosLeadingCoeff_add_of_natDegree_lt_right hleft_lt hright_pos).ne_zero
  · subst hβ_zero
    simpa using (Polynomial.derivative_ne_zero.mpr hfdeg)

/-- In the succ-degree positive-leading setting, derivative closed-segment
members inherit splitting from the original closed segment. -/
theorem succDegree_closedSegment_derivative_splits
    {f g : ℝ[X]}
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧
        (C (1 - β) * f + C β * g).Splits))
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hfdeg : f.natDegree ≠ 0)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f.derivative + C β * g.derivative).Splits :=
  closedSegment_derivative_splits_of_ne hseg hβ0 hβ1
    (succDegree_closedSegment_derivative_ne_zero hg_pos hdeg hfdeg hβ0)

/-- Closed-segment form of the exact gap-two obstruction.  This is the
continuity/count target left after the sign argument has shown that the fixed
threshold is never a root along the closed segment from `f` to `g`. -/
def CompatibleSuccDegreeClosedSegmentNoGapTwoStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≠ 2

/-- Closed-segment endpoint count-equality formulation.  This is the precise
count-stability theorem suggested by the root-continuity route: if a fixed
threshold is never crossed along the closed segment from the lower-degree
endpoint to the higher-degree endpoint, then the endpoint upper root counts at
that threshold agree. -/
def CompatibleSuccDegreeClosedSegmentCountEqStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card

/-- Right-pencil form of the exact gap-two obstruction.  The closed-segment
form reduces to this by the change of variables `β = μ / (μ + 1)`. -/
def CompatibleSuccDegreeRightFamilyNoGapTwoStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≠ 2

/-- Endpoint-sign form of the exact gap-two obstruction.  The right-pencil
no-root hypothesis is equivalent to this same-sign condition at a common
non-root threshold. -/
def CompatibleSuccDegreeEndpointSignNoGapTwoStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 < f.eval x * g.eval x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≠ 2

/-- Coefficient-free compatible succ-degree all-combinations shortcut.  This
candidate direct Obreschkoff span statement is now known to be false; see
`CommonInterleaverExamples.not_compatibleSuccDegreeAllComboStatement`. -/
def CompatibleSuccDegreeAllComboStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    AllComboRealRooted f g

/-- Signed right-pencil form of the compatible succ-degree all-combinations
shortcut.  By scaling, this one-parameter family is equivalent to the whole
real linear span, and it is likewise known to be false. -/
def CompatibleSuccDegreeSignedRightFamilyStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ μ : ℝ, (f + C μ * g).Splits

/-- Negative right-pencil form of the compatible succ-degree all-combinations
shortcut.  Compatibility supplies the case `0 ≤ μ`, but the isolated negative
half-line is false in general. -/
def CompatibleSuccDegreeNegativeRightFamilyStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ μ : ℝ, μ < 0 → (f + C μ * g).Splits

/-- Nonnegative-coefficient version of the negative right-pencil shortcut.
This candidate strengthening is false even before translating endpoints. -/
def CompatibleSuccDegreeNegativeRightFamilyNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ μ : ℝ, μ < 0 → (f + C μ * g).Splits

/-- Coefficient-free compatible succ-degree orientation shortcut.  The forced
proper-position orientation `f ≪ g` is false in general; this statement remains
only as a named failed route. -/
def CompatibleSuccDegreePrecStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    Prec f g

/-- Exact lower-threshold endpoint-sign comparison expected from the
left-endpoint/count-stability picture. -/
def CompatibleSuccDegreeEndpointSignLowerCountEqStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 < f.eval x * g.eval x →
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card = 1

/-- Lower-threshold endpoint-sign form of the exact gap obstruction.  This is
weaker than the exact lower-count comparison, but it is equivalent to the
upper-threshold endpoint-sign target by complement-count arithmetic. -/
def CompatibleSuccDegreeEndpointSignLowerNoGapStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      0 < f.eval x * g.eval x →
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≠ 3 ∧
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≠ 1

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

/-- Compatible-pair version of the forward gap-two endpoint-sign lemma. -/
theorem compatibleSuccDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  succDegree_eval_mul_pos_of_roots_gt_count_sub_eq_two
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hxf hxg hcount

/-- Compatible-pair version of the reverse gap-two endpoint-sign lemma. -/
theorem compatibleSuccDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcount : ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) :
    0 < f.eval x * g.eval x :=
  succDegree_eval_mul_pos_of_rev_roots_gt_count_sub_eq_two
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hxf hxg hcount

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

/-- Positive closed-segment members of a succ-degree pair keep the larger
endpoint degree. -/
theorem succDegree_closedSegment_natDegree_eq_right_of_pos
    {f g : ℝ[X]}
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ : 0 < β) :
    (C (1 - β) * f + C β * g).natDegree = g.natDegree := by
  have hleft_le : (C (1 - β) * f).natDegree ≤ f.natDegree :=
    Polynomial.natDegree_C_mul_le _ _
  have hright_deg : (C β * g).natDegree = g.natDegree := by rw [Polynomial.natDegree_C_mul hβ.ne']
  have hlt : (C (1 - β) * f).natDegree < (C β * g).natDegree := by
    rw [hright_deg, hdeg]
    exact Nat.lt_succ_of_le hleft_le
  exact
    (natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hlt
      (hasPosLeadingCoeff_C_mul hβ hg_pos)).trans hright_deg

/-- Positive closed-segment members of a succ-degree pair have positive
leading coefficient. -/
theorem succDegree_closedSegment_hasPosLeadingCoeff_of_pos
    {f g : ℝ[X]}
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ : 0 < β) :
    HasPosLeadingCoeff (C (1 - β) * f + C β * g) := by
  have hleft_le : (C (1 - β) * f).natDegree ≤ f.natDegree :=
    Polynomial.natDegree_C_mul_le _ _
  have hright_deg : (C β * g).natDegree = g.natDegree := by rw [Polynomial.natDegree_C_mul hβ.ne']
  have hlt : (C (1 - β) * f).natDegree < (C β * g).natDegree := by
    rw [hright_deg, hdeg]
    exact Nat.lt_succ_of_le hleft_le
  exact
    hasPosLeadingCoeff_add_of_natDegree_lt_right hlt
      (hasPosLeadingCoeff_C_mul hβ hg_pos)

/-- Positive closed-segment members of a compatible succ-degree pair are
nonzero and split. -/
theorem compatibleSuccDegree_closedSegment_isRealRooted_of_pos
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f + C β * g) ≠ 0 ∧
      (C (1 - β) * f + C β * g).Splits := by
  have hleft_nonneg : 0 ≤ 1 - β := by linarith
  rcases hcomp (1 - β) β hleft_nonneg hβ0.le with hzero | hrr
  · exact False.elim <|
      (succDegree_closedSegment_hasPosLeadingCoeff_of_pos hg_pos hdeg hβ0).ne_zero
        hzero
  · exact hrr

/-- Positive closed-segment members of a compatible succ-degree pair have
exactly the larger endpoint number of roots. -/
theorem compatibleSuccDegree_closedSegment_roots_card_eq_right_of_pos
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f + C β * g).roots.card = g.natDegree := by
  rw [card_roots_of_splits
    (compatibleSuccDegree_closedSegment_isRealRooted_of_pos
      hcomp hg_pos hdeg hβ0 hβ1).2]
  exact succDegree_closedSegment_natDegree_eq_right_of_pos hg_pos hdeg hβ0

/-- Positive closed-segment members of a compatible succ-degree pair have one
more root than the lower-degree endpoint. -/
theorem compatibleSuccDegree_closedSegment_roots_card_eq_succ_of_pos
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f + C β * g).roots.card = f.natDegree + 1 := by
  rw [compatibleSuccDegree_closedSegment_roots_card_eq_right_of_pos
    hcomp hg_pos hdeg hβ0 hβ1, hdeg]

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
pencil preserves the root multiset. -/
theorem closedSegment_roots_eq_add_right_of_lt_one
    {f g : ℝ[X]} {β : ℝ} (hβ : β < 1) :
    (C (1 - β) * f + C β * g).roots =
      (f + C (β / (1 - β)) * g).roots := by
  rw [closedSegment_eq_C_mul_add_right hβ,
    Polynomial.roots_C_mul _ (by linarith : 1 - β ≠ 0)]

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

private lemma div_one_sub_inj_of_lt_one {β γ : ℝ}
    (hβ : β < 1) (hγ : γ < 1)
    (h : β / (1 - β) = γ / (1 - γ)) :
    β = γ := by
  have hβne : 1 - β ≠ 0 := by linarith
  have hγne : 1 - γ ≠ 0 := by linarith
  have hmul : β * (1 - γ) = γ * (1 - β) :=
    (div_eq_div_iff hβne hγne).mp h
  linarith

/-- Positive interior closed-segment form of the no-common right-pencil
parameter formula. -/
theorem closedSegment_isRoot_iff_parameter_eq_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β x : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (C (1 - β) * f + C β * g).IsRoot x ↔
      β / (1 - β) = -f.eval x / g.eval x := by
  rw [closedSegment_isRoot_iff_add_right_of_lt_one hβ1]
  exact isRoot_add_right_iff_parameter_eq_of_no_common hno
    (div_pos hβ0 (sub_pos.mpr hβ1))

/-- Every interior closed-segment member of a no-common positive-combination
family has simple roots. -/
theorem PosComboRealRooted.hasSimpleRoots_closedSegment
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasSimpleRoots (C (1 - β) * f + C β * g) := by
  rw [closedSegment_eq_C_mul_add_right hβ1]
  exact
    (hfg.hasSimpleRoots_add_right hno (div_pos hβ0 (sub_pos.mpr hβ1))).C_mul
      (by linarith : 1 - β ≠ 0)

/-- A fixed threshold can be a root of a no-common closed-segment family for
at most one parameter below the right endpoint. -/
theorem closedSegment_parameter_unique_of_isRoot_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β γ x : ℝ}
    (hβ : β < 1) (hγ : γ < 1)
    (hrootβ : (C (1 - β) * f + C β * g).IsRoot x)
    (hrootγ : (C (1 - γ) * f + C γ * g).IsRoot x) :
    β = γ := by
  have hrootβ_right :
      (f + C (β / (1 - β)) * g).IsRoot x :=
    (closedSegment_isRoot_iff_add_right_of_lt_one hβ).mp hrootβ
  have hrootγ_right :
      (f + C (γ / (1 - γ)) * g).IsRoot x :=
    (closedSegment_isRoot_iff_add_right_of_lt_one hγ).mp hrootγ
  exact div_one_sub_inj_of_lt_one hβ hγ <|
    pencil_parameter_unique_of_isRoot_of_no_common hno hrootβ_right hrootγ_right

/-- A root of an interior no-common closed-segment member carries the same
endpoint nonvanishing, parameter formula, and simple-crossing derivative data
as the corresponding right-pencil member. -/
theorem PosComboRealRooted.root_crossing_data_closedSegment
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β x : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hroot : (C (1 - β) * f + C β * g).IsRoot x) :
    g.eval x ≠ 0 ∧ f.eval x ≠ 0 ∧
      β / (1 - β) = -f.eval x / g.eval x ∧
      (C (1 - β) * f + C β * g).derivative.eval x ≠ 0 := by
  have hμ_pos : 0 < β / (1 - β) := div_pos hβ0 (sub_pos.mpr hβ1)
  have hroot_right :
      (f + C (β / (1 - β)) * g).IsRoot x :=
    (closedSegment_isRoot_iff_add_right_of_lt_one hβ1).mp hroot
  rcases hfg.root_crossing_data_add_right hno hμ_pos hroot_right with
    ⟨hgx, hfx, hμ_eq, hder_right⟩
  refine ⟨hgx, hfx, hμ_eq, ?_⟩
  have hscale :
      (C (1 - β) * f + C β * g).derivative =
        C (1 - β) * (f + C (β / (1 - β)) * g).derivative := by
    rw [closedSegment_eq_C_mul_add_right hβ1, derivative_C_mul]
  intro hder
  apply hder_right
  have hscaled_eval :
      (1 - β) * (f + C (β / (1 - β)) * g).derivative.eval x = 0 := by
    rw [hscale] at hder
    simpa [hscale, eval_mul, eval_C] using hder
  exact (mul_eq_zero.mp hscaled_eval).resolve_left (by linarith : 1 - β ≠ 0)

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

/-- The change of variables `β = μ / (μ + 1)` preserves the root multiset
between a nonnegative right-pencil member and its closed-segment representative. -/
theorem closedSegment_roots_eq_add_right_of_nonneg
    {f g : ℝ[X]} {μ : ℝ} (hμ : 0 ≤ μ) :
    (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).roots =
      (f + C μ * g).roots := by
  have hden_pos : 0 < μ + 1 := by linarith
  have hβlt : μ / (μ + 1) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have hratio : (μ / (μ + 1)) / (1 - μ / (μ + 1)) = μ := by
    field_simp [hden_pos.ne']
    ring
  rw [closedSegment_roots_eq_add_right_of_lt_one hβlt, hratio]

/-- The change of variables `β = μ / (μ + 1)` preserves upper-threshold root
counts between a nonnegative right-pencil member and its closed-segment
representative. -/
theorem closedSegment_roots_gt_card_eq_add_right_of_nonneg
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ) :
    ((C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).roots.filter
      (x < ·)).card =
      ((f + C μ * g).roots.filter (x < ·)).card := by
  rw [closedSegment_roots_eq_add_right_of_nonneg (f := f) (g := g) hμ]

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

/-- Same-sign endpoint evaluations rule out nonnegative right-family roots at
that threshold. -/
theorem rightFamily_not_isRoot_of_eval_mul_pos
    {f g : ℝ[X]} {x μ : ℝ} (hμ : 0 ≤ μ)
    (hprod : 0 < f.eval x * g.eval x) :
    ¬ (f + C μ * g).IsRoot x := by
  intro hroot
  have hroot_eval : f.eval x + μ * g.eval x = 0 := by
    simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C] using hroot
  have hf_ne : f.eval x ≠ 0 := by
    intro hf
    rw [hf, zero_mul] at hprod
    linarith
  by_cases hf_pos : 0 < f.eval x
  · have hg_pos : 0 < g.eval x := by nlinarith
    have hpos : 0 < f.eval x + μ * g.eval x := by nlinarith
    linarith
  · have hf_neg : f.eval x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hf_pos) hf_ne
    have hg_neg : g.eval x < 0 := by nlinarith
    have hneg : f.eval x + μ * g.eval x < 0 := by nlinarith
    linarith

/-- If a common non-root threshold is never a root of the nonnegative
right-family, then the endpoint evaluations have the same sign. -/
theorem eval_mul_pos_of_no_rightFamily_isRoot
    {f g : ℝ[X]} {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    0 < f.eval x * g.eval x := by
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  have hgx_eval : g.eval x ≠ 0 := by
    intro hgx
    exact hxg (by simpa [Polynomial.IsRoot.def] using hgx)
  have hno_pos : ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x := by
    rintro ⟨μ, hμ, hroot⟩
    exact hno hμ.le hroot
  have hsign :
      (0 < f.eval x ↔ 0 < g.eval x) :=
    (not_exists_pos_isRoot_add_right_iff_eval_pos_iff hfx_eval hgx_eval).mp hno_pos
  rcases lt_or_gt_of_ne hfx_eval with hf_neg | hf_pos
  · have hg_neg : g.eval x < 0 := by
      by_contra hnot
      have hg_pos : 0 < g.eval x := lt_of_le_of_ne (le_of_not_gt hnot) hgx_eval.symm
      exact (not_lt_of_ge (le_of_lt hf_neg)) (hsign.mpr hg_pos)
    exact mul_pos_of_neg_of_neg hf_neg hg_neg
  · exact mul_pos hf_pos (hsign.mp hf_pos)

/-- If a common non-root threshold is never a root of the positive right-family,
then the endpoint evaluations have the same sign. -/
theorem eval_mul_pos_of_no_pos_rightFamily_isRoot
    {f g : ℝ[X]} {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ μ : ℝ, 0 < μ → ¬ (f + C μ * g).IsRoot x) :
    0 < f.eval x * g.eval x := by
  refine eval_mul_pos_of_no_rightFamily_isRoot hxf hxg ?_
  intro μ hμ
  by_cases hμ0 : μ = 0
  · subst μ
    simpa using hxf
  · exact hno μ (lt_of_le_of_ne hμ (Ne.symm hμ0))

/-- At a common non-root threshold, nonvanishing of the nonnegative right
family is equivalent to same-sign endpoint evaluations. -/
theorem no_rightFamily_isRoot_iff_eval_mul_pos
    {f g : ℝ[X]} {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) ↔
      0 < f.eval x * g.eval x :=
  ⟨eval_mul_pos_of_no_rightFamily_isRoot hxf hxg,
    fun hprod {_} hμ => rightFamily_not_isRoot_of_eval_mul_pos hμ hprod⟩

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
  have hseg_root : (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).IsRoot x := by
    exact (closedSegment_isRoot_iff_add_right_of_nonneg (f := f) (g := g)
      (x := x) hμ).2 hroot
  exact hseg hβ0 hβ1 hseg_root

/-- At a common non-root threshold, closed-segment nonvanishing is equivalent
to same-sign endpoint evaluations. -/
theorem closedSegment_forall_not_isRoot_iff_eval_mul_pos
    {f g : ℝ[X]} {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x) ↔
      0 < f.eval x * g.eval x := by
  constructor
  · intro hseg
    have hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x := by
      intro μ hμ
      exact closedSegment_not_isRoot_add_right_of_nonneg hμ hseg
    exact eval_mul_pos_of_no_rightFamily_isRoot hxf hxg hno
  · intro hprod β hβ0 hβ1
    exact closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 hprod

/-- The right-pencil no-gap-two theorem implies the closed-segment no-gap-two
theorem by the parameter change `β = μ / (μ + 1)`. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_rightFamily
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  exact hright hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
    (fun {_} hμ => closedSegment_not_isRoot_add_right_of_nonneg hμ hseg)

/-- The endpoint-sign no-gap-two theorem implies the right-family no-gap-two
theorem because the right-family no-root hypothesis is exactly same-sign
endpoint evaluation at a common non-root threshold. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeRightFamilyNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hno
  exact hsign hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
    (eval_mul_pos_of_no_rightFamily_isRoot hxf hxg hno)

/-- The right-family no-gap-two theorem implies the endpoint-sign no-gap-two
theorem because same-sign endpoint evaluations rule out nonnegative
right-family roots at the fixed threshold. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwo_of_rightFamily
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeEndpointSignNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  exact hright hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
    (fun {_} hμ => rightFamily_not_isRoot_of_eval_mul_pos hμ hprod)

/-- The right-family and endpoint-sign no-gap-two targets are equivalent. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwo_iff_endpointSign :
    CompatibleSuccDegreeRightFamilyNoGapTwoStatement ↔
      CompatibleSuccDegreeEndpointSignNoGapTwoStatement :=
  ⟨compatibleSuccDegreeEndpointSignNoGapTwo_of_rightFamily,
    compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign⟩

/-- The all-combinations target contains the signed right-pencil family. -/
theorem compatibleSuccDegreeSignedRightFamily_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreeSignedRightFamilyStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split μ
  simpa using hallTarget hcomp hf_pos hg_pos hdeg hf_split 1 μ

/-- The all-combinations target implies the negative right-pencil target. -/
theorem compatibleSuccDegreeNegativeRightFamily_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreeNegativeRightFamilyStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split μ _
  exact compatibleSuccDegreeSignedRightFamily_of_allCombo hallTarget
    hcomp hf_pos hg_pos hdeg hf_split μ

/-- The all-combinations target implies the nonnegative-coefficient negative
right-pencil target. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonneg_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreeNegativeRightFamilyNonnegStatement := by
  intro f g hcomp hf_pos hg_pos _ _ hdeg hf_split μ hμ
  exact compatibleSuccDegreeNegativeRightFamily_of_allCombo hallTarget
    hcomp hf_pos hg_pos hdeg hf_split μ hμ

/-- Degree-zero base case for the nonnegative-coefficient negative right-pencil
target.  If the lower-degree endpoint is constant, the pencil has degree at
most one for every parameter. -/
theorem compatibleSuccDegreeNegativeRightFamilyNonneg_of_natDegree_eq_zero
    {f g : ℝ[X]}
    (_hcomp : Compatible f g)
    (_hf_pos : HasPosLeadingCoeff f)
    (_hg_pos : HasPosLeadingCoeff g)
    (_hfnn : HasNonnegCoeffs f)
    (_hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (_hf_split : f.Splits)
    (hfdeg : f.natDegree = 0)
    (μ : ℝ) (_hμ : μ < 0) :
    (f + C μ * g).Splits := by
  apply Polynomial.Splits.of_natDegree_le_one
  calc
    (f + C μ * g).natDegree ≤ max f.natDegree (C μ * g).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ 1 := by
      have hmul : (C μ * g).natDegree ≤ g.natDegree :=
        Polynomial.natDegree_C_mul_le μ g
      rw [hdeg, hfdeg] at hmul
      rw [hfdeg]
      exact max_le (by norm_num) (by simpa using hmul)

/-- The signed right-pencil family gives the whole all-combinations target by
scaling every nonzero left coefficient to `1`. -/
theorem compatibleSuccDegreeAllCombo_of_signedRightFamily
    (hsigned : CompatibleSuccDegreeSignedRightFamilyStatement) :
    CompatibleSuccDegreeAllComboStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split α β
  by_cases hα : α = 0
  · have hfg : PosComboRealRooted f g :=
      hcomp.toPosComboRealRooted hf_pos hg_pos
    have hg_split : g.Splits :=
      (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
    simpa [hα] using (Polynomial.Splits.C (R := ℝ) β).mul hg_split
  · have hright : (f + C (β / α) * g).Splits :=
      hsigned hcomp hf_pos hg_pos hdeg hf_split (β / α)
    have hscale : C α * (f + C (β / α) * g) = C α * f + C β * g := by
      rw [mul_add]
      congr 1
      have hαβ : α * (β / α) = β := by field_simp [hα]
      calc
        C α * (C (β / α) * g) = C (α * (β / α)) * g := by grind
        _ = C β * g := by rw [hαβ]
    rw [← hscale]
    exact (Polynomial.Splits.C (R := ℝ) α).mul hright

/-- It is enough to prove the negative half of the right pencil: compatibility
already gives the nonnegative half. -/
theorem compatibleSuccDegreeSignedRightFamily_of_negativeRightFamily
    (hneg : CompatibleSuccDegreeNegativeRightFamilyStatement) :
    CompatibleSuccDegreeSignedRightFamilyStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split μ
  by_cases hμ : 0 ≤ μ
  · rcases hcomp 1 μ zero_le_one hμ with hzero | hrr
    · have htarget_zero : f + C μ * g = 0 := by simpa using hzero
      simp [htarget_zero]
    · simpa using hrr.2
  · exact hneg hcomp hf_pos hg_pos hdeg hf_split μ (lt_of_not_ge hμ)

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

/-- The coefficient-free negative right-pencil target reduces to the
nonnegative-coefficient target by translating both endpoints far enough that
their roots are nonpositive. -/
theorem compatibleSuccDegreeNegativeRightFamily_of_nonnegShift
    (hneg : CompatibleSuccDegreeNegativeRightFamilyNonnegStatement) :
    CompatibleSuccDegreeNegativeRightFamilyStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split μ hμ
  have hfg : PosComboRealRooted f g :=
    hcomp.toPosComboRealRooted hf_pos hg_pos
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  obtain ⟨rf, hrf⟩ := exists_root_upper_bound f
  obtain ⟨rg, hrg⟩ := exists_root_upper_bound g
  let r : ℝ := max rf rg
  let f' : ℝ[X] := f.comp (X + C r)
  let g' : ℝ[X] := g.comp (X + C r)
  have hcomp' : Compatible f' g' := by simpa [f', g'] using hcomp.comp_X_add_C r
  have hf'_pos : HasPosLeadingCoeff f' := by simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
  have hfnn : HasNonnegCoeffs f' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hf_split ?_
    grind
  have hgnn : HasNonnegCoeffs g' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hg_pos hg_split ?_
    grind
  have hdeg' : g'.natDegree = f'.natDegree + 1 := by
    simpa [f', g', Polynomial.natDegree_comp] using hdeg
  have hf'_split : f'.Splits :=
    (isRealRooted_comp_X_add_C hf_pos.ne_zero hf_split r).2
  have hshift : (f' + C μ * g').Splits :=
    hneg hcomp' hf'_pos hg'_pos hfnn hgnn hdeg' hf'_split μ hμ
  have htranslate :
      (f + C μ * g).comp (X + C r) = f' + C μ * g' := by
    simp [f', g']
  exact splits_of_comp_X_add_C_splits r (by simpa [htranslate] using hshift)

/-- The negative right-pencil target implies the all-combinations target. -/
theorem compatibleSuccDegreeAllCombo_of_negativeRightFamily
    (hneg : CompatibleSuccDegreeNegativeRightFamilyStatement) :
    CompatibleSuccDegreeAllComboStatement :=
  compatibleSuccDegreeAllCombo_of_signedRightFamily
    (compatibleSuccDegreeSignedRightFamily_of_negativeRightFamily hneg)

/-- The nonnegative-coefficient negative right-pencil target implies the
all-combinations target. -/
theorem compatibleSuccDegreeAllCombo_of_negativeRightFamily_nonnegShift
    (hneg : CompatibleSuccDegreeNegativeRightFamilyNonnegStatement) :
    CompatibleSuccDegreeAllComboStatement :=
  compatibleSuccDegreeAllCombo_of_negativeRightFamily
    (compatibleSuccDegreeNegativeRightFamily_of_nonnegShift hneg)

/-- The compatible succ-degree all-combinations target implies the forced
proper-position orientation, by Obreschkoff's converse and degree orientation.
-/
theorem compatibleSuccDegreePrec_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreePrecStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split
  have hall : AllComboRealRooted f g :=
    hallTarget hcomp hf_pos hg_pos hdeg hf_split
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
    hall.isRealRooted_right hg_pos.ne_zero
  have horient : Prec f g ∨ Prec g f :=
    prec_of_allComboRealRooted
      hf_pos.ne_zero hf_split hg_rr.1 hg_rr.2 hall (Or.inl hdeg.symm)
  exact prec_forward_of_orientation_of_succDegree hdeg horient

/-- The signed right-pencil target implies the forced succ-degree
orientation. -/
theorem compatibleSuccDegreePrec_of_signedRightFamily
    (hsigned : CompatibleSuccDegreeSignedRightFamilyStatement) :
    CompatibleSuccDegreePrecStatement :=
  compatibleSuccDegreePrec_of_allCombo
    (compatibleSuccDegreeAllCombo_of_signedRightFamily hsigned)

/-- The negative right-pencil target implies the forced succ-degree
orientation. -/
theorem compatibleSuccDegreePrec_of_negativeRightFamily
    (hneg : CompatibleSuccDegreeNegativeRightFamilyStatement) :
    CompatibleSuccDegreePrecStatement :=
  compatibleSuccDegreePrec_of_allCombo
    (compatibleSuccDegreeAllCombo_of_negativeRightFamily hneg)

/-- The nonnegative-coefficient negative right-pencil target implies the forced
succ-degree orientation. -/
theorem compatibleSuccDegreePrec_of_negativeRightFamily_nonnegShift
    (hneg : CompatibleSuccDegreeNegativeRightFamilyNonnegStatement) :
    CompatibleSuccDegreePrecStatement :=
  compatibleSuccDegreePrec_of_negativeRightFamily
    (compatibleSuccDegreeNegativeRightFamily_of_nonnegShift hneg)

/-- The no-common positive-combination orientation core implies the
coefficient-free compatible succ-degree orientation target.  Shared roots are
handled by the existing positive-combination common-root induction, and the
succ-degree hypothesis selects the forward orientation. -/
theorem compatibleSuccDegreePrec_of_noCommonOrientation
    (hstep : PosComboNoCommonOrientationStatement) :
    CompatibleSuccDegreePrecStatement := by
  intro f g hcomp hf_pos hg_pos hdeg _hf_split
  have hfg : PosComboRealRooted f g :=
    hcomp.toPosComboRealRooted hf_pos hg_pos
  have horient : Prec f g ∨ Prec g f :=
    PosComboRealRooted.prec_or_revPrec_of_posComboRealRooted_of_no_common
      (hstep := fun {f g} hfg hf_pos hg_pos hdeg_lo hdeg_hi hno =>
        hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno)
      hfg hf_pos hg_pos (by lia) (by lia)
  exact prec_forward_of_orientation_of_succDegree hdeg horient

/-- The exact lower-count endpoint comparison implies the lower-threshold
endpoint-sign exact gap obstruction. -/
theorem compatibleSuccDegreeEndpointSignLowerNoGap_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeEndpointSignLowerNoGapStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hgf :=
    hcount hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  constructor <;> intro hbad <;> linarith

/-- The lower-threshold endpoint-sign target implies the upper-threshold
endpoint-sign target by exact complement-count arithmetic. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwo_of_lower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeEndpointSignNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hg_split : g.Splits := (hcomp.isRealRooted_right hg_pos).2
  obtain ⟨hgf_ne3, hfg_ne1⟩ :=
    hlower hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  constructor
  · intro hcount
    exact hgf_ne3 <|
      (succDegree_roots_gt_count_sub_eq_two_iff_roots_le_rev_sub_eq_three
        hf_split hg_split hdeg x).mp hcount
  · intro hcount
    exact hfg_ne1 <|
      (succDegree_rev_roots_gt_count_sub_eq_two_iff_roots_le_sub_eq_one
        hf_split hg_split hdeg x).mp hcount

/-- The exact lower-count endpoint comparison implies the upper-threshold
endpoint-sign exact gap-two obstruction. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeEndpointSignNoGapTwoStatement :=
  compatibleSuccDegreeEndpointSignNoGapTwo_of_lower
    (compatibleSuccDegreeEndpointSignLowerNoGap_of_lowerCountEq hcount)

/-- The lower-threshold endpoint-sign target implies the right-family
no-gap-two theorem. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeRightFamilyNoGapTwoStatement :=
  compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lower hlower)

/-- The exact lower-count endpoint comparison implies the right-family
no-gap-two theorem. -/
theorem compatibleSuccDegreeRightFamilyNoGapTwo_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeRightFamilyNoGapTwoStatement :=
  compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq hcount)

/-- The endpoint-sign no-gap-two theorem implies the closed-segment
no-gap-two theorem. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSign
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  exact hsign hcomp hf_pos hg_pos hdeg hf_split x hxf hxg <|
    (closedSegment_forall_not_isRoot_iff_eval_mul_pos hxf hxg).mp hseg

/-- The closed-segment no-gap-two theorem implies the endpoint-sign
no-gap-two theorem because same-sign endpoint evaluations rule out
closed-segment roots at the fixed threshold. -/
theorem compatibleSuccDegreeEndpointSignNoGapTwo_of_closedSegment
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    CompatibleSuccDegreeEndpointSignNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  exact hclosed hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
    (fun {_} hβ0 hβ1 => closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 hprod)

/-- The closed-segment and endpoint-sign no-gap-two targets are equivalent. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_iff_endpointSign :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement ↔
      CompatibleSuccDegreeEndpointSignNoGapTwoStatement :=
  ⟨compatibleSuccDegreeEndpointSignNoGapTwo_of_closedSegment,
    compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSign⟩

/-- The lower-threshold endpoint-sign target implies the closed-segment
no-gap-two theorem. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lower hlower)

/-- The exact lower-count endpoint comparison implies the closed-segment
no-gap-two theorem. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement :=
  compatibleSuccDegreeClosedSegmentNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq hcount)

/-- Closed-segment endpoint count equality excludes both exact upper
root-count gaps of two. -/
theorem compatibleSuccDegreeClosedSegmentNoGapTwo_of_countEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    CompatibleSuccDegreeClosedSegmentNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hcard := hcount hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hcard_int :
      ((f.roots.filter (x < ·)).card : ℤ) =
        (g.roots.filter (x < ·)).card := by
    exact_mod_cast hcard
  constructor <;> intro hgap <;> linarith

/-- Closed-segment endpoint count equality implies the exact lower-threshold
endpoint-sign comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot x := by
    intro β hβ0 hβ1
    exact closedSegment_not_isRoot_of_eval_mul_pos hβ0 hβ1 hprod
  have hgt := hcount hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hg_split : g.Splits := (hcomp.isRealRooted_right hg_pos).2
  have hfpart := card_roots_filter_gt_add_le_of_splits hf_split x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg_split x
  have hgtZ :
      ((f.roots.filter (x < ·)).card : ℤ) =
        (g.roots.filter (x < ·)).card := by
    exact_mod_cast hgt
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) +
          (f.roots.filter (· ≤ x)).card =
        f.natDegree := by
    exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) +
          (g.roots.filter (· ≤ x)).card =
        g.natDegree := by
    exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = (f.natDegree : ℤ) + 1 := by exact_mod_cast hdeg
  linarith

/-- The exact lower-threshold endpoint-sign comparison implies closed-segment
endpoint count equality. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeClosedSegmentCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hprod : 0 < f.eval x * g.eval x :=
    (closedSegment_forall_not_isRoot_iff_eval_mul_pos hxf hxg).mp hseg
  have hle := hcount hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hg_split : g.Splits := (hcomp.isRealRooted_right hg_pos).2
  have hfpart := card_roots_filter_gt_add_le_of_splits hf_split x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg_split x
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) +
          (f.roots.filter (· ≤ x)).card =
        f.natDegree := by
    exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) +
          (g.roots.filter (· ≤ x)).card =
        g.natDegree := by
    exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = (f.natDegree : ℤ) + 1 := by exact_mod_cast hdeg
  have hgtZ :
      ((f.roots.filter (x < ·)).card : ℤ) =
        (g.roots.filter (x < ·)).card := by
    linarith
  exact_mod_cast hgtZ

/-- The closed-segment endpoint count-equality target is equivalent to the
exact lower-threshold endpoint-sign count target. -/
theorem compatibleSuccDegreeClosedSegmentCountEq_iff_lowerCountEq :
    CompatibleSuccDegreeClosedSegmentCountEqStatement ↔
      CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  ⟨compatibleSuccDegreeEndpointSignLowerCountEq_of_closedSegmentCountEq,
    compatibleSuccDegreeClosedSegmentCountEq_of_lowerCountEq⟩

/-- Closed-segment endpoint count equality gives interval count equality
between any two common non-root thresholds that are not crossed by the closed
segment.  This is the interval-count bookkeeping used in the
Chudnovsky--Seymour `3.3` route. -/
theorem compatibleSuccDegree_roots_Ioo_eq_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement)
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits)
    {a b : ℝ} (hab : a ≤ b)
    (hfa : ¬ f.IsRoot a) (hga : ¬ g.IsRoot a)
    (hfb : ¬ f.IsRoot b) (hgb : ¬ g.IsRoot b)
    (hsega : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot a)
    (hsegb : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ¬ (C (1 - β) * f + C β * g).IsRoot b) :
    (f.roots.filter (fun r => a < r ∧ r < b)).card =
      (g.roots.filter (fun r => a < r ∧ r < b)).card :=
  card_roots_filter_Ioo_eq_of_card_filter_gt_eq
    hf_pos.ne_zero hg_pos.ne_zero hab hfb hgb
    (hcount hcomp hf_pos hg_pos hdeg hf_split a hfa hga hsega)
    (hcount hcomp hf_pos hg_pos hdeg hf_split b hfb hgb hsegb)

/-- The closed-segment no-gap-two theorem implies the compatible exact
gap-two obstruction, since an assumed exact gap two supplies the required
closed-segment nonvanishing by the endpoint sign lemma. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
  constructor
  · intro hcount
    have hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x := by
      intro β hβ0 hβ1
      exact
        compatibleSuccDegree_closedSegment_not_isRoot_of_roots_gt_count_sub_eq_two
          hcomp hf_pos hg_pos hdeg hf_split hβ0 hβ1 hxf hxg hcount
    exact (hclosed hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg).1 hcount
  · intro hcount
    have hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x := by
      intro β hβ0 hβ1
      exact
        compatibleSuccDegree_closedSegment_not_isRoot_of_rev_roots_gt_count_sub_eq_two
          hcomp hf_pos hg_pos hdeg hf_split hβ0 hβ1 hxf hxg hcount
    exact (hclosed hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg).2 hcount

/-- A gap-at-most-two theorem plus the closed-segment no-gap-two theorem gives
the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_closedSegment
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_noGapTwo hle2
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment hclosed)

/-- The right-pencil no-gap-two theorem implies the compatible exact gap-two
obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_rightFamily
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment
    (compatibleSuccDegreeClosedSegmentNoGapTwo_of_rightFamily hright)

/-- The endpoint-sign no-gap-two theorem implies the compatible exact gap-two
obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_rightFamily
    (compatibleSuccDegreeRightFamilyNoGapTwo_of_endpointSign hsign)

/-- The lower-threshold endpoint-sign target implies the compatible exact
gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lower hlower)

/-- The exact lower-count endpoint comparison implies the compatible exact
gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq hcount)

/-- Closed-segment endpoint count equality implies the compatible exact
gap-two obstruction. -/
theorem compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNoGapTwoStatement :=
  compatibleSuccDegreeRootCountAboveNoGapTwo_of_closedSegment
    (compatibleSuccDegreeClosedSegmentNoGapTwo_of_countEq hcount)

/-- A gap-at-most-two theorem plus the right-pencil no-gap-two theorem gives
the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_rightFamily
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_noGapTwo hle2
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_rightFamily hright)

/-- A gap-at-most-two theorem plus the endpoint-sign no-gap-two theorem gives
the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSign
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_noGapTwo hle2
    (compatibleSuccDegreeRootCountAboveNoGapTwo_of_endpointSign hsign)

/-- A gap-at-most-two theorem plus the lower-threshold endpoint-sign target
gives the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSignLower
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSign hle2
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lower hlower)

/-- A gap-at-most-two theorem plus the exact lower-count endpoint comparison
gives the compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_lowerCountEq
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement :=
  compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_endpointSign hle2
    (compatibleSuccDegreeEndpointSignNoGapTwo_of_lowerCountEq hcount)

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

/-- If the threshold is never a root of a nonnegative right-pencil member, then
the reverse upper root-count difference has even parity. -/
theorem succDegree_even_rev_roots_gt_count_sub_of_no_rightFamily_isRoot
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    Even (((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card) := by
  have h := succDegree_even_roots_gt_count_sub_of_no_rightFamily_isRoot
    hf_pos hg_pos hfg hdeg hf_split hxf hxg hno
  simpa [sub_eq_add_neg, add_comm] using h.neg

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

/-- Compatible-pair version of
`succDegree_even_rev_roots_gt_count_sub_of_no_rightFamily_isRoot`. -/
theorem compatibleSuccDegree_even_rev_roots_gt_count_sub_of_no_rightFamily_isRoot
    {f g : ℝ[X]}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    Even (((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card) :=
  succDegree_even_rev_roots_gt_count_sub_of_no_rightFamily_isRoot
    hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
    hdeg hf_split hxf hxg hno

/-- Succ-degree right-pencil parity bridge for lower root counts. Since `g` has
one more root than `f`, the lower root-count difference has even parity exactly
when the right pencil crosses zero at the threshold. -/
theorem succDegree_even_roots_le_count_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  rw [even_int_nat_sub_iff_even_add]
  have hfpart := card_roots_filter_gt_add_le_of_splits hf_split x
  have hgpart :
      (g.roots.filter (x < ·)).card + (g.roots.filter (· ≤ x)).card =
        f.natDegree + 1 := by
    rw [card_roots_filter_gt_add_le_of_splits hg_split x, hdeg]
  exact (even_add_iff_odd_add_of_add_eq_succ hfpart hgpart).trans
    (sameDegree_odd_card_roots_gt_add_iff_exists_pos_isRoot_add_right
      hf_split hg_split hf_pos hg_pos hxf hxg)

/-- Succ-degree lower root-count parity in endpoint-sign form. -/
theorem succDegree_even_roots_le_count_sub_iff_eval_mul_neg
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Even (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) ↔ f.eval x * g.eval x < 0) := by
  have hfx_eval : f.eval x ≠ 0 := by
    intro hfx
    exact hxf (by simpa [Polynomial.IsRoot.def] using hfx)
  exact (succDegree_even_roots_le_count_sub_iff_exists_pos_isRoot_add_right
    hf_pos hg_pos hfg hdeg hf_split hxf hxg).trans
    (exists_pos_isRoot_add_right_iff_eval_mul_neg hfx_eval)

/-- The compatible succ-degree orientation target implies the exact
lower-count endpoint comparison.  The oriented `Prec` count bounds leave only
the cases `g_le - f_le = 0` and `g_le - f_le = 1`; same-sign endpoint
evaluations rule out the even zero case by the succ-degree lower-count parity
bridge. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_prec
    (hprecTarget : CompatibleSuccDegreePrecStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hprod
  have hprec : Prec f g :=
    hprecTarget hcomp hf_pos hg_pos hdeg hf_split
  obtain ⟨hfg_le, hgf_le⟩ :=
    succDegreeRootCountLowerOriented_of_prec hprec hdeg x
  have hnot_even :
      ¬ Even (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card) := by
    intro heven
    have hneg :=
      (succDegree_even_roots_le_count_sub_iff_eval_mul_neg
        hf_pos hg_pos (hcomp.toPosComboRealRooted hf_pos hg_pos)
        hdeg hf_split hxf hxg).mp heven
    linarith
  by_contra hne
  let d : ℤ :=
    ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    linarith
  have hd_le_one : d ≤ 1 := by
    dsimp [d]
    linarith
  have hd_ne_one : d ≠ 1 := by simpa [d] using hne
  have hd_le_zero : d ≤ 0 :=
    Int.lt_add_one_iff.mp (lt_of_le_of_ne hd_le_one hd_ne_one)
  have hd_zero : d = 0 := le_antisymm hd_le_zero hd_nonneg
  have hfg_zero :
      ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card = 0 := by
    dsimp [d] at hd_zero
    linarith
  exact hnot_even (by rw [hfg_zero]; norm_num)

/-- The compatible succ-degree all-combinations target implies the exact
lower-count endpoint comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_allCombo
    (hallTarget : CompatibleSuccDegreeAllComboStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_prec
    (compatibleSuccDegreePrec_of_allCombo hallTarget)

/-- The signed right-pencil target implies the exact lower-count endpoint
comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_signedRightFamily
    (hsigned : CompatibleSuccDegreeSignedRightFamilyStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_allCombo
    (compatibleSuccDegreeAllCombo_of_signedRightFamily hsigned)

/-- The negative right-pencil target implies the exact lower-count endpoint
comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_negativeRightFamily
    (hneg : CompatibleSuccDegreeNegativeRightFamilyStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_allCombo
    (compatibleSuccDegreeAllCombo_of_negativeRightFamily hneg)

/-- The nonnegative-coefficient negative right-pencil target implies the exact
lower-count endpoint comparison. -/
theorem compatibleSuccDegreeEndpointSignLowerCountEq_of_negativeRightFamily_nonnegShift
    (hneg : CompatibleSuccDegreeNegativeRightFamilyNonnegStatement) :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  compatibleSuccDegreeEndpointSignLowerCountEq_of_negativeRightFamily
    (compatibleSuccDegreeNegativeRightFamily_of_nonnegShift hneg)

end RealRooted
