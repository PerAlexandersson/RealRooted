/-
# Root-count combinatorics for common interleavers

Succ-degree root-count statements and generic threshold/list/derivative
combinatorics extracted from `RealRooted.CommonInterleaverTwo`.
-/
import RealRooted.Compatibility.Basic
import RealRooted.CommonInterleaver.SameDegreeRootCount
import RealRooted.CommonInterleaver.SuccDegreeEndpoint
import RealRooted.Derivative
import RealRooted.RootCountJump
import RealRooted.RootOrderBridge
import RealRooted.SuccDegreeRootCrossing

open Polynomial

noncomputable section

namespace RealRooted

/-- **Sub-statement B of milestone B2: descending-root crossing inequalities.**

Given the nonnegative positive-combination/no-common hypotheses at succ degree
and that `f` already splits, the descending root sequences of `f` and `g` weave
in the two clean crossing inequalities consumed by
`rootSlotInterval_inter_nonempty_of_crossing`. This is the genuine analytic
converse-Obreschkoff crossing content for the succ-degree case, now separated
from the proved combinatorial slot construction. -/
def PosComboNoCommonSuccDegreeRootCrossingNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0)

/-- **Analytic root-count formulation of the succ-degree root-crossing target.**

For a succ-degree positive-combination pair with no common roots, the lower
threshold root count for `f` should be at most the lower threshold root count
for `g`, and the count for `g` should exceed the count for `f` by at most two.
Equivalently, the numbers of roots strictly above a threshold differ by at most
one, with the extra `g` root accounted for. -/
def PosComboNoCommonSuccDegreeRootCountNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2

/-- **Upper-threshold version of the succ-degree root-count formulation.**

This is the form naturally suggested by the root-continuity proof route: the
numbers of roots strictly above each threshold differ by at most one. -/
def PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1

/-- Common-non-root version of the succ-degree upper root-count formulation. -/
def PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1

/-- Compatible-pair version of the succ-degree common-non-root upper
root-count leaf.  This strips the #42 target down to the Chudnovsky--Seymour
compatibility input, positive leading coefficients, the succ-degree condition,
and splitting of the lower-degree endpoint. -/
def CompatibleSuccDegreeRootCountAboveNonRootStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1

/-- Compatible-pair gap-at-most-two version of the succ-degree
common-non-root upper root-count leaf. -/
def CompatibleSuccDegreeRootCountAboveLeTwoStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 2

/-- Exact gap-two obstruction for the compatible succ-degree common-non-root
upper root-count leaf. -/
def CompatibleSuccDegreeRootCountAboveNoGapTwoStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    Compatible f g →
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    g.natDegree = f.natDegree + 1 →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≠ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≠ 2

/-- An integer bounded above by two but not equal to two is bounded above by one. -/
theorem int_le_one_of_le_two_ne_two {z : ℤ} (hzle : z ≤ 2) (hzne : z ≠ 2) :
    z ≤ 1 := by
  have hzlt : z < 2 := lt_of_le_of_ne hzle hzne
  exact Int.lt_add_one_iff.mp (by simpa using hzlt)

/-- A gap-at-most-two theorem plus exclusion of exact gap two gives the full
compatible succ-degree common-non-root upper root-count leaf. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_of_leTwo_of_noGapTwo
    (hle2 : CompatibleSuccDegreeRootCountAboveLeTwoStatement)
    (hgap : CompatibleSuccDegreeRootCountAboveNoGapTwoStatement) :
    CompatibleSuccDegreeRootCountAboveNonRootStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
  obtain ⟨hfg_le2, hgf_le2⟩ :=
    hle2 hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
  obtain ⟨hfg_ne2, hgf_ne2⟩ :=
    hgap hcomp hf_pos hg_pos hdeg hf_split x hxf hxg
  exact ⟨int_le_one_of_le_two_ne_two hfg_le2 hfg_ne2,
    int_le_one_of_le_two_ne_two hgf_le2 hgf_ne2⟩

/-- The compatible CS 3.4 root-count leaf implies the #42 positive-combo
succ-degree root-count leaf. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  intro f g hf_pos hg_pos _hfnn _hgnn hfg hdeg _hno hf_split x hxf hxg
  exact hcount
    (Compatible.of_posComboRealRooted_succDegree hfg hf_pos hg_pos hdeg hf_split)
    hf_pos hg_pos hdeg hf_split x hxf hxg

/-- Differentiating a succ-degree pair preserves the succ-degree relation,
provided the lower-degree endpoint has positive degree. -/
theorem succDegree_derivative_natDegree_eq
    {f g : ℝ[X]} (hdeg : g.natDegree = f.natDegree + 1)
    (hfdeg : f.natDegree ≠ 0) :
    g.derivative.natDegree = f.derivative.natDegree + 1 := by
  rw [f.natDegree_derivative, g.natDegree_derivative, hdeg]
  lia

/-- Applying the compatible succ-degree root-count theorem to derivatives. -/
theorem compatibleSuccDegreeRootCountAboveNonRoot_derivative
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement)
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : 2 ≤ f.natDegree) :
    ∀ x : ℝ, ¬ f.derivative.IsRoot x → ¬ g.derivative.IsRoot x →
      ((f.derivative.roots.filter (x < ·)).card : ℤ) -
          (g.derivative.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.derivative.roots.filter (x < ·)).card : ℤ) -
          (f.derivative.roots.filter (x < ·)).card ≤ 1 := by
  have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  have hg'_pos : HasPosLeadingCoeff g.derivative :=
    hg_pos.derivative (by rw [hdeg]; lia)
  have hdeg' : g.derivative.natDegree = f.derivative.natDegree + 1 :=
    succDegree_derivative_natDegree_eq hdeg (by lia)
  have hf'_split : f.derivative.Splits :=
    (derivative_interlaces hf_split hfdeg).2.1.2
  exact hcount hcomp.derivative hf'_pos hg'_pos hdeg' hf'_split

/-- Derivative application of the compatible succ-degree root-count theorem,
promoted from common non-root thresholds to all thresholds. -/
theorem compatibleSuccDegreeRootCountAbove_derivative
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement)
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : 2 ≤ f.natDegree) :
    ∀ x : ℝ,
      ((f.derivative.roots.filter (x < ·)).card : ℤ) -
          (g.derivative.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.derivative.roots.filter (x < ·)).card : ℤ) -
          (f.derivative.roots.filter (x < ·)).card ≤ 1 := by
  have hf'_ne : f.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (by lia)
  have hg'_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by rw [hdeg]; lia)
  exact rootCountAbove_diff_le_one_of_nonRoot_isRoot hf'_ne hg'_ne
    (compatibleSuccDegreeRootCountAboveNonRoot_derivative
      hcount hcomp hf_pos hg_pos hdeg hf_split hfdeg)

/-- Partition roots of a splitting polynomial by a threshold. -/
theorem card_roots_filter_gt_add_le_of_splits {p : ℝ[X]} (hp : p.Splits)
    (x : ℝ) :
    (p.roots.filter (x < ·)).card + (p.roots.filter (· ≤ x)).card =
      p.natDegree := by
  have hcompl :
      p.roots.filter (· ≤ x) = p.roots.filter (fun r => ¬ x < r) := by
    apply Multiset.filter_congr
    intro r _
    exact ⟨fun h => not_lt.mpr h, fun h => not_lt.mp h⟩
  rw [hcompl, ← Multiset.card_add, Multiset.filter_add_not,
    card_roots_of_splits hp]

/-- At a fixed threshold, same-degree upper common-non-root bounds are
equivalent to the lower common-non-root bounds. -/
theorem sameDegreeRootCountAbove_nonRoot_iff_rootCount_nonRoot_pointwise
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree) (x : ℝ) :
    (((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
        ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1)
      ↔
    (((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
        ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 1) := by
  have hfpart := card_roots_filter_gt_add_le_of_splits hf x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg x
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) + (f.roots.filter (· ≤ x)).card =
        f.natDegree := by exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) + (g.roots.filter (· ≤ x)).card =
        g.natDegree := by exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = f.natDegree := by exact_mod_cast hdeg
  constructor <;> · rintro ⟨h1, h2⟩; constructor <;> lia

/-- The same-degree upper common-non-root root-count target is equivalent to
the lower common-non-root root-count target. -/
theorem posComboNoCommonSameDegreeRootCountAboveNonRoot_iff_rootCountNonRoot :
    PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement ↔
      PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement := by
  constructor
  · intro hcount f g hf_pos hg_pos hfnn hgnn hfg hdeg hno x hxf hxg
    have hf_split : f.Splits :=
      (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    have hg_split : g.Splits :=
      (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    exact (sameDegreeRootCountAbove_nonRoot_iff_rootCount_nonRoot_pointwise
      hf_split hg_split hdeg x).mp
      (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno x hxf hxg)
  · intro hcount f g hf_pos hg_pos hfnn hgnn hfg hdeg hno x hxf hxg
    have hf_split : f.Splits :=
      (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    have hg_split : g.Splits :=
      (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    exact (sameDegreeRootCountAbove_nonRoot_iff_rootCount_nonRoot_pointwise
      hf_split hg_split hdeg x).mpr
      (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno x hxf hxg)

/-- The same-degree lower common-non-root target implies the full
upper-threshold same-degree root-count target. -/
theorem posComboNoCommonSameDegreeRootCountAbove_of_rootCountNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSameDegreeRootCountAboveNonnegStatement :=
  posComboNoCommonSameDegreeRootCountAbove_of_nonRoot
    (posComboNoCommonSameDegreeRootCountAboveNonRoot_iff_rootCountNonRoot.mpr
      hcount)

/-- The same-degree upper common-non-root target implies the full
lower-threshold same-degree root-count target. -/
theorem posComboNoCommonSameDegreeRootCount_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSameDegreeRootCountNonnegStatement :=
  posComboNoCommonSameDegreeRootCount_of_nonRoot
    (posComboNoCommonSameDegreeRootCountAboveNonRoot_iff_rootCountNonRoot.mp
      hcount)

/-- Oriented same-cardinality root counts: the lower-threshold comparison
`f` against `g` is equivalent to the opposite upper-threshold comparison.

This form is useful when a same-degree comparison is later used after a `divX`
step: the lower count of `f` is bounded by the lower count of `g` exactly when
the upper count of `g` is bounded by the upper count of `f`. -/
theorem sameDegreeRootCountAbove_oriented_iff_rootCount_oriented_pointwise
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree) (x : ℝ) :
    (((g.roots.filter (x < ·)).card : ℤ) ≤ (f.roots.filter (x < ·)).card ∧
        ((f.roots.filter (x < ·)).card : ℤ) ≤
          (g.roots.filter (x < ·)).card + 1)
      ↔
    (((f.roots.filter (· ≤ x)).card : ℤ) ≤ (g.roots.filter (· ≤ x)).card ∧
        ((g.roots.filter (· ≤ x)).card : ℤ) ≤
          (f.roots.filter (· ≤ x)).card + 1) := by
  have hfpart := card_roots_filter_gt_add_le_of_splits hf x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg x
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) + (f.roots.filter (· ≤ x)).card =
        f.natDegree := by exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) + (g.roots.filter (· ≤ x)).card =
        g.natDegree := by exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = f.natDegree := by exact_mod_cast hdeg
  constructor <;> · rintro ⟨h1, h2⟩; constructor <;> lia

/-- Succ-degree oriented root counts: the lower-threshold comparison is
equivalent to the same upper-threshold comparison.

The extra degree of `g` appears on both sides of the complement calculation, so
the orientation is unchanged when passing from roots at or below the threshold
to roots strictly above it. -/
theorem succDegreeRootCountAbove_oriented_iff_rootCount_oriented_pointwise
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (x : ℝ) :
    (((f.roots.filter (x < ·)).card : ℤ) ≤ (g.roots.filter (x < ·)).card ∧
        ((g.roots.filter (x < ·)).card : ℤ) ≤
          (f.roots.filter (x < ·)).card + 1)
      ↔
    (((f.roots.filter (· ≤ x)).card : ℤ) ≤ (g.roots.filter (· ≤ x)).card ∧
        ((g.roots.filter (· ≤ x)).card : ℤ) ≤
          (f.roots.filter (· ≤ x)).card + 1) := by
  have hfpart := card_roots_filter_gt_add_le_of_splits hf x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg x
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) + (f.roots.filter (· ≤ x)).card =
        f.natDegree := by exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) + (g.roots.filter (· ≤ x)).card =
        g.natDegree := by exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = (f.natDegree : ℤ) + 1 := by exact_mod_cast hdeg
  constructor <;> · rintro ⟨h1, h2⟩; constructor <;> lia

/-- Common-non-root version of the succ-degree lower root-count formulation. -/
def PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2

/-- At a fixed threshold, the succ-degree upper common-non-root bounds are
equivalent to the lower common-non-root bounds. -/
theorem succDegreeRootCountAbove_nonRoot_iff_rootCount_nonRoot_pointwise
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (x : ℝ) :
    (((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
        ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1)
      ↔
    (((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
        ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 2) := by
  have hfpart := card_roots_filter_gt_add_le_of_splits hf x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg x
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) + (f.roots.filter (· ≤ x)).card =
        f.natDegree := by exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) + (g.roots.filter (· ≤ x)).card =
        g.natDegree := by exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = (f.natDegree : ℤ) + 1 := by exact_mod_cast hdeg
  constructor <;> · rintro ⟨h1, h2⟩; constructor <;> lia

/-- In the succ-degree setting, an exact forward upper-count gap of two is
equivalent to an exact reverse lower-count gap of three. -/
theorem succDegree_roots_gt_count_sub_eq_two_iff_roots_le_rev_sub_eq_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (x : ℝ) :
    (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card = 2) ↔
      (((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card = 3) := by
  have hfpart := card_roots_filter_gt_add_le_of_splits hf x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg x
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) + (f.roots.filter (· ≤ x)).card =
        f.natDegree := by exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) + (g.roots.filter (· ≤ x)).card =
        g.natDegree := by exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = (f.natDegree : ℤ) + 1 := by exact_mod_cast hdeg
  constructor <;> intro h <;> lia

/-- In the succ-degree setting, an exact reverse upper-count gap of two is
equivalent to the lower-degree endpoint having exactly one more lower root. -/
theorem succDegree_rev_roots_gt_count_sub_eq_two_iff_roots_le_sub_eq_one
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) (x : ℝ) :
    (((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card = 2) ↔
      (((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card = 1) := by
  have hfpart := card_roots_filter_gt_add_le_of_splits hf x
  have hgpart := card_roots_filter_gt_add_le_of_splits hg x
  have hfpartZ :
      ((f.roots.filter (x < ·)).card : ℤ) + (f.roots.filter (· ≤ x)).card =
        f.natDegree := by exact_mod_cast hfpart
  have hgpartZ :
      ((g.roots.filter (x < ·)).card : ℤ) + (g.roots.filter (· ≤ x)).card =
        g.natDegree := by exact_mod_cast hgpart
  have hdegZ : (g.natDegree : ℤ) = (f.natDegree : ℤ) + 1 := by exact_mod_cast hdeg
  constructor <;> intro h <;> lia

/-- The succ-degree upper common-non-root root-count target is equivalent to
the lower common-non-root root-count target. -/
theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_iff_rootCountNonRoot :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement ↔
      PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement := by
  constructor
  · intro hcount f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split x hxf hxg
    have hg_split : g.Splits :=
      (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
    exact (succDegreeRootCountAbove_nonRoot_iff_rootCount_nonRoot_pointwise
      hf_split hg_split hdeg x).mp
      (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split x hxf hxg)
  · intro hcount f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split x hxf hxg
    have hg_split : g.Splits :=
      (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
    exact (succDegreeRootCountAbove_nonRoot_iff_rootCount_nonRoot_pointwise
      hf_split hg_split hdeg x).mpr
      (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split x hxf hxg)

/-- Root-count bridge for the succ-degree root-crossing target.

The asymmetric lower-threshold count inequalities encode the fact that `g`
has one extra root.  They imply exactly the two descending-root crossing
inequalities consumed by the succ-degree slot construction. -/
theorem succDegreeRootCrossing_of_rootCount
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcount : ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree + 1 := by
    rw [card_roots_of_splits hg, hdeg]
  exact succRootCrossing_of_count_le_two hMcard hNcard hcount

/-- Converse root-count bridge from successor-degree descending-root crossing
to the asymmetric lower-threshold formulation. -/
theorem succDegreeRootCount_of_rootCrossing
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcross :
      (∀ j, 1 ≤ j → j ≤ f.natDegree →
          (rootSeqDesc g).getD j 0 ≤
            (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
          (rootSeqDesc f).getD j 0 ≤
            (rootSeqDesc g).getD (j - 1) 0)) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
          (f.roots.filter (· ≤ x)).card ≤ 2 := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree + 1 := by
    rw [card_roots_of_splits hg, hdeg]
  simpa [rootSeqDesc] using
    (count_le_two_of_succRootCrossing (M := f.roots) (N := g.roots)
      hMcard hNcard hcross)

/-- Root-count bridge from the upper-threshold formulation to the succ-degree
root-crossing target. -/
theorem succDegreeRootCrossing_of_rootCountAbove
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcount : ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    (∀ j, 1 ≤ j → j ≤ f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree + 1 := by
    rw [card_roots_of_splits hg, hdeg]
  exact succRootCrossing_of_count_gt_diff_le_one hMcard hNcard hcount

/-- Convert the upper-threshold succ-degree root-count formulation into the
lower-threshold formulation. -/
theorem succDegreeRootCount_of_rootCountAbove
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcount : ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree + 1 := by
    rw [card_roots_of_splits hg, hdeg]
  exact count_le_two_of_count_gt_diff_le_one hMcard hNcard hcount

/-- Convert the lower-threshold succ-degree root-count formulation into the
upper-threshold formulation. -/
theorem succDegreeRootCountAbove_of_rootCount
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcount : ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  have hMcard : f.roots.card = f.natDegree := card_roots_of_splits hf
  have hNcard : g.roots.card = f.natDegree + 1 := by
    rw [card_roots_of_splits hg, hdeg]
  exact count_gt_diff_le_one_of_count_le_two hMcard hNcard hcount

/-- If every entry of a list lies strictly above `x`, then filtering by
`x < ·` keeps all entries. -/
private lemma filter_gt_length_eq_of_all (l : List ℝ) (x : ℝ)
    (h : ∀ a ∈ l, x < a) :
    (l.filter (fun y => decide (x < y))).length = l.length := by
  rw [List.filter_eq_self.mpr]
  intro a ha
  exact decide_eq_true (h a ha)

/-- In a sorted increasing cons list whose head lies strictly above `x`, every
entry lies strictly above `x`. -/
private lemma all_gt_of_sorted_head {a : ℝ} {l : List ℝ} {x : ℝ}
    (hsorted : (a :: l).Pairwise (· ≤ ·)) (hx : x < a) :
    ∀ b ∈ (a :: l), x < b := by
  intro b hb
  rw [List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact hx
  · exact lt_of_lt_of_le hx ((List.pairwise_cons.mp hsorted).1 b hb)

/-- Core combinatorial count bound for differ-by-one list interlacing.

If sorted lists `ss` and `rs` interlace in the differ-by-one pattern, then the
numbers of entries strictly above a threshold differ by at most one, with `rs`
never below `ss`. -/
private lemma interlaces_filter_gt_length_bounds :
    ∀ (ss rs : List ℝ) (x : ℝ),
      ss.Pairwise (· ≤ ·) → rs.Pairwise (· ≤ ·) →
      ss.length + 1 = rs.length → ListInterlaces ss rs →
      (ss.filter (fun y => decide (x < y))).length
          ≤ (rs.filter (fun y => decide (x < y))).length ∧
      (rs.filter (fun y => decide (x < y))).length
          ≤ (ss.filter (fun y => decide (x < y))).length + 1
  | [], [], _, _, _, hlen, _ => by simp at hlen
  | [], [r], x, _, _, _, _ => by
      simp only [List.filter_nil, List.length_nil]
      refine ⟨Nat.zero_le _, ?_⟩
      exact List.length_filter_le (fun y => decide (x < y)) [r]
  | [], _ :: _ :: _, _, _, _, _, hint => by simp [ListInterlaces] at hint
  | _ :: _, [], _, _, _, _, hint => by simp [ListInterlaces] at hint
  | _ :: _, [_], _, _, _, hlen, _ => by simp at hlen
  | s :: sst, r₁ :: r₂ :: rs, x, hss, hrs, hlen, hint => by
      obtain ⟨hr₁s, hsr₂, htail⟩ := hint
      have hss_tl : sst.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hss).2
      have hrs_tl : (r₂ :: rs).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hrs).2
      have hlen' : sst.length + 1 = (r₂ :: rs).length := by
        simp only [List.length_cons] at hlen ⊢
        lia
      obtain ⟨IH1, IH2⟩ :=
        interlaces_filter_gt_length_bounds sst (r₂ :: rs) x hss_tl hrs_tl hlen' htail
      set p : ℝ → Bool := fun y => decide (x < y) with hp
      by_cases hr₁ : x < r₁
      · have hs : x < s := lt_of_lt_of_le hr₁ hr₁s
        rw [List.filter_cons_of_pos (by simp [hp, hs]),
          List.filter_cons_of_pos (by simp [hp, hr₁]), List.length_cons, List.length_cons]
        lia
      · by_cases hs : x < s
        · have hs_all : ∀ b ∈ (s :: sst), x < b := all_gt_of_sorted_head hss hs
          have hr₂ : x < r₂ := lt_of_lt_of_le hs hsr₂
          have hr_all : ∀ b ∈ (r₂ :: rs), x < b := all_gt_of_sorted_head hrs_tl hr₂
          have hsfull : ((s :: sst).filter p).length = (s :: sst).length :=
            filter_gt_length_eq_of_all _ x hs_all
          have hrfull : ((r₂ :: rs).filter p).length = (r₂ :: rs).length :=
            filter_gt_length_eq_of_all _ x hr_all
          have hRHS : ((r₁ :: r₂ :: rs).filter p).length =
              ((r₂ :: rs).filter p).length := by
            rw [List.filter_cons_of_neg (by
              rw [hp]
              simp only [decide_eq_true_eq]
              exact hr₁)]
          rw [hRHS, hsfull, hrfull, List.length_cons, List.length_cons]
          rw [List.length_cons] at hlen'
          lia
        · rw [List.filter_cons_of_neg (by
              rw [hp]
              simp only [decide_eq_true_eq]
              exact hs),
            List.filter_cons_of_neg (by
              rw [hp]
              simp only [decide_eq_true_eq]
              exact hr₁)]
          exact ⟨IH1, IH2⟩

/-- Lower-threshold companion of `interlaces_filter_gt_length_bounds`.

If sorted lists `ss` and `rs` interlace in the differ-by-one pattern, then the
numbers of entries at or below a threshold differ by at most one, with `rs`
never below `ss`. -/
private lemma interlaces_filter_le_length_bounds :
    ∀ (ss rs : List ℝ) (x : ℝ),
      ss.Pairwise (· ≤ ·) → rs.Pairwise (· ≤ ·) →
      ss.length + 1 = rs.length → ListInterlaces ss rs →
      (ss.filter (fun y => decide (y ≤ x))).length
          ≤ (rs.filter (fun y => decide (y ≤ x))).length ∧
      (rs.filter (fun y => decide (y ≤ x))).length
          ≤ (ss.filter (fun y => decide (y ≤ x))).length + 1
  | [], [], _, _, _, hlen, _ => by simp at hlen
  | [], [r], x, _, _, _, _ => by
      simp only [List.filter_nil, List.length_nil]
      refine ⟨Nat.zero_le _, ?_⟩
      exact List.length_filter_le (fun y => decide (y ≤ x)) [r]
  | [], _ :: _ :: _, _, _, _, _, hint => by simp [ListInterlaces] at hint
  | _ :: _, [], _, _, _, _, hint => by simp [ListInterlaces] at hint
  | _ :: _, [_], _, _, _, hlen, _ => by simp at hlen
  | s :: sst, r₁ :: r₂ :: rs, x, hss, hrs, hlen, hint => by
      obtain ⟨hr₁s, hsr₂, htail⟩ := hint
      have hss_tl : sst.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hss).2
      have hrs_tl : (r₂ :: rs).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hrs).2
      have hlen' : sst.length + 1 = (r₂ :: rs).length := by
        simp only [List.length_cons] at hlen ⊢
        lia
      obtain ⟨IH1, IH2⟩ :=
        interlaces_filter_le_length_bounds sst (r₂ :: rs) x hss_tl hrs_tl hlen' htail
      set p : ℝ → Bool := fun y => decide (y ≤ x) with hp
      by_cases hs : s ≤ x
      · have hr₁ : r₁ ≤ x := le_trans hr₁s hs
        rw [List.filter_cons_of_pos (by simpa [hp] using hs),
          List.filter_cons_of_pos (by simpa [hp] using hr₁)]
        simp only [List.length_cons]
        exact ⟨by lia, by lia⟩
      · have hxs : x < s := lt_of_not_ge hs
        have hsst_all : ∀ b ∈ sst, x < b := fun b hb =>
          lt_of_lt_of_le hxs ((List.pairwise_cons.mp hss).1 b hb)
        have hr₂ : x < r₂ := lt_of_lt_of_le hxs hsr₂
        have hr_all : ∀ b ∈ (r₂ :: rs), x < b := all_gt_of_sorted_head hrs_tl hr₂
        have hsst0 : (sst.filter p).length = 0 := by
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro a ha
          simp only [hp, decide_eq_true_eq]
          exact not_le.mpr (hsst_all a ha)
        have hr0 : ((r₂ :: rs).filter p).length = 0 := by
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro a ha
          simp only [hp, decide_eq_true_eq]
          exact not_le.mpr (hr_all a ha)
        rw [List.filter_cons_of_neg (by simpa [hp] using hs)]
        by_cases hr₁ : r₁ ≤ x
        · rw [List.filter_cons_of_pos (by simpa [hp] using hr₁)]
          simp only [List.length_cons, hsst0, hr0]
          exact ⟨by lia, by lia⟩
        · rw [List.filter_cons_of_neg (by simpa [hp] using hr₁)]
          simp only [hsst0, hr0]
          exact ⟨by lia, by lia⟩

/-- Core combinatorial oriented count bound for same-degree list alternation.

If sorted lists `ss` and `rs` alternate in the same-degree pattern, then at any
threshold `rs` has at most as many entries at or below it as `ss`, and `ss` has
at most one more than `rs`. -/
private lemma alternates_filter_le_length_bounds :
    ∀ (ss rs : List ℝ) (x : ℝ),
      ss.Pairwise (· ≤ ·) → rs.Pairwise (· ≤ ·) →
      ss.length = rs.length → ListAlternates ss rs →
      (rs.filter (fun y => decide (y ≤ x))).length
          ≤ (ss.filter (fun y => decide (y ≤ x))).length ∧
      (ss.filter (fun y => decide (y ≤ x))).length
          ≤ (rs.filter (fun y => decide (y ≤ x))).length + 1
  | [], [], _, _, _, _, _ => by simp
  | [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _ => by simp at hlen
  | s :: sst, r :: rs, x, hss, hrs, hlen, halt => by
      obtain ⟨hsr, htail⟩ := halt
      have hss_tl : sst.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hss).2
      have hlen' : sst.length + 1 = (r :: rs).length := by
        simp only [List.length_cons] at hlen ⊢
        lia
      obtain ⟨IH1, IH2⟩ :=
        interlaces_filter_le_length_bounds sst (r :: rs) x hss_tl hrs hlen' htail
      set p : ℝ → Bool := fun y => decide (y ≤ x) with hp
      by_cases hs : s ≤ x
      · have hs_len :
            ((s :: sst).filter p).length = (sst.filter p).length + 1 := by
          rw [List.filter_cons_of_pos (l := sst) (a := s) (p := p)
            (by simpa [hp] using hs)]
          rfl
        rw [hs_len]
        exact ⟨IH2, by simpa using Nat.succ_le_succ IH1⟩
      · have hxs : x < s := lt_of_not_ge hs
        have hsst_all : ∀ b ∈ sst, x < b := fun b hb =>
          lt_of_lt_of_le hxs ((List.pairwise_cons.mp hss).1 b hb)
        have hr : x < r := lt_of_lt_of_le hxs hsr
        have hr_all : ∀ b ∈ (r :: rs), x < b := all_gt_of_sorted_head hrs hr
        have hsst0 : (sst.filter p).length = 0 := by
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro a ha
          simp only [hp, decide_eq_true_eq]
          exact not_le.mpr (hsst_all a ha)
        have hr0 : ((r :: rs).filter p).length = 0 := by
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro a ha
          simp only [hp, decide_eq_true_eq]
          exact not_le.mpr (hr_all a ha)
        have hs_len :
            ((s :: sst).filter p).length = (sst.filter p).length := by
          rw [List.filter_cons_of_neg (l := sst) (a := s) (p := p)
            (by simpa [hp] using hs)]
        rw [hs_len, hsst0, hr0]
        exact ⟨by lia, by lia⟩

/-- `Prec`-to-root-count bridge in upper-threshold form.

For splitting real polynomials `f, g` with `g.natDegree = f.natDegree + 1`,
the interlacing relation `Prec f g` forces the succ-degree upper-threshold
root-count inequalities: the numbers of roots strictly above each threshold
differ by at most one in each direction. -/
theorem succDegreeRootCountAbove_of_prec
    {f g : ℝ[X]} (hprec : Prec f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  obtain ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := hprec
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have hlen : ss.length + 1 = rs.length := by rw [hss_len, hrs_len, hdeg]
  have hint : ListInterlaces ss rs := by
    rcases hshape with ⟨_, hi⟩ | ⟨hbad, _⟩
    · exact hi
    · exfalso
      rw [hss_len, hrs_len, hdeg] at hbad
      lia
  intro x
  obtain ⟨B1, B2⟩ := interlaces_filter_gt_length_bounds ss rs x hss hrs hlen hint
  have hfcard : (f.roots.filter (x < ·)).card =
      (ss.filter (fun y => decide (x < y))).length := by
    rw [← hss_eq, Multiset.filter_coe, Multiset.coe_card]
  have hgcard : (g.roots.filter (x < ·)).card =
      (rs.filter (fun y => decide (x < y))).length := by
    rw [← hrs_eq, Multiset.filter_coe, Multiset.coe_card]
  rw [hfcard, hgcard]
  constructor <;> lia

/-- Rolle root-count bound in upper-threshold form.

For a splitting real polynomial of degree at least two, the numbers of roots of
`p` and `p.derivative` strictly above any threshold differ by at most one. -/
theorem rootCountAbove_derivative_diff_le_one_of_splits
    {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    ∀ x : ℝ,
      ((p.derivative.roots.filter (x < ·)).card : ℤ) -
          (p.roots.filter (x < ·)).card ≤ 1 ∧
      ((p.roots.filter (x < ·)).card : ℤ) -
          (p.derivative.roots.filter (x < ·)).card ≤ 1 := by
  have hprec : Prec p.derivative p := (derivative_interlaces hp hdeg).toPrec
  have hdeg' : p.natDegree = p.derivative.natDegree + 1 := by
    rw [p.natDegree_derivative]
    lia
  exact succDegreeRootCountAbove_of_prec hprec hdeg'

/-- `Prec`-to-root-count bridge in lower-threshold form. -/
theorem succDegreeRootCount_of_prec
    {f g : ℝ[X]} (hprec : Prec f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 :=
  succDegreeRootCount_of_rootCountAbove hprec.1.2 hprec.2.1.2 hdeg
    (succDegreeRootCountAbove_of_prec hprec hdeg)

/-- Rolle root-count bound in lower-threshold form.

For a splitting real polynomial of degree at least two, every threshold contains
at least as many roots of `p` as roots of `p.derivative`, but no more than two
extra in the succ-degree convention. -/
theorem rootCount_derivative_diff_le_two_of_splits
    {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    ∀ x : ℝ,
      ((p.derivative.roots.filter (· ≤ x)).card : ℤ) -
          (p.roots.filter (· ≤ x)).card ≤ 0 ∧
      ((p.roots.filter (· ≤ x)).card : ℤ) -
          (p.derivative.roots.filter (· ≤ x)).card ≤ 2 := by
  have hprec : Prec p.derivative p := (derivative_interlaces hp hdeg).toPrec
  have hdeg' : p.natDegree = p.derivative.natDegree + 1 := by
    rw [p.natDegree_derivative]
    lia
  exact succDegreeRootCount_of_prec hprec hdeg'

/-- Tight oriented lower-threshold `Prec`-to-root-count bridge for the
differ-by-one case.

If `p ≺ q` and `q` has one more root than `p`, then every lower threshold
contains at least as many roots of `q` as roots of `p`, but at most one more. -/
theorem succDegreeRootCountLowerOriented_of_prec
    {p q : ℝ[X]} (hprec : Prec p q)
    (hdeg : q.natDegree = p.natDegree + 1) :
    ∀ x : ℝ,
      ((p.roots.filter (· ≤ x)).card : ℤ) ≤ (q.roots.filter (· ≤ x)).card ∧
      ((q.roots.filter (· ≤ x)).card : ℤ) ≤
        (p.roots.filter (· ≤ x)).card + 1 := by
  obtain ⟨hp, hq, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := hprec
  have hss_len : ss.length = p.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hp.2]
  have hrs_len : rs.length = q.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hq.2]
  have hlen : ss.length + 1 = rs.length := by rw [hss_len, hrs_len, hdeg]
  have hint : ListInterlaces ss rs := by
    rcases hshape with ⟨_, hi⟩ | ⟨hbad, _⟩
    · exact hi
    · exfalso
      rw [hss_len, hrs_len, hdeg] at hbad
      lia
  intro x
  obtain ⟨B1, B2⟩ := interlaces_filter_le_length_bounds ss rs x hss hrs hlen hint
  have hpcard : (p.roots.filter (· ≤ x)).card =
      (ss.filter (fun y => decide (y ≤ x))).length := by
    rw [← hss_eq, Multiset.filter_coe, Multiset.coe_card]
  have hqcard : (q.roots.filter (· ≤ x)).card =
      (rs.filter (fun y => decide (y ≤ x))).length := by
    rw [← hrs_eq, Multiset.filter_coe, Multiset.coe_card]
  rw [hpcard, hqcard]
  constructor <;> lia

/-- Tight oriented upper-threshold `Prec`-to-root-count bridge for the
differ-by-one case.

If `p ≺ q` and `q` has one more root than `p`, then every upper threshold
contains at least as many roots of `q` as roots of `p`, but at most one more. -/
theorem succDegreeRootCountAboveOriented_of_prec
    {p q : ℝ[X]} (hprec : Prec p q)
    (hdeg : q.natDegree = p.natDegree + 1) :
    ∀ x : ℝ,
      ((p.roots.filter (x < ·)).card : ℤ) ≤ (q.roots.filter (x < ·)).card ∧
      ((q.roots.filter (x < ·)).card : ℤ) ≤
        (p.roots.filter (x < ·)).card + 1 := fun x =>
  (succDegreeRootCountAbove_oriented_iff_rootCount_oriented_pointwise
    hprec.1.2 hprec.2.1.2 hdeg x).mpr
    (succDegreeRootCountLowerOriented_of_prec hprec hdeg x)

/-- Oriented Rolle root-count bound in upper-threshold form. -/
theorem rootCountAbove_derivative_oriented_of_splits
    {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    ∀ x : ℝ,
      ((p.derivative.roots.filter (x < ·)).card : ℤ) ≤
        (p.roots.filter (x < ·)).card ∧
      ((p.roots.filter (x < ·)).card : ℤ) ≤
        (p.derivative.roots.filter (x < ·)).card + 1 := by
  have hprec : Prec p.derivative p := (derivative_interlaces hp hdeg).toPrec
  have hdeg' : p.natDegree = p.derivative.natDegree + 1 := by
    rw [p.natDegree_derivative]
    lia
  exact succDegreeRootCountAboveOriented_of_prec hprec hdeg'

/-- A forward upper-count gap of at least three propagates to a derivative gap
of at least two. -/
theorem rootCountAbove_derivative_sub_ge_two_of_sub_ge_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hfdeg : 2 ≤ f.natDegree) (hgdeg : 2 ≤ g.natDegree) {x : ℝ}
    (hgap : 3 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
      (g.roots.filter (x < ·)).card) :
    2 ≤ ((f.derivative.roots.filter (x < ·)).card : ℤ) -
      (g.derivative.roots.filter (x < ·)).card := by
  obtain ⟨_hf_le, hf_back⟩ :=
    rootCountAbove_derivative_oriented_of_splits hf hfdeg x
  obtain ⟨hg_forw, _hg_back⟩ :=
    rootCountAbove_derivative_oriented_of_splits hg hgdeg x
  lia

/-- A reverse upper-count gap of at least three propagates to a derivative gap
of at least two. -/
theorem rootCountAbove_derivative_rev_sub_ge_two_of_sub_ge_three
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hfdeg : 2 ≤ f.natDegree) (hgdeg : 2 ≤ g.natDegree) {x : ℝ}
    (hgap : 3 ≤ ((g.roots.filter (x < ·)).card : ℤ) -
      (f.roots.filter (x < ·)).card) :
    2 ≤ ((g.derivative.roots.filter (x < ·)).card : ℤ) -
      (f.derivative.roots.filter (x < ·)).card := by
  obtain ⟨_hg_le, hg_back⟩ :=
    rootCountAbove_derivative_oriented_of_splits hg hgdeg x
  obtain ⟨hf_forw, _hf_back⟩ :=
    rootCountAbove_derivative_oriented_of_splits hf hfdeg x
  lia

/-- Pair-specific derivative induction rules out all upper-count gaps of size
at least three for a succ-degree compatible pair. -/
theorem compatibleSuccDegreeRootCountAbove_le_two_of_derivative_bound
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (_hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : 2 ≤ f.natDegree)
    (hder_bound : ∀ x : ℝ,
      ¬ f.derivative.IsRoot x → ¬ g.derivative.IsRoot x →
        ((f.derivative.roots.filter (x < ·)).card : ℤ) -
            (g.derivative.roots.filter (x < ·)).card ≤ 1 ∧
        ((g.derivative.roots.filter (x < ·)).card : ℤ) -
            (f.derivative.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≤ 2 := by
  have hg_split : g.Splits := (hcomp.isRealRooted_right hg_pos).2
  have hgdeg : 2 ≤ g.natDegree := by rw [hdeg]; lia
  have hf'_ne : f.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (by lia)
  have hg'_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by rw [hdeg]; lia)
  have hder_full :=
    rootCountAbove_diff_le_one_of_nonRoot_isRoot hf'_ne hg'_ne hder_bound
  intro x
  constructor
  · by_contra hle
    have hgap :
        3 ≤ ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card := by
      lia
    have hder_gap :=
      rootCountAbove_derivative_sub_ge_two_of_sub_ge_three
        hf_split hg_split hfdeg hgdeg hgap
    have hder_le := (hder_full x).1
    lia
  · by_contra hle
    have hgap :
        3 ≤ ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card := by
      lia
    have hder_gap :=
      rootCountAbove_derivative_rev_sub_ge_two_of_sub_ge_three
        hf_split hg_split hfdeg hgdeg hgap
    have hder_le := (hder_full x).2
    lia

/-- Derivative induction rules out all upper-count gaps of size at least
three for a succ-degree compatible pair.

This is the CS 3.4 induction step up to the remaining exact gap-two case. -/
theorem compatibleSuccDegreeRootCountAbove_le_two_of_derivative
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement)
    {f g : ℝ[X]} (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits) (hfdeg : 2 ≤ f.natDegree) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≤ 2 := by
  refine compatibleSuccDegreeRootCountAbove_le_two_of_derivative_bound
    hcomp hf_pos hg_pos hdeg hf_split hfdeg ?_
  intro x _hxf _hxg
  exact
    compatibleSuccDegreeRootCountAbove_derivative
      hcount hcomp hf_pos hg_pos hdeg hf_split hfdeg
      x

/-- Oriented same-degree `Prec`-to-root-count bridge in lower-threshold form.

For splitting real polynomials `p, q` of equal degree, the same-degree
interlacing relation `Prec p q` forces the oriented lower-threshold root-count
inequalities: at each threshold `q` has at most as many roots at or below it as
`p`, and `p` has at most one more than `q`. -/
theorem sameDegreeRootCountOriented_of_prec
    {p q : ℝ[X]} (hprec : Prec p q)
    (hdeg : q.natDegree = p.natDegree) :
    ∀ x : ℝ,
      ((q.roots.filter (· ≤ x)).card : ℤ) ≤ (p.roots.filter (· ≤ x)).card ∧
      ((p.roots.filter (· ≤ x)).card : ℤ) ≤ (q.roots.filter (· ≤ x)).card + 1 := by
  obtain ⟨hp, hq, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := hprec
  have hss_len : ss.length = p.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hp.2]
  have hrs_len : rs.length = q.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hq.2]
  have hlen : ss.length = rs.length := by rw [hss_len, hrs_len, hdeg]
  have halt : ListAlternates ss rs := by
    rcases hshape with ⟨hbad, _⟩ | ⟨_, ha⟩
    · exfalso
      rw [hss_len, hrs_len, hdeg] at hbad
      lia
    · exact ha
  intro x
  obtain ⟨B1, B2⟩ := alternates_filter_le_length_bounds ss rs x hss hrs hlen halt
  have hpcard : (p.roots.filter (· ≤ x)).card =
      (ss.filter (fun y => decide (y ≤ x))).length := by
    rw [← hss_eq, Multiset.filter_coe, Multiset.coe_card]
  have hqcard : (q.roots.filter (· ≤ x)).card =
      (rs.filter (fun y => decide (y ≤ x))).length := by
    rw [← hrs_eq, Multiset.filter_coe, Multiset.coe_card]
  rw [hpcard, hqcard]
  constructor <;> lia

/-- The succ-degree upper root-count target follows from its common-non-root
variant. -/
theorem posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  have hg_ne : g ≠ 0 :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).1
  exact rootCountAbove_diff_le_one_of_nonRoot_isRoot hf_pos.ne_zero hg_ne
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)

/-- The succ-degree lower common-non-root root-count target implies the full
upper-threshold succ-degree root-count target. -/
theorem posComboNoCommonSuccDegreeRootCountAbove_of_rootCountNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement :=
  posComboNoCommonSuccDegreeRootCountAbove_of_nonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_iff_rootCountNonRoot.mpr
      hcount)

end RealRooted
