import RealRooted.LiuOppositeSigns.BoundedIntervalContinuity
import RealRooted.LiuOppositeSigns.CommonInterleaverConsequences
import RealRooted.LiuOppositeSigns.Corollary22
import RealRooted.LiuOppositeSigns.DerivativeShiftSequenceRegularization
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderAssembly
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderLower
import RealRooted.LiuOppositeSigns.ForwardCubicQuadratic.RootOrderUpper
import RealRooted.LiuOppositeSigns.RootCountClosure
import RealRooted.LiuOppositeSigns.Theorem21Assembly
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount
import RealRooted.ObreschkoffConverse

/-!
# Liu opposite-sign compatibility theorem

This module contains the low-degree and analytic proof machinery for the
Liu opposite-sign compatibility theorem.  The theorem statement and
projection interface live in
`RealRooted.LiuOppositeSigns.Theorem21Statements`.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The no-common, nonconstant forward implication in Liu Theorem 2.1.

The derivative-shift regularization repairs the source's invalid inference
from no common roots to simple roots. The simple-root argument is applied to
arbitrarily close regularizations, and root matching closes the result. -/
theorem theorem21CompatibleToRootCountBranchesNoCommonNonconstant :
    theorem21CompatibleToRootCountBranchesNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno hf_deg hg_deg hcompat
  apply theorem21RootCountBranches_of_forall_pos_exists_roots_rel
    hsgn.left_ne_zero hsgn.right_ne_zero hf hg hno hf_deg hg_deg
  intro ρ hρ
  obtain ⟨epss, hlen, hbounds, hcompat', hno', hfrel, hgrel⟩ :=
    hno.exists_applyTDerivList_roots_rel (κ := 1) (ρ := ρ)
      hcompat hsgn.left_ne_zero hsgn.right_ne_zero hf hg
      zero_lt_one hρ (max f.natDegree g.natDegree)
  let f' : ℝ[X] := applyTDerivList epss f
  let g' : ℝ[X] := applyTDerivList epss g
  have hpos : ∀ eps ∈ epss, 0 < eps :=
    fun eps heps => (hbounds eps heps).1
  have hf'_ne : f' ≠ 0 := by
    simpa [f'] using
      applyTDerivList_ne_zero (epss := epss) hsgn.left_ne_zero
  have hg'_ne : g' ≠ 0 := by
    simpa [g'] using
      applyTDerivList_ne_zero (epss := epss) hsgn.right_ne_zero
  have hf'_split : f'.Splits := by
    simpa [f'] using hf.applyTDerivList hpos
  have hg'_split : g'.Splits := by
    simpa [g'] using hg.applyTDerivList hpos
  have hf'_deg : f'.natDegree ≠ 0 := by
    simpa [f'] using hf_deg
  have hg'_deg : g'.natDegree ≠ 0 := by
    simpa [g'] using hg_deg
  have hsgn' : OppositeLeadingSigns f' g' := by
    simpa [f', g', OppositeLeadingSigns] using hsgn
  have hf'_simple : HasSimpleRoots f' := by
    change HasSimpleRoots (applyTDerivList epss f)
    apply hasSimpleRoots_applyTDerivList_of_natDegree_le_length
      hpos hsgn.left_ne_zero hf
    rw [hlen]
    exact Nat.le_max_left _ _
  have hg'_simple : HasSimpleRoots g' := by
    change HasSimpleRoots (applyTDerivList epss g)
    apply hasSimpleRoots_applyTDerivList_of_natDegree_le_length
      hpos hsgn.right_ne_zero hg
    rw [hlen]
    exact Nat.le_max_right _ _
  have hbranches : theorem21RootCountBranches f' g' :=
    theorem21RootCountBranches_of_compatible_noCommon_nonconstant_of_simple
      hf'_split hg'_split hsgn' hno' hf'_deg hg'_deg
      hf'_simple hg'_simple hcompat'
  refine
    ⟨f', g', hf'_ne, hg'_ne, hf'_split, hg'_split, ?_, ?_, hbranches⟩
  · simpa [f'] using hfrel
  · simpa [g'] using hgrel

/-- The nonconstant no-common-root form of Liu Theorem 2.1. -/
theorem theorem21CompatibleRootCountNoCommonNonconstant :
    theorem21CompatibleRootCountNoCommonNonconstantStatement := by
  intro f g hf hg hsgn hno hf_deg hg_deg
  exact
    ⟨theorem21CompatibleToRootCountBranchesNoCommonNonconstant
        hf hg hsgn hno hf_deg hg_deg,
      theorem21RootCountBranchesToCompatibleNonconstant_of_xSub
        hf hg hsgn hf_deg hg_deg⟩

/-- Compatible no-common nonconstant opposite-sign pairs have degree gap at
most two. -/
theorem natDegree_abs_sub_le_two_of_compatible_noCommon_nonconstant
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hno : NoCommonRoots f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
    (theorem21CompatibleToRootCountBranchesNoCommonNonconstant
      hf hg hsgn hno hf_deg hg_deg hcompat)

/-- Correct nonconstant Liu equivalence with common roots retained explicitly.
The legacy branch-only equivalence is false when the endpoints share a largest
root: the right branch requires a strict largest-root inequality, while deleting
the largest root from only the left endpoint can leave a root-count gap of two.
The common-root deletion alternative is therefore necessary.

The reduced predicate is the strongest form because its ordinary root-count
branch retains the accompanying `NoCommonRoots` witness. -/
theorem compatible_iff_theorem21RootCountBranchesReduced_nonconstant
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21RootCountBranchesReduced f g := by
  constructor
  · intro hcompat
    by_cases hno : NoCommonRoots f g
    · exact Or.inl
        ⟨hno,
          theorem21CompatibleToRootCountBranchesNoCommonNonconstant
            hf hg hsgn hno hf_deg hg_deg hcompat⟩
    · exact Or.inr
        (CommonRootDeletionCompatibleBranch.of_compatible_of_not_noCommonRoots
          hcompat hno)
  · intro hbranches
    rcases hbranches with hbranches | hcommon
    · exact theorem21RootCountBranchesToCompatibleNonconstant_of_xSub
        hf hg hsgn hf_deg hg_deg hbranches.2
    · exact hcommon.compatible

/-- Public-facing correct nonconstant Liu equivalence. Compared with the
legacy branch-only predicate, this conclusion includes the necessary explicit
common-root deletion alternative. -/
theorem compatible_iff_theorem21RootCountBranchesWithCommon_nonconstant
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21RootCountBranchesWithCommon f g := by
  constructor
  · intro hcompat
    exact theorem21RootCountBranchesReduced.withCommon
      ((compatible_iff_theorem21RootCountBranchesReduced_nonconstant
        hf hg hsgn hf_deg hg_deg).mp hcompat)
  · intro hbranches
    rcases hbranches with hbranches | hcommon
    · exact theorem21RootCountBranchesToCompatibleNonconstant_of_xSub
        hf hg hsgn hf_deg hg_deg hbranches
    · exact hcommon.compatible

/-- The isolated forward direction of Liu Theorem 2.1 gives the pointwise
root-count gap bound. -/
theorem rootCountAtOrAbove_abs_sub_le_two_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 :=
  rootCountAtOrAbove_abs_sub_le_two_of_theorem21RootCountBranches hsgn
    (hforward hf hg hsgn hcompat)

/-- The isolated forward direction of Liu Theorem 2.1 gives the oriented
branch-wise pointwise root-count bounds. -/
theorem rootCountAtOrAbove_branch_bounds_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    (∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1) ∨
      (∀ x : ℝ,
        ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
          ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2) :=
  rootCountAtOrAbove_branch_bounds_of_theorem21RootCountBranches hsgn
    (hforward hf hg hsgn hcompat)

/-- The isolated forward direction of Liu Theorem 2.1 gives the normalized
positive-deletion count branches. -/
theorem theorem21PositiveDeletionCountBranches_of_compatible_of_forward
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (hcompat : Compatible f g) :
    theorem21PositiveDeletionCountBranches f g :=
  theorem21PositiveDeletionCountBranches_of_theorem21RootCountBranches hf hg hsgn
    (hforward hf hg hsgn hcompat)

/-- Guardrail for the factor-return route: multiplying the higher-degree
member of a simple quadratic/linear interlacing pair by `X` need not preserve
all-combinations real-rootedness.  Thus the Liu factor-return proof cannot use
a generic all-combinations strengthening of the translated `X * q` target. -/
theorem not_allComboRealRooted_X_mul_quadratic_linear_example :
    ¬ AllComboRealRooted
      (X * ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))) (-(X + C (2 : ℝ))) := by
  intro hall
  let p : ℝ[X] :=
    C (1 : ℝ) * (X * ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))) +
      C (-1 : ℝ) * (-(X + C (2 : ℝ)))
  have hp_splits : p.Splits := by
    simpa [p] using hall 1 (-1)
  have hp_deg : p.natDegree ≤ 3 := by
    dsimp [p]
    compute_degree!
  have hdisc_nonneg : 0 ≤ cubicDiscr p :=
    cubicDiscr_nonneg_of_splits_natDegree_le_three hp_deg hp_splits
  have hdisc_neg : cubicDiscr p < 0 := by
    norm_num [p, cubicDiscr, coeff_add, coeff_C_mul, coeff_neg, coeff_mul,
      Finset.antidiagonal, coeff_X, coeff_C, coeff_one]
  linarith

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and all-combinations factor-return
degree cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allCombo
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_degreeCases
      hcases)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and all-combinations
factor-return degree cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_allComboDegreeCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allComboDegreeCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and
all-combinations factor-return degree cases. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_allComboDegreeCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_allCombo
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_degreeCases
      hcases)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated forward direction and left all-combinations
factor-return degree cases, with right cases supplied by symmetry. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_leftAllComboCases
    (hforward : theorem21CompatibleToDeletionPairCommonInterleaverBranchesStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_allCombo
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_leftCases
      hcases)

/-- The branch-retaining deletion-pair common-interleaver theorem package
follows from the isolated root-count forward direction and left
all-combinations factor-return degree cases, with right cases supplied by
symmetry. -/
theorem
    theorem21DeletionPairCommonInterleaverIff_of_forward_and_leftAllComboCases
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesStatement :=
  theorem21DeletionPairCommonInterleaverIff_of_commonForward_and_leftAllComboCases
    (theorem21CompatibleToDeletionPairCommonInterleaverBranches_of_forward
      hforward)
    hcases

/-- The nonconstant branch-retaining deletion-pair common-interleaver theorem
package follows from the isolated nonconstant forward direction and left
all-combinations factor-return degree cases, with right cases supplied by
symmetry. -/
theorem
    theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_leftAllComboCases
    (hforward :
      theorem21CompatibleToDeletionPairCommonInterleaverBranchesNonconstantStatement)
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21CompatibleDeletionPairCommonInterleaverBranchesNonconstantStatement :=
  theorem21DeletionPairCommonInterleaverIffNonconstant_of_commonForward_and_allCombo
    hforward
    (theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_leftCases
      hcases)

/-- The constant endpoint omitted by the source formulation of Corollary 2.2:
compatibility with an oppositely signed nonzero constant forces degree at most two. -/
lemma natDegree_le_two_of_compatible_C_left
    {c : ℝ} {p : ℝ[X]} (hp : p.Splits)
    (hsgn : OppositeLeadingSigns (C c) p) (hcompat : Compatible (C c) p) :
    p.natDegree ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤ p.natDegree := by
    lia
  have shift_ne {q : ℝ[X]} (t : ℝ) (hqdeg : 3 ≤ q.natDegree) :
      q - C t ≠ 0 := by
    have hdegree : (q - C t).natDegree = q.natDegree := by
      apply natDegree_sub_eq_left_of_natDegree_lt
      simp only [natDegree_C]
      lia
    intro hzero
    have : q.natDegree = 0 := by
      rw [← hdegree, hzero, natDegree_zero]
    lia
  rcases hsgn.pos_neg_or_neg_pos with hpos | hneg
  · have hc_pos : 0 < c := by
      simpa [HasPosLeadingCoeff] using hpos.1
    have hneg_three : 3 ≤ (-p).natDegree := by
      simpa only [natDegree_neg] using hthree
    obtain ⟨t, ht, hshift⟩ :=
      exists_pos_shift_down_not_isRealRooted_of_isRealRooted_of_natDegree_ge_three
        hp.neg hpos.2 hneg_three
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    have hq_ne : (-p) - C t ≠ 0 := shift_ne t hneg_three
    have hcomb :=
      hcompat (t / c) 1 (div_nonneg ht.le hc_pos.le) zero_le_one
    have hpoly :
        C (t / c) * C c + C 1 * p = -((-p) - C t) := by
      calc
        C (t / c) * C c + C 1 * p = C ((t / c) * c) + p := by
          rw [C_mul, C_1, one_mul]
        _ = C t + p := by rw [div_mul_cancel₀ t hc_ne]
        _ = -((-p) - C t) := by ring
    rw [hpoly] at hcomb
    rcases hcomb with hzero | hreal
    · exact hq_ne (neg_eq_zero.mp hzero)
    · exact hshift ⟨hq_ne, by simpa only [neg_neg] using hreal.2.neg⟩
  · have hc_pos : 0 < -c := by
      simpa [HasPosLeadingCoeff] using hneg.1
    obtain ⟨t, ht, hshift⟩ :=
      exists_pos_shift_down_not_isRealRooted_of_isRealRooted_of_natDegree_ge_three
        hp hneg.2 hthree
    have hc_ne : -c ≠ 0 := ne_of_gt hc_pos
    have hq_ne : p - C t ≠ 0 := shift_ne t hthree
    have hcomb :=
      hcompat (t / (-c)) 1 (div_nonneg ht.le hc_pos.le) zero_le_one
    have hpoly : C (t / (-c)) * C c + C 1 * p = p - C t := by
      have hc' : c ≠ 0 := neg_ne_zero.mp hc_ne
      calc
        C (t / (-c)) * C c + C 1 * p = C ((t / (-c)) * c) + p := by
          rw [C_mul, C_1, one_mul]
        _ = C (-t) + p := by
          congr 2
          field_simp
        _ = p - C t := by simp only [map_neg]; ring
    rw [hpoly] at hcomb
    rcases hcomb with hzero | hreal
    · exact hq_ne hzero
    · exact hshift hreal

/-- The right polynomial has degree at most two when the left polynomial is constant. -/
lemma natDegree_right_le_two_of_compatible_of_left_natDegree_eq_zero
    {f g : ℝ[X]} (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hfdeg : f.natDegree = 0) :
    g.natDegree ≤ 2 := by
  rw [eq_C_of_natDegree_eq_zero hfdeg] at hsgn hcompat
  exact natDegree_le_two_of_compatible_C_left hg hsgn hcompat

/-- The left polynomial has degree at most two when the right polynomial is constant. -/
lemma natDegree_left_le_two_of_compatible_of_right_natDegree_eq_zero
    {f g : ℝ[X]} (hf : f.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hgdeg : g.natDegree = 0) :
    f.natDegree ≤ 2 :=
  natDegree_right_le_two_of_compatible_of_left_natDegree_eq_zero
    hf hsgn.symm hcompat.comm hgdeg

/-- Corollary 2.2's degree bound when the left polynomial is constant. -/
lemma natDegree_abs_sub_le_two_of_compatible_of_left_natDegree_eq_zero
    {f g : ℝ[X]} (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hfdeg : f.natDegree = 0) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  have hle :=
    natDegree_right_le_two_of_compatible_of_left_natDegree_eq_zero
      hg hsgn hcompat hfdeg
  rw [hfdeg]
  norm_num
  exact_mod_cast hle

/-- Corollary 2.2's degree bound when the right polynomial is constant. -/
lemma natDegree_abs_sub_le_two_of_compatible_of_right_natDegree_eq_zero
    {f g : ℝ[X]} (hf : f.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) (hgdeg : g.natDegree = 0) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 := by
  simpa only [abs_sub_comm] using
    natDegree_abs_sub_le_two_of_compatible_of_left_natDegree_eq_zero
      hf hsgn.symm hcompat.comm hgdeg

/-- Liu's Corollary 2.2: compatible real-rooted polynomials with opposite
leading signs have degrees differing by at most two. -/
theorem corollary22DegreeDiff_proof : corollary22DegreeDiffStatement := by
  unfold corollary22DegreeDiffStatement
  suffices h :
      ∀ n : ℕ, ∀ f g : ℝ[X], f.natDegree + g.natDegree = n →
        f.Splits → g.Splits → OppositeLeadingSigns f g → Compatible f g →
          |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 by
    intro f g hf hg hsgn hcompat
    exact h _ f g rfl hf hg hsgn hcompat
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f g hsum hf hg hsgn hcompat
    by_cases hfdeg : f.natDegree = 0
    · exact
        natDegree_abs_sub_le_two_of_compatible_of_left_natDegree_eq_zero
          hg hsgn hcompat hfdeg
    by_cases hgdeg : g.natDegree = 0
    · exact
        natDegree_abs_sub_le_two_of_compatible_of_right_natDegree_eq_zero
          hf hsgn hcompat hgdeg
    by_cases hno : NoCommonRoots f g
    · exact
        natDegree_abs_sub_le_two_of_compatible_noCommon_nonconstant
          hf hg hsgn hno hfdeg hgdeg hcompat
    obtain ⟨r, hfr, hgr⟩ := exists_common_root_of_not_noCommonRoots hno
    let f' : ℝ[X] := deleteRootFactor f r
    let g' : ℝ[X] := deleteRootFactor g r
    have hf'_splits : f'.Splits :=
      deleteRootFactor_splits_of_isRoot hf hfr
    have hg'_splits : g'.Splits :=
      deleteRootFactor_splits_of_isRoot hg hgr
    have hsgn' : OppositeLeadingSigns f' g' := by
      simpa [f', g'] using
        (hsgn.deleteRootFactor_left hfr).deleteRootFactor_right hgr
    have hcompat' : Compatible f' g' :=
      compatible_deleteRootFactor_of_common_root hcompat hfr hgr
    have hf'_degree : f'.natDegree = f.natDegree - 1 :=
      natDegree_deleteRootFactor f r
    have hg'_degree : g'.natDegree = g.natDegree - 1 :=
      natDegree_deleteRootFactor g r
    have hf_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hfdeg
    have hg_pos : 0 < g.natDegree := Nat.pos_of_ne_zero hgdeg
    have hlt : f'.natDegree + g'.natDegree < n := by
      rw [hf'_degree, hg'_degree, ← hsum]
      lia
    have hrec :=
      ih (f'.natDegree + g'.natDegree) hlt f' g' rfl
        hf'_splits hg'_splits hsgn' hcompat'
    rw [hf'_degree, hg'_degree] at hrec
    rw [Nat.cast_sub hf_pos, Nat.cast_sub hg_pos] at hrec
    norm_num at hrec
    simpa only [sub_sub_sub_cancel_right] using hrec


end LiuOppositeSigns
end RealRooted
