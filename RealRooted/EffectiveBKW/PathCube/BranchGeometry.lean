module

public import RealRooted.EffectiveBKW.PathCube.ParameterBounds
public import RealRooted.EffectiveBKW.PathCube.PhaseGeometry
import RealRooted.EffectiveBKW.PathCube.BranchBounds
import RealRooted.EffectiveBKW.PathCube.EndpointChecks
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Interpreting the checked branch near its collisions
-/

public section

namespace RealRooted.EffectiveBKW.PathCube

open Set

private theorem cell_check_of_branch_check (h : branch.check = true)
    {c : BranchCell} (hc : c ∈ cells) : c.check curve false = true := by
  simp only [Branch.check, Bool.and_eq_true] at h
  have hcell := List.all_eq_true.mp h.1.2 c hc
  simp only [Bool.and_eq_true] at hcell
  exact hcell.1.1

/-- The selected resolvent root is strictly positive everywhere on the rational hull. -/
theorem branch_pos_of_check (h : branch.check = true) {t : ℝ}
    (ht : t ∈ Icc branch.lo.val branch.hi.val) : 0 < branch.y t := by
  obtain ⟨c, hc, hct⟩ := Branch.covers_sound cells_cover ht
  have hv := (BranchCell.valid_of_check (cell_check_of_branch_check h hc)).2.2.1
  have hlo := QNum.lt_sound (by decide +kernel) hv
    (List.all_eq_true.mp cells_lower_pos c hc)
  have hlo' : 0 < c.lo.val := by simpa [QNum.val] using hlo
  have hy := (Branch.check_sound h).2.2 c hc t hct
  exact hlo'.trans_le hy.1

/-- Every parameter in the rational hull is negative. -/
theorem parameter_neg {t : ℝ} (ht : t ∈ Icc branch.lo.val branch.hi.val) : t < 0 := by
  have hh : branch.hi.val < 0 := by norm_num [branch, QNum.val]
  exact ht.2.trans_lt hh

private theorem branch_mem_side (h : branch.check = true) {c d : BranchCell}
    (hc : c.check curve false = true) (hd : d ∈ cells)
    (hcomp : c.compatible d curve false = true) {t : ℝ}
    (ht : t ∈ Icc branch.lo.val branch.hi.val) (hct : t ∈ c.domain)
    (hdt : t ∈ d.domain) : branch.y t ∈ c.strip := by
  obtain ⟨y, hy, he, _⟩ := BranchCell.check_sound hc hct
  have hglobal := Branch.check_sound h
  have hsame := BranchCell.compatible_sound hc (cell_check_of_branch_check h hd)
    hcomp hct hdt ⟨hy.1.le, hy.2.le⟩ (hglobal.2.2 d hd t hdt) he
    (hglobal.2.1 t ht)
  exact hsame ▸ ⟨hy.1.le, hy.2.le⟩

private theorem cpos_eval (t b : ℝ) :
    exprCPOS.eval t b = b * scalarD t b ^ 2 - scalarA t b ^ 2 := by
  simp only [exprCPOS, IntPoly2.eval_add, IntPoly2.eval_mul, IntPoly2.eval_pow,
    IntPoly2.eval_smul, eval_polyB, eval_polyD, eval_polyA, Int.cast_neg, Int.cast_one]
  ring

private theorem ratio_lt_neg_one {t b : ℝ} (hb : 0 < b) (ha : scalarA t b < 0)
    (hp : exprCPOS.eval t b < 0) : pairReal t b / Real.sqrt b < -1 := by
  have hd := scalarD_pos (t := t) hb
  have hneg : pairReal t b < 0 := div_neg_of_neg_of_pos ha hd
  have hsq : b < pairReal t b ^ 2 := by
    rw [cpos_eval] at hp
    rw [pairReal, div_pow]
    exact (lt_div_iff₀ (sq_pos_of_pos hd)).mpr (by linarith)
  have hs := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  apply (div_lt_iff₀ hs).mpr
  nlinarith

private theorem one_lt_ratio {t b : ℝ} (hb : 0 < b) (ha : 0 < scalarA t b)
    (hp : exprCPOS.eval t b < 0) : 1 < pairReal t b / Real.sqrt b := by
  have hd := scalarD_pos (t := t) hb
  have hpos : 0 < pairReal t b := div_pos ha hd
  have hsq : b < pairReal t b ^ 2 := by
    rw [cpos_eval] at hp
    rw [pairReal, div_pow]
    exact (lt_div_iff₀ (sq_pos_of_pos hd)).mpr (by linarith)
  have hs := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  apply (lt_div_iff₀ hs).mpr
  nlinarith

/-- The rational hull starts beyond the negative collision and ends beyond the positive one. -/
theorem branch_ratio_endpoints (h : branch.check = true) :
    pairReal branch.lo.val (branch.y branch.lo.val) / Real.sqrt (branch.y branch.lo.val) < -1 ∧
      1 < pairReal branch.hi.val (branch.y branch.hi.val) /
        Real.sqrt (branch.y branch.hi.val) := by
  have hle : branch.lo.val ≤ branch.hi.val := by norm_num [branch, QNum.val]
  have hlo : branch.lo.val ∈ Icc branch.lo.val branch.hi.val := ⟨le_rfl, hle⟩
  have hhi : branch.hi.val ∈ Icc branch.lo.val branch.hi.val := ⟨hle, le_rfl⟩
  have hleft := branch_mem_side h sideCellLeft0_check
    (show cell000 ∈ cells by decide +kernel) sideCellLeft0_parent hlo
    (by norm_num [branch, sideCellLeft0, BranchCell.domain, QNum.val])
    (by norm_num [branch, cell000, BranchCell.domain, QNum.val])
  have hright := branch_mem_side h sideCellRight1_check
    (show cell168 ∈ cells by decide +kernel) sideCellRight1_parent hhi
    (by norm_num [branch, sideCellRight1, BranchCell.domain, QNum.val])
    (by norm_num [branch, cell168, BranchCell.domain, QNum.val])
  have hal := IntPoly2.posOnBox_sound sideCellLeft0_aNumerator
    (show branch.lo.val ∈ sideCellLeft0.domain by
      norm_num [branch, sideCellLeft0, BranchCell.domain, QNum.val]) hleft
  have har := IntPoly2.posOnBox_sound sideCellRight1_aNumerator
    (show branch.hi.val ∈ sideCellRight1.domain by
      norm_num [branch, sideCellRight1, BranchCell.domain, QNum.val]) hright
  have hpl := IntPoly2.posOnBox_sound sideCellLeft0_sign
    (show branch.lo.val ∈ sideCellLeft0.domain by
      norm_num [branch, sideCellLeft0, BranchCell.domain, QNum.val]) hleft
  have hpr := IntPoly2.posOnBox_sound sideCellRight1_sign
    (show branch.hi.val ∈ sideCellRight1.domain by
      norm_num [branch, sideCellRight1, BranchCell.domain, QNum.val]) hright
  simp only [IntPoly2.eval_signed, Bool.false_eq_true, ite_true, ite_false,
    neg_mul, one_mul] at hal har hpl hpr
  change 0 < -(polyA.eval branch.lo.val (branch.y branch.lo.val)) at hal
  change 0 < polyA.eval branch.hi.val (branch.y branch.hi.val) at har
  rw [eval_polyA] at hal har
  have hel := eval_exprCPOS ((Branch.check_sound h).2.1 _ hlo)
  have her := eval_exprCPOS ((Branch.check_sound h).2.1 _ hhi)
  norm_num only [pow_zero, mul_one, one_mul] at hel her
  exact ⟨ratio_lt_neg_one (branch_pos_of_check h hlo) (by linarith) (by linarith),
    one_lt_ratio (branch_pos_of_check h hhi) har (by linarith)⟩

/-- The normalized real part is continuous throughout the rational hull. -/
theorem continuousOn_branch_ratio (h : branch.check = true) :
    ContinuousOn (fun t ↦ pairReal t (branch.y t) / Real.sqrt (branch.y t))
      (Icc branch.lo.val branch.hi.val) := by
  have hb := (Branch.check_sound h).1
  have ha : ContinuousOn (fun t ↦ scalarA t (branch.y t))
      (Icc branch.lo.val branch.hi.val) := by
    dsimp [scalarA, scalarS, scalarC]
    fun_prop
  have hd : ContinuousOn (fun t ↦ scalarD t (branch.y t))
      (Icc branch.lo.val branch.hi.val) := by
    dsimp [scalarD, scalarPi]
    fun_prop
  exact (ha.div hd (fun t ht ↦ (scalarD_pos (t := t) (branch_pos_of_check h ht)).ne')).div
    hb.sqrt (fun t ht ↦ (Real.sqrt_pos.mpr (branch_pos_of_check h ht)).ne')

/-- A checked branch has a collision interval with a strictly nonreal pair inside.
The endpoints are selected by first and last level crossings of the normalized real part. -/
theorem exists_collision_interval_of_check (h : branch.check = true) :
    ∃ l r, l < r ∧ Icc l r ⊆ Icc branch.lo.val branch.hi.val ∧
      pairReal l (branch.y l) / Real.sqrt (branch.y l) = -1 ∧
      pairReal r (branch.y r) / Real.sqrt (branch.y r) = 1 ∧
      ∀ t ∈ Ioo l r, pairReal t (branch.y t) ^ 2 < branch.y t := by
  have hle : branch.lo.val ≤ branch.hi.val := by norm_num [branch, QNum.val]
  obtain ⟨hl, hr⟩ := branch_ratio_endpoints h
  obtain ⟨l, r, hlr, hsub, hfl, hfr, hinside⟩ :=
    exists_interval_of_continuousOn_crossing hle (continuousOn_branch_ratio h)
      (by norm_num : (-1 : ℝ) < 1) hl hr
  refine ⟨l, r, hlr, hsub, hfl, hfr, ?_⟩
  intro t ht
  have hb := branch_pos_of_check h (hsub (Ioo_subset_Icc_self ht))
  have hi := hinside t ht
  have hsq : (pairReal t (branch.y t) / Real.sqrt (branch.y t)) ^ 2 < 1 := by
    nlinarith [hi.1, hi.2]
  rw [div_pow, Real.sq_sqrt hb.le] at hsq
  exact (div_lt_one hb).mp hsq

end RealRooted.EffectiveBKW.PathCube
