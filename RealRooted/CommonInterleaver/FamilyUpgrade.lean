import RealRooted.CommonInterleaver.DescPolynomial

/-!
# Common interleavers: finite-family upgrades

The Chudnovsky--Seymour pairwise-to-global common-interleaver upgrades, with
their right- and left-oriented finite-sum corollaries.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

private lemma pairwise_ge_of_commonInterleaverSeq
    {fs : List ℝ[X]}
    (hseq : HasCommonInterleaverSeq fs)
    (hrr : ∀ f ∈ fs, f.Splits)
    (hfs_ne : fs ≠ []) :
    let d := csDegree fs
    let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
    (List.ofFn xs).Pairwise (· ≥ ·) := by
  classical
  let d := csDegree fs
  let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
  obtain ⟨fmax, hfmax_mem, hfmax_deg⟩ := exists_mem_csDegree_of_ne_nil (fs := fs) hfs_ne
  have hfmax_rr : fmax.Splits := hrr fmax hfmax_mem
  refine List.pairwise_ofFn.2 ?_
  intro i j hij
  have hd_pos : 0 < d := by lia
  have hroot_ne : rootSeqDesc fmax ≠ [] :=
    CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos hfmax_rr (by lia)
  have hi_slot : i.1 < (rootSeqDesc fmax).length + 1 := by
    rw [rootSeqDesc_length hfmax_rr, hfmax_deg]
    lia
  have hj_slot : j.1 < (rootSeqDesc fmax).length + 1 := by
    rw [rootSeqDesc_length hfmax_rr, hfmax_deg]
    lia
  have hxi :
      xs i ∈ rootSlotInterval (rootSeqDesc fmax) ⟨i.1, hi_slot⟩ :=
    (Classical.choose_spec (hseq i.1)) fmax hfmax_mem hi_slot
  have hxj :
      xs j ∈ rootSlotInterval (rootSeqDesc fmax) ⟨j.1, hj_slot⟩ :=
    (Classical.choose_spec (hseq j.1)) fmax hfmax_mem hj_slot
  exact
    CommonInterleaver.RootSlots.le_of_mem_rootSlots_of_lt
      (rs := rootSeqDesc fmax)
      hroot_ne
      rootSeqDesc_pairwise
      (i := i.1) (j := j.1)
      (by lia)
      (by lia)
      hxi hxj

private lemma pairwise_ge_of_commonLeftInterleaverSeq
    {fs : List ℝ[X]}
    (hseq : HasCommonLeftInterleaverSeq fs)
    (hrr : ∀ f ∈ fs, f.Splits)
    (hfs_ne : fs ≠ []) :
    let d := leftCsDegree fs
    let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
    (List.ofFn xs).Pairwise (· ≥ ·) := by
  classical
  let d := leftCsDegree fs
  let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
  obtain ⟨fmin, hfmin_mem, hfmin_deg⟩ := exists_mem_leftCsDegree_of_ne_nil
    (fs := fs) hfs_ne
  have hfmin_rr : fmin.Splits := hrr fmin hfmin_mem
  refine List.pairwise_ofFn.2 ?_
  intro i j hij
  have hd_pos : 0 < d := by lia
  have hroot_ne : rootSeqDesc fmin ≠ [] :=
    CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos hfmin_rr (by lia)
  have hi_slot : i.1 + 1 < (rootSeqDesc fmin).length + 1 := by
    rw [rootSeqDesc_length hfmin_rr, hfmin_deg]
    exact Nat.succ_lt_succ i.2
  have hj_slot : j.1 + 1 < (rootSeqDesc fmin).length + 1 := by
    rw [rootSeqDesc_length hfmin_rr, hfmin_deg]
    exact Nat.succ_lt_succ j.2
  have hxi :
      xs i ∈ rootSlotInterval (rootSeqDesc fmin) ⟨i.1 + 1, hi_slot⟩ :=
    (Classical.choose_spec (hseq i.1)) fmin hfmin_mem hi_slot
  have hxj :
      xs j ∈ rootSlotInterval (rootSeqDesc fmin) ⟨j.1 + 1, hj_slot⟩ :=
    (Classical.choose_spec (hseq j.1)) fmin hfmin_mem hj_slot
  exact
    CommonInterleaver.RootSlots.le_of_mem_rootSlots_of_lt
      (rs := rootSeqDesc fmin)
      hroot_ne
      rootSeqDesc_pairwise
      (i := i.1 + 1) (j := j.1 + 1)
      (by lia)
      (by lia)
      hxi hxj
private theorem hasCommonInterleaver_of_pairwiseHasCommonInterleaver_ge_two
    {f g : ℝ[X]} {fs : List ℝ[X]}
    (hrr : ∀ p ∈ f :: g :: fs, p.Splits)
    (hpos : ∀ p ∈ f :: g :: fs, HasPosLeadingCoeff p)
    (hpair : PairwiseHasCommonInterleaver (f :: g :: fs)) :
    HasCommonInterleaver (f :: g :: fs) := by
  /-
  This is the genuine Chudnovsky--Seymour core. The base cases `[]` and `[f]`
  are handled separately below, so the remaining argument may freely assume the
  family has length at least `2`.
  -/
  let ps : List ℝ[X] := f :: g :: fs
  have hrr_ps : ∀ p ∈ ps, p.Splits := by grind
  have hpos_ps : ∀ p ∈ ps, HasPosLeadingCoeff p := by grind
  have hpair_ps : PairwiseHasCommonInterleaver ps := by lia
  have hseq :
      HasCommonInterleaverSeq ps :=
    hasCommonInterleaverSeq_of_pairwiseHasCommonInterleaver
      (fs := ps) hrr_ps hpair_ps
  have hps_ne : ps ≠ [] := by lia
  let d : ℕ := csDegree ps
  let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
  let xlist : List ℝ := List.ofFn xs
  have hx_pair : xlist.Pairwise (· ≥ ·) := by
    simpa [d, xs, xlist] using
      (pairwise_ge_of_commonInterleaverSeq (fs := ps) hseq hrr_ps hps_ne)
  let h : ℝ[X] := CommonInterleaver.polyOfDescRoots xlist
  refine ⟨h, ?_⟩
  intro p hp
  have hp_mem : p ∈ ps := by lia
  have hp_rr : p.Splits := hrr_ps p hp_mem
  have hp_deg_lo : p.natDegree ≤ xlist.length := by
    have : p.natDegree ≤ csDegree ps := natDegree_le_csDegree (fs := ps) hp_mem
    grind
  have hp_deg_hi : xlist.length ≤ p.natDegree + 1 := by
    have : csDegree ps ≤ p.natDegree + 1 :=
      csDegree_le_natDegree_succ_of_pairwiseHasCommonInterleaver
        (fs := ps) (f := p) hps_ne hp_mem hpair_ps
    grind
  have hslot :
      ∀ j (hj : j < xlist.length),
        xlist.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc p)
          ⟨j, by
            have : j < p.natDegree + 1 := lt_of_lt_of_le hj hp_deg_hi
            simpa [rootSeqDesc_length hp_rr] using this⟩ := by
    grind
  have hp_prec : Prec p (CommonInterleaver.polyOfDescRoots xlist) :=
    CommonInterleaver.prec_of_slots_polyOfDescRoots
      (hpos p hp_mem).ne_zero hp_rr hx_pair hp_deg_lo hp_deg_hi hslot
  lia

theorem hasCommonInterleaver_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonInterleaver fs) :
    HasCommonInterleaver fs := by
  cases fs with
  | nil =>
      refine ⟨1, ?_⟩
      simp
  | cons f fs =>
    cases fs with
    | nil =>
      refine ⟨f, ?_⟩
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      simpa using prec_refl (hpos p (by simp)).ne_zero (hrr p (by simp))
    | cons g fs =>
      exact
        hasCommonInterleaver_of_pairwiseHasCommonInterleaver_ge_two
          (f := f) (g := g) (fs := fs) hrr hpos hpair

/-- Global finite-family right upgrade: pairwise common interleavers imply a
single common interleaver under the usual split and positive-leading
hypotheses. -/
def CommonInterleaverFamilyUpgradeStatement : Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, f.Splits) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    PairwiseHasCommonInterleaver fs →
    HasCommonInterleaver fs

/-- The proved global finite-family right upgrade, packaged as a statement alias. -/
theorem commonInterleaverFamilyUpgrade :
    CommonInterleaverFamilyUpgradeStatement :=
  hasCommonInterleaver_of_pairwiseHasCommonInterleaver

/-- Chudnovsky--Seymour `2 ⇒ 3`, left-oriented version: pairwise common left
interleavers can be upgraded to a single common left interleaver. -/
private theorem hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver_ge_two
    {f g : ℝ[X]} {fs : List ℝ[X]}
    (hrr : ∀ p ∈ f :: g :: fs, p.Splits)
    (hpos : ∀ p ∈ f :: g :: fs, HasPosLeadingCoeff p)
    (hpair : PairwiseHasCommonLeftInterleaver (f :: g :: fs)) :
    HasCommonLeftInterleaver (f :: g :: fs) := by
  let ps : List ℝ[X] := f :: g :: fs
  have hrr_ps : ∀ p ∈ ps, p.Splits := by grind
  have hpos_ps : ∀ p ∈ ps, HasPosLeadingCoeff p := by grind
  have hpair_ps : PairwiseHasCommonLeftInterleaver ps := by lia
  have hseq :
      HasCommonLeftInterleaverSeq ps :=
    hasCommonLeftInterleaverSeq_of_pairwiseHasCommonLeftInterleaver hpair_ps
  have hps_ne : ps ≠ [] := by lia
  let d : ℕ := leftCsDegree ps
  let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
  let xlist : List ℝ := List.ofFn xs
  have hx_pair : xlist.Pairwise (· ≥ ·) := by
    simpa [d, xs, xlist] using
      (pairwise_ge_of_commonLeftInterleaverSeq (fs := ps) hseq hrr_ps hps_ne)
  let h : ℝ[X] := CommonInterleaver.polyOfDescRoots xlist
  refine ⟨h, ?_⟩
  intro p hp
  have hp_mem : p ∈ ps := by lia
  have hp_rr : p.Splits := hrr_ps p hp_mem
  have hp_deg_lo : xlist.length ≤ p.natDegree := by
    have : leftCsDegree ps ≤ p.natDegree :=
      leftCsDegree_le_natDegree (fs := ps) hp_mem
    grind
  have hp_deg_hi : p.natDegree ≤ xlist.length + 1 := by
    have : p.natDegree ≤ leftCsDegree ps + 1 :=
      natDegree_le_leftCsDegree_succ_of_pairwiseHasCommonLeftInterleaver
        (fs := ps) (f := p) hps_ne hp_mem hpair_ps
    grind
  have hslot :
      ∀ j (hj : j < xlist.length),
        xlist.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc p)
          ⟨j + 1, by
            have : j < p.natDegree := lt_of_lt_of_le hj hp_deg_lo
            simpa [rootSeqDesc_length hp_rr] using Nat.succ_lt_succ this⟩ := by
    grind
  have hp_prec : Prec (CommonInterleaver.polyOfDescRoots xlist) p :=
    CommonInterleaver.prec_left_of_shifted_slots_polyOfDescRoots
      (hpos p hp_mem).ne_zero hp_rr hx_pair hp_deg_lo hp_deg_hi hslot
  lia

theorem hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    HasCommonLeftInterleaver fs := by
  cases fs with
  | nil =>
      refine ⟨1, ?_⟩
      simp
  | cons f fs =>
    cases fs with
    | nil =>
      refine ⟨f, ?_⟩
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      simpa using prec_refl (hpos p (by simp)).ne_zero (hrr p (by simp))
    | cons g fs =>
      exact
        hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver_ge_two
          (f := f) (g := g) (fs := fs) hrr hpos hpair

/-- Global finite-family left upgrade: pairwise common left interleavers imply a
single common left interleaver under the usual split and positive-leading
hypotheses. -/
def CommonLeftInterleaverFamilyUpgradeStatement : Prop :=
  ∀ {fs : List ℝ[X]},
    (∀ f ∈ fs, f.Splits) →
    (∀ f ∈ fs, HasPosLeadingCoeff f) →
    PairwiseHasCommonLeftInterleaver fs →
    HasCommonLeftInterleaver fs

/-- The proved global finite-family left upgrade, packaged as a statement alias. -/
theorem commonLeftInterleaverFamilyUpgrade :
    CommonLeftInterleaverFamilyUpgradeStatement :=
  hasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver

/-- A common interleaver immediately implies real-rootedness of the full sum,
by Wagner's finite-sum theorem on the right. -/
theorem isRealRooted_sum_of_commonInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hne : fs ≠ []) : (fs.sum ≠ 0 ∧ fs.sum.Splits) := by
  rcases hcommon with ⟨h, hprec⟩
  exact (prec_sum_right fs h hprec hpos hne).1

/-- Left-oriented sum real-rootedness package used by the Brändén 7.8.3
product family. This is the direct Chudnovsky--Seymour `3 ⇒ m` step for a
family with a common left interleaver. It should not be routed through
`WeightedCompatibleLeft`: that recursive Wagner structure imposes coprimeness
conditions which a common left interleaver does not provide in general. -/
theorem isRealRooted_sum_of_commonLeftInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hne : fs ≠ []) : (fs.sum ≠ 0 ∧ fs.sum.Splits) := by
  rcases hcommon with ⟨h, hprec⟩
  exact (prec_sum_left_of_common_left_signed fs h hprec hpos hne).2.1

end

end RealRooted
