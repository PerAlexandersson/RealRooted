import RealRooted.CommonInterleaver.FamilyUpgrade
import RealRooted.LiuOppositeSigns.RootCount
import RealRooted.WagnerRightSum.Sign

/-!
# Largest-root selection from a common left interlacer

This file proves the finite-family root-selection lemma of
Marcus--Spielman--Srivastava.  The orientation and degree gap are explicit: a
polynomial of degree `d - 1` lies in proper position on the left of every
degree-`d` family member.
-/

open Polynomial

noncomputable section

namespace RealRooted

open LiuOppositeSigns

private lemma forall_lt_of_forall₂_le {l₁ l₂ : List ℝ} {x : ℝ}
    (h : List.Forall₂ (· ≤ ·) l₁ l₂)
    (hlt : ∀ y ∈ l₂, y < x) :
    ∀ y ∈ l₁, y < x := by
  induction h with
  | nil => simp
  | @cons a b l₁ l₂ hab _ ih =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hab.trans_lt (hlt b (by simp))
      · exact ih (fun z hz => hlt z (by simp [hz])) y hy

/-- In the degree-one-gap case, a point above every root of the left
interlacer but below some root of the right polynomial has negative
evaluation. -/
theorem Prec.eval_neg_of_left_top_gap {h p : ℝ[X]} {x : ℝ}
    (hhp : Prec h p) (hdeg : h.natDegree + 1 = p.natDegree)
    (hp_pos : HasPosLeadingCoeff p)
    (hh_lt : ∀ r ∈ h.roots, r < x)
    (hp_above : ∃ r, p.IsRoot r ∧ x < r) :
    p.eval x < 0 := by
  obtain ⟨hh, hp, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩ := hhp
  have hss_length : ss.length = h.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hh.2]
  have hrs_length : rs.length = p.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hp.2]
  rcases hshape with ⟨hlen, hinter⟩ | ⟨hlen, _⟩
  · have hrs_ne : rs ≠ [] := by
      intro hrs_nil
      rw [hrs_nil] at hlen
      simp at hlen
    have hpaired : List.Forall₂ (· ≤ ·) rs.dropLast ss :=
      listInterlaces_dropLast_forall₂_le hinter hlen
    have hss_lt : ∀ r ∈ ss, r < x := by
      intro r hr
      exact hh_lt r (by simpa [hss_eq] using Multiset.mem_coe.mpr hr)
    have hdrop_lt : ∀ r ∈ rs.dropLast, r < x :=
      forall_lt_of_forall₂_le hpaired hss_lt
    obtain ⟨r, hr_root, hxr⟩ := hp_above
    have hr_mem : r ∈ rs := by
      apply Multiset.mem_coe.mp
      rw [hrs_eq]
      exact (Polynomial.mem_roots hp.1).mpr hr_root
    have hlast_gt : x < rs.getLast hrs_ne :=
      hxr.trans_le (List.Pairwise.rel_getLast hrs_sorted hr_mem)
    have hprod_pos : 0 < (rs.dropLast.map (x - ·)).prod := by
      apply List.prod_pos
      intro y hy
      simp only [List.mem_map] at hy
      rcases hy with ⟨z, hz, rfl⟩
      exact sub_pos.mpr (hdrop_lt z hz)
    calc
      p.eval x = p.leadingCoeff * (rs.map (x - ·)).prod := by
        rw [eval_eq_leadingCoeff_mul_prod_sub hp.2 x, ← hrs_eq]
        rfl
      _ = p.leadingCoeff *
          ((rs.dropLast.map (x - ·)).prod * (x - rs.getLast hrs_ne)) := by
        conv_lhs =>
          rw [← List.dropLast_append_getLast hrs_ne, List.map_append,
            List.prod_append]
        simp
      _ < 0 :=
        mul_neg_of_pos_of_neg hp_pos
          (mul_neg_of_pos_of_neg hprod_pos (sub_neg.mpr hlast_gt))
  · lia

namespace LiuOppositeSigns.IsLargestRoot

/-- A nonzero scalar multiple has the same largest-root certificate. -/
theorem C_mul {p : ℝ[X]} {r a : ℝ} (h : IsLargestRoot p r) (ha : a ≠ 0) :
    IsLargestRoot (C a * p) r := by
  refine ⟨?_, ?_⟩
  · simpa [Polynomial.IsRoot.def, ha] using h.isRoot
  · intro s hs
    apply h.roots_le s
    simpa [Polynomial.roots_C_mul _ ha] using hs

/-- Remove a nonzero scalar from a largest-root certificate. -/
theorem of_C_mul {p : ℝ[X]} {r a : ℝ}
    (h : IsLargestRoot (C a * p) r) (ha : a ≠ 0) :
    IsLargestRoot p r := by
  refine ⟨?_, ?_⟩
  · simpa [Polynomial.IsRoot.def, ha] using h.isRoot
  · intro s hs
    apply h.roots_le s
    simpa [Polynomial.roots_C_mul _ ha] using hs

/-- Largest-root certificates are unique for a nonzero polynomial. -/
theorem unique {p : ℝ[X]} {r s : ℝ} (hp : p ≠ 0)
    (hr : IsLargestRoot p r) (hs : IsLargestRoot p s) : r = s := by
  apply le_antisymm
  · exact hs.roots_le r ((Polynomial.mem_roots hp).mpr hr.isRoot)
  · exact hr.roots_le s ((Polynomial.mem_roots hp).mpr hs.isRoot)

end LiuOppositeSigns.IsLargestRoot

/-- The two-polynomial MSS selection step for a common left interlacer whose
degree is one below the common family degree. -/
theorem exists_largestRoot_le_of_common_left_pair
    {h f g : ℝ[X]} {d : ℕ}
    (hfh : Prec h f) (hgh : Prec h g)
    (hh_deg : h.natDegree + 1 = d)
    (hf_deg : f.natDegree = d) (hg_deg : g.natDegree = d)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    ∃ r, IsLargestRoot (f + g) r ∧
      ((∃ rf, IsLargestRoot f rf ∧ rf ≤ r) ∨
        ∃ rg, IsLargestRoot g rg ∧ rg ≤ r) := by
  have hfg_deg : f.natDegree = g.natDegree := hf_deg.trans hg_deg.symm
  have hsum_pos : HasPosLeadingCoeff (f + g) :=
    hasPosLeadingCoeff_add_of_same_natDegree hfg_deg hf_pos hg_pos
  have hsum_prec : Prec h (f + g) := by
    simpa using prec_sum_left_of_common_left_signed [f, g] h
      (by simp [hfh, hgh]) (by simp [hf_pos, hg_pos]) (by simp)
  have hd_pos : 0 < d := by lia
  obtain ⟨rf, hrf⟩ :=
    LiuOppositeSigns.exists_isLargestRoot hfh.2.1.1 hfh.2.1.2 (by lia)
  obtain ⟨rg, hrg⟩ :=
    LiuOppositeSigns.exists_isLargestRoot hgh.2.1.1 hgh.2.1.2 (by lia)
  obtain ⟨r, hr⟩ :=
    LiuOppositeSigns.exists_isLargestRoot hsum_pos.ne_zero hsum_prec.2.1.2 (by
      rw [natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hfg_deg hf_pos hg_pos,
        hf_deg]
      exact hd_pos)
  refine ⟨r, hr, ?_⟩
  by_cases hrf_le : rf ≤ r
  · exact Or.inl ⟨rf, hrf, hrf_le⟩
  by_cases hrg_le : rg ≤ r
  · exact Or.inr ⟨rg, hrg, hrg_le⟩
  exfalso
  have hr_lt_rf : r < rf := lt_of_not_ge hrf_le
  have hr_lt_rg : r < rg := lt_of_not_ge hrg_le
  let x := (r + min rf rg) / 2
  have hr_lt_x : r < x := by
    dsimp [x]
    have : r < min rf rg := lt_min hr_lt_rf hr_lt_rg
    linarith
  have hx_lt_rf : x < rf := by
    dsimp [x]
    have := min_le_left rf rg
    linarith
  have hx_lt_rg : x < rg := by
    dsimp [x]
    have := min_le_right rf rg
    linarith
  have hh_lt : ∀ s ∈ h.roots, s < x := by
    intro s hs
    have hs_le_r : s ≤ r := roots_le_of_prec_right hsum_prec hr.roots_le s hs
    exact hs_le_r.trans_lt hr_lt_x
  have hf_neg : f.eval x < 0 :=
    hfh.eval_neg_of_left_top_gap (by lia) hf_pos hh_lt
      ⟨rf, hrf.isRoot, hx_lt_rf⟩
  have hg_neg : g.eval x < 0 :=
    hgh.eval_neg_of_left_top_gap (by lia) hg_pos hh_lt
      ⟨rg, hrg.isRoot, hx_lt_rg⟩
  have hsum_eval_pos : 0 < (f + g).eval x :=
    eval_pos_of_all_roots_lt hsum_pos.ne_zero hsum_prec.2.1.2 hsum_pos fun s hs =>
      (hr.roots_le s hs).trans_lt hr_lt_x
  rw [Polynomial.eval_add] at hsum_eval_pos
  linarith

/-- A common left interlacer with the degree gap required by MSS. -/
def HasCommonLeftInterlacerOfDegree (fs : List ℝ[X]) (d : ℕ) : Prop :=
  ∃ h : ℝ[X], h.natDegree + 1 = d ∧ ∀ p ∈ fs, Prec h p

/-- Finite nonnegative-weight MSS selection. The selected member is required
to have strictly positive weight. -/
theorem exists_mem_largestRoot_le_weightedSum :
    ∀ {l : List (ℝ × ℝ[X])} {h : ℝ[X]} {d : ℕ},
      h.natDegree + 1 = d →
      (∀ ap ∈ l, 0 ≤ ap.1) →
      (∀ ap ∈ l, Prec h ap.2) →
      (∀ ap ∈ l, ap.2.natDegree = d) →
      (∀ ap ∈ l, HasPosLeadingCoeff ap.2) →
      (∃ ap ∈ l, 0 < ap.1) →
      ∃ ap ∈ l, 0 < ap.1 ∧
        ∃ rp rsum, IsLargestRoot ap.2 rp ∧
          IsLargestRoot (weightedSum l) rsum ∧ rp ≤ rsum
  | [], _, _, _, _, _, _, _, hex => by simp_all
  | (a, p) :: l, h, d, hh_deg, hnonneg, hprec, hdeg, hpos, hex => by
      have ha_nonneg : 0 ≤ a := hnonneg (a, p) (by simp)
      have hp_prec : Prec h p := hprec (a, p) (by simp)
      have hp_deg : p.natDegree = d := hdeg (a, p) (by simp)
      have hp_pos : HasPosLeadingCoeff p := hpos (a, p) (by simp)
      have hnonneg_tail : ∀ ap ∈ l, 0 ≤ ap.1 :=
        List.forall_mem_of_forall_mem_cons hnonneg
      have hprec_tail : ∀ ap ∈ l, Prec h ap.2 :=
        List.forall_mem_of_forall_mem_cons hprec
      have hdeg_tail : ∀ ap ∈ l, ap.2.natDegree = d :=
        List.forall_mem_of_forall_mem_cons hdeg
      have hpos_tail : ∀ ap ∈ l, HasPosLeadingCoeff ap.2 :=
        List.forall_mem_of_forall_mem_cons hpos
      rcases eq_or_lt_of_le ha_nonneg with rfl | ha_pos
      · obtain ⟨ap, hap, hap_pos, rp, rsum, hrp, hrsum, hle⟩ :=
          exists_mem_largestRoot_le_weightedSum hh_deg hnonneg_tail
            hprec_tail hdeg_tail hpos_tail (by simp_all)
        exact ⟨ap, by simp [hap], hap_pos, rp, rsum, hrp, by simpa using hrsum, hle⟩
      · by_cases htail : ∃ ap ∈ l, 0 < ap.1
        · obtain ⟨ap, hap, hap_pos, rp, rtail, hrp, hrtail, hrp_le⟩ :=
            exists_mem_largestRoot_le_weightedSum hh_deg hnonneg_tail
              hprec_tail hdeg_tail hpos_tail htail
          have htail_prec : Prec h (weightedSum l) :=
            prec_weightedSum_left_of_common_left_signed
              l h hnonneg_tail hprec_tail hpos_tail htail
          have htail_deg : (weightedSum l).natDegree = d :=
            natDegree_weightedSum_eq_of_nonneg_of_sameDegree
              hnonneg_tail hdeg_tail hpos_tail htail
          have htail_pos : HasPosLeadingCoeff (weightedSum l) :=
            hasPosLeadingCoeff_weightedSum l hnonneg_tail hpos_tail htail
          have hscaled_prec : Prec h (C a * p) :=
            prec_C_mul_right hp_prec ha_pos.ne'
          have hscaled_deg : (C a * p).natDegree = d := by
            rw [Polynomial.natDegree_C_mul ha_pos.ne', hp_deg]
          have hscaled_pos : HasPosLeadingCoeff (C a * p) :=
            hasPosLeadingCoeff_C_mul ha_pos hp_pos
          obtain ⟨rsum, hrsum, hhead | htail_sel⟩ :=
            exists_largestRoot_le_of_common_left_pair
              hscaled_prec htail_prec hh_deg hscaled_deg htail_deg hscaled_pos htail_pos
          · obtain ⟨rhead, hrhead, hle⟩ := hhead
            exact ⟨(a, p), by simp, ha_pos, rhead, rsum,
              hrhead.of_C_mul ha_pos.ne', by simpa [weightedSum_cons] using hrsum, hle⟩
          · obtain ⟨rtail', hrtail', htail_le⟩ := htail_sel
            have htail_ne : weightedSum l ≠ 0 := htail_pos.ne_zero
            have hrtail_eq : rtail = rtail' :=
              hrtail.unique htail_ne hrtail'
            exact ⟨ap, by simp [hap], hap_pos, rp, rsum, hrp,
              by simpa [weightedSum_cons] using hrsum,
              hrp_le.trans (hrtail_eq.le.trans htail_le)⟩
        · have hzero_tail : weightedSum l = 0 :=
            weightedSum_eq_zero_of_forall_coeff_zero l
              (fun ap hap => by
                have hap_nonneg := hnonneg_tail ap hap
                have hap_not_pos : ¬ 0 < ap.1 := by
                  intro hap_pos
                  exact htail ⟨ap, hap, hap_pos⟩
                linarith)
          obtain ⟨rp, hrp⟩ :=
            LiuOppositeSigns.exists_isLargestRoot hp_prec.2.1.1 hp_prec.2.1.2 (by lia)
          exact ⟨(a, p), by simp, ha_pos, rp, rp, hrp,
            by simpa [weightedSum_cons, hzero_tail] using hrp.C_mul ha_pos.ne', le_rfl⟩

/-- Unweighted finite-family MSS selection. -/
theorem exists_mem_largestRoot_le_sum
    {fs : List ℝ[X]} {d : ℕ}
    (hcommon : HasCommonLeftInterlacerOfDegree fs d)
    (hdeg : ∀ p ∈ fs, p.natDegree = d)
    (hpos : ∀ p ∈ fs, HasPosLeadingCoeff p)
    (hne : fs ≠ []) :
    ∃ p ∈ fs, ∃ rp rsum, IsLargestRoot p rp ∧
      IsLargestRoot fs.sum rsum ∧ rp ≤ rsum := by
  rcases hcommon with ⟨h, hh_deg, hprec⟩
  obtain ⟨ap, hap, _, rp, rsum, hrp, hrsum, hle⟩ :=
    exists_mem_largestRoot_le_weightedSum
      (l := fs.map fun p => ((1 : ℝ), p)) hh_deg
      (by simp) (by simp_all) (by simp_all) (by simp_all) (by
        rcases List.exists_mem_of_ne_nil fs hne with ⟨p, hp⟩
        exact ⟨(1, p), by simp [hp]⟩)
  rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
  exact ⟨p, hp, rp, rsum, hrp, by simpa using hrsum, hle⟩

end RealRooted
