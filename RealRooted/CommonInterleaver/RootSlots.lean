import RealRooted.CommonInterleaver.RootSlots.Basic

/-!
# Common interleavers: root-slot transport

Interlacing transport through the root-slot intervals attached to descending
root sequences.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

private lemma listInterlaces_get_bounds
    {ss rs : List ℝ}
    (hint : ListInterlaces ss rs)
    {k : ℕ}
    (hks : k < ss.length)
    (hkr : k + 1 < rs.length) :
    rs.get ⟨k, lt_trans (Nat.lt_succ_self k) hkr⟩ ≤ ss.get ⟨k, hks⟩ ∧
    ss.get ⟨k, hks⟩ ≤ rs.get ⟨k + 1, hkr⟩ := by
  induction ss generalizing rs k with
  | nil => grind
  | cons s ss ih =>
  cases rs with
  | nil => grind
  | cons r₁ rs' =>
  cases rs' with
  | nil => grind
  | cons r₂ rs'' =>
  rcases hint with ⟨hr₁s, hsr₂, htail⟩
  simp_all
  grind

protected lemma CommonInterleaver.RootSlots.listInterlaces_of_index_bounds
    {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length)
    (hlower : ∀ k (hk : k < ss.length),
      rs.get ⟨k, by
        lia⟩ ≤ ss.get ⟨k, hk⟩)
    (hupper : ∀ k (hk : k < ss.length),
      ss.get ⟨k, hk⟩ ≤ rs.get ⟨k + 1, by
        lia⟩) :
    ListInterlaces ss rs := by
  induction ss generalizing rs with
  | nil =>
      cases rs with
      | nil =>
          lia
      | cons r rs =>
          cases rs with
          | nil =>
              simp [ListInterlaces]
          | cons r₂ rs' =>
              simp at hlen
  | cons s ss ih =>
      cases rs with
      | nil =>
          simp at hlen
      | cons r₁ rs =>
          cases rs with
          | nil =>
              simp at hlen
          | cons r₂ rs' =>
              have hlen' : ss.length + 1 = (r₂ :: rs').length := by simpa using Nat.succ.inj hlen
              have hr₁s : r₁ ≤ s := by simpa using hlower 0 (by simp)
              have hs_r₂ : s ≤ r₂ := by simpa using hupper 0 (by simp)
              have hlower' : ∀ k (hk : k < ss.length),
                  (r₂ :: rs').get ⟨k, by
                    lia⟩ ≤ ss.get ⟨k, hk⟩ := by
                intro k hk
                have hk' : k + 1 < (s :: ss).length := by simpa using Nat.succ_lt_succ hk
                simpa using hlower (k + 1) hk'
              have hupper' : ∀ k (hk : k < ss.length),
                  ss.get ⟨k, hk⟩ ≤ (r₂ :: rs').get ⟨k + 1, by
                    lia⟩ := by
                intro k hk
                have hk' : k + 1 < (s :: ss).length := by simpa using Nat.succ_lt_succ hk
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  hupper (k + 1) hk'
              exact ⟨hr₁s, hs_r₂, ih hlen' hlower' hupper'⟩

protected lemma CommonInterleaver.RootSlots.listAlternates_of_index_bounds
    {ss rs : List ℝ}
    (hlen : ss.length = rs.length)
    (hlower : ∀ k (hk : k < ss.length),
      ss.get ⟨k, hk⟩ ≤ rs.get ⟨k, by lia⟩)
    (hupper : ∀ k (hk : k + 1 < ss.length),
      rs.get ⟨k, by
        lia⟩ ≤ ss.get ⟨k + 1, hk⟩) :
    ListAlternates ss rs := by
  induction ss generalizing rs with
  | nil =>
      cases rs with
      | nil =>
          simp [ListAlternates]
      | cons r rs =>
          simp at hlen
  | cons s ss ih =>
      cases rs with
      | nil =>
          simp at hlen
      | cons r rs =>
          have hlen' : ss.length = rs.length := by simpa using Nat.succ.inj hlen
          have hs_r : s ≤ r := by simpa using hlower 0 (by simp)
          have hinter : ListInterlaces ss (r :: rs) := by
            refine CommonInterleaver.RootSlots.listInterlaces_of_index_bounds ?_ ?_ ?_
            · simpa using hlen
            · intro k hk
              have hk' : k + 1 < (s :: ss).length := by simpa using Nat.succ_lt_succ hk
              simpa using hupper k hk'
            · intro k hk
              have hk' : k + 1 < (s :: ss).length := by simpa using Nat.succ_lt_succ hk
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                hlower (k + 1) hk'
          exact ⟨hs_r, hinter⟩

private lemma listAlternates_get_lower
    {ss rs : List ℝ}
    (halt : ListAlternates ss rs)
    {k : ℕ}
    (hks : k < ss.length)
    (hkr : k < rs.length) :
    ss.get ⟨k, hks⟩ ≤ rs.get ⟨k, hkr⟩ := by
  induction ss generalizing rs k with
  | nil =>
      grind
  | cons s ss ih =>
      cases rs with
      | nil =>
          grind
      | cons r rs' =>
          rcases halt with ⟨hsr, htail⟩
          cases k with
          | zero =>
              simp_all
          | succ k =>
              have hks' : k < ss.length := by simp_all
              have hkr' : k < rs'.length := by simp_all
              simpa using (listInterlaces_get_bounds htail hks'
                (by lia)).2

private lemma listAlternates_get_upper
    {ss rs : List ℝ}
    (halt : ListAlternates ss rs)
    {k : ℕ}
    (hk : k + 1 < ss.length)
    (hkr : k < rs.length) :
    rs.get ⟨k, hkr⟩ ≤ ss.get ⟨k + 1, hk⟩ := by
  induction ss generalizing rs k with
  | nil => grind
  | cons s ss ih =>
  cases rs with
  | nil => grind
  | cons r rs' =>
  rcases halt with ⟨hsr, htail⟩
  cases ss with
  | nil => grind
  | cons s₂ ss₂ =>
  cases rs' with
  | nil => cases htail
  | cons r₂ rs₂ =>
  rcases htail with ⟨hr_s₂, hs₂_r₂, htail'⟩
  cases k with
  | zero => grind
  | succ k =>
  simp_all
  have halt' : ListAlternates (s₂ :: ss₂) (r₂ :: rs₂) := ⟨hs₂_r₂, htail'⟩
  grind

private lemma mem_rootSlotInterval_reverse_of_listInterlaces_interior
    {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    {j : Fin rs.length}
    (h0 : j.1 ≠ 0)
    (hlast : j.1 ≠ ss.length) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simp [List.length_reverse, hlen]⟩ := by
  have hj_pos : 0 < j.1 := Nat.pos_of_ne_zero h0
  have hjss : j.1 < ss.length := by lia
  have hnot_last : ¬ j.1 = ss.length := hlast
  let k : Fin rs.length := ⟨rs.length - 1 - j.1, by lia⟩
  let klow : Fin ss.length := ⟨ss.length - 1 - j.1, by lia⟩
  let khigh : Fin ss.length := ⟨ss.length - j.1, by lia⟩
  have hrs_rev :
      rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ = rs.get k := by
    simp [k]
  have hss_rev_lo :
      ss.reverse.get ⟨j.1, by simp_all⟩ = ss.get klow := by
    simp [klow]
  have hpred' : j.1 - 1 < ss.length := by lia
  have hpred : j.1 - 1 < ss.reverse.length := by simp_all
  let kupper : Fin ss.length := ⟨ss.length - 1 - (j.1 - 1), by lia⟩
  have hkupper_eq : kupper = khigh := by
    apply Fin.ext
    simp [kupper, khigh]
    lia
  have hss_rev_hi :
      ss.reverse.get ⟨j.1 - 1, hpred⟩ = ss.get khigh := by
    rw [show ss.get khigh = ss.get kupper by simp [hkupper_eq]]
    simp [kupper]
  have hslot :
      rootSlotInterval ss.reverse
        ⟨j.1, by simp [List.length_reverse, hlen]⟩ =
        Set.Icc (ss.reverse.get ⟨j.1, by simp_all⟩)
          (ss.reverse.get ⟨j.1 - 1, hpred⟩) := by
    simp [rootSlotInterval, h0, hnot_last, List.length_reverse]
  rw [hslot, hrs_rev, hss_rev_lo, hss_rev_hi]
  have hklow_succ_lt : klow.1 + 1 < rs.length := by
    simp [klow]
    lia
  have hb_low := listInterlaces_get_bounds hint klow.2 hklow_succ_lt
  have hidx_low :
      (⟨klow.1 + 1, hklow_succ_lt⟩ : Fin rs.length) = k := by
    apply Fin.ext
    simp [klow, k]
    lia
  have hlower : ss.get klow ≤ rs.get k := by simp_all
  have hkhigh_succ_lt : khigh.1 + 1 < rs.length := by
    simp [khigh]
    lia
  have hb_high := listInterlaces_get_bounds hint khigh.2 hkhigh_succ_lt
  have hidx_high :
      (⟨khigh.1, lt_trans (Nat.lt_succ_self khigh.1) hkhigh_succ_lt⟩ : Fin rs.length) = k := by
    apply Fin.ext
    simp [khigh, k]
    lia
  simp_all

private lemma mem_rootSlotInterval_reverse_of_listInterlaces_zero
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs) :
    rs.reverse.get ⟨0, by
      grind⟩ ∈
      rootSlotInterval ss.reverse
        ⟨0, by
          lia⟩ := by
  cases ss with
  | nil =>
      simp [rootSlotInterval] at hlen ⊢
  | cons s ss =>
      have hss_ne : (s :: ss) ≠ [] := by lia
      have hrs_pos : 0 < rs.length := by lia
      have hrs_ne : rs ≠ [] := List.length_pos_iff_ne_nil.mp hrs_pos
      rw [CommonInterleaver.RootSlots.rootSlotInterval_reverse_zero hss_ne]
      rw [CommonInterleaver.RootSlots.reverse_get_zero_eq_getLast hrs_ne]
      exact Set.mem_Ici.mpr <|
        listInterlaces_all_le_getLast hrs_ne hrs hint _ (List.getLast_mem hss_ne)

private lemma mem_rootSlotInterval_reverse_of_listInterlaces_last
    {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    (hss_ne : ss ≠ []) :
    rs.reverse.get ⟨ss.length, by
      grind⟩ ∈
      rootSlotInterval ss.reverse
        ⟨ss.length, by
          simp⟩ := by
  have hrs_pos : 0 < rs.length := by lia
  have hrs_ne : rs ≠ [] := List.length_pos_iff_ne_nil.mp hrs_pos
  rw [CommonInterleaver.RootSlots.rootSlotInterval_reverse_last hss_ne]
  have hidx :
      (⟨ss.length, by
        grind⟩ : Fin rs.reverse.length) =
      ⟨rs.length - 1, by
        simp_all⟩ := by
    have hsub : ss.length = rs.length - 1 := by lia
    simp_all
  rw [hidx]
  rw [CommonInterleaver.RootSlots.reverse_get_last_eq_get_zero hrs_ne]
  apply Set.mem_Iic.mpr
  have hss_pos : 0 < ss.length := List.length_pos_iff_ne_nil.mpr hss_ne
  have hb :=
    listInterlaces_get_bounds hint (k := 0)
      (by simp_all)
      (by simp_all)
  simp_all

private lemma mem_rootSlotInterval_reverse_of_listInterlaces
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    (j : Fin rs.length) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simp [List.length_reverse, hlen]⟩ := by
  by_cases h0 : j.1 = 0
  · have hj :
        j = ⟨0, by
          lia⟩ := by
      grind
    simpa [hj] using mem_rootSlotInterval_reverse_of_listInterlaces_zero hss hrs hlen hint
  · by_cases hlast : j.1 = ss.length
    · have hss_ne : ss ≠ [] := by simp_all
      have hj :
          j = ⟨ss.length, by
            lia⟩ := by
        grind
      simpa [hj] using
        mem_rootSlotInterval_reverse_of_listInterlaces_last hlen hint hss_ne
    · exact
        mem_rootSlotInterval_reverse_of_listInterlaces_interior hlen hint h0 hlast

private lemma mem_rootSlotInterval_reverse_of_listAlternates_interior
    {ss rs : List ℝ}
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs)
    {j : Fin rs.length}
    (h0 : j.1 ≠ 0) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simp [List.length_reverse, hlen]⟩ := by
  have hjss : j.1 < ss.length := by lia
  have hnot_last : ¬ j.1 = ss.length := ne_of_lt hjss
  let k : Fin ss.length := ⟨ss.length - 1 - j.1, by lia⟩
  have hk_succ : k.1 + 1 < ss.length := by
    simp [k]
    lia
  let ks : Fin ss.length := ⟨k.1 + 1, hk_succ⟩
  let kr : Fin rs.length := ⟨rs.length - 1 - j.1, by lia⟩
  have hkr_eq : kr.1 = k.1 := by simp [kr, k, hlen]
  have hks_eq : ks.1 = ss.length - j.1 := by
    simp [ks, k]
    lia
  have hrs_rev :
      rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ = rs.get kr := by
    simp [kr]
  have hss_rev_lo :
      ss.reverse.get ⟨j.1, by simp [List.length_reverse, hlen]⟩ = ss.get k := by
    simp [k, hlen]
  have hpred' : j.1 - 1 < ss.length := by lia
  have hpred : j.1 - 1 < ss.reverse.length := by simp_all
  let kupper : Fin ss.length := ⟨ss.length - 1 - (j.1 - 1), by
    lia⟩
  have hkupper_eq : kupper = ks := by
    apply Fin.ext
    simp [kupper, ks, k]
    lia
  have hss_rev_hi :
      ss.reverse.get ⟨j.1 - 1, hpred⟩ = ss.get ks := by
    rw [show ss.get ks = ss.get kupper by simp [hkupper_eq]]
    simp [kupper, hlen]
  have hslot :
      rootSlotInterval ss.reverse
        ⟨j.1, by simp [List.length_reverse, hlen]⟩ =
        Set.Icc (ss.reverse.get ⟨j.1, by simp [List.length_reverse, hlen]⟩)
          (ss.reverse.get ⟨j.1 - 1, hpred⟩) := by
    simp [rootSlotInterval, h0, hnot_last, List.length_reverse]
  rw [hslot, hrs_rev, hss_rev_lo, hss_rev_hi]
  rw [show kr = ⟨k.1, by simpa [hkr_eq] using kr.2⟩ by
    apply Fin.ext
    simp_all]
  have hk_lower : ss.get k ≤ rs.get ⟨k.1, by simpa [hkr_eq] using kr.2⟩ :=
    listAlternates_get_lower halt k.2 (by simpa [hkr_eq] using kr.2)
  have hk_upper : rs.get ⟨k.1, by simpa [hkr_eq] using kr.2⟩ ≤ ss.get ks := by
    have hk_rs : k.1 < rs.length := by simpa [hkr_eq] using kr.2
    simpa [ks] using listAlternates_get_upper halt hk_succ hk_rs
  simp_all

private lemma mem_rootSlotInterval_reverse_of_listAlternates_zero
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs)
    (hrs_ne : rs ≠ []) :
    rs.reverse.get ⟨0, by
      grind⟩ ∈
      rootSlotInterval ss.reverse
        ⟨0, by
          lia⟩ := by
  cases ss with
  | nil =>
      grind
  | cons s ss =>
      have hss_ne : (s :: ss) ≠ [] := by lia
      have hrs_ne : rs ≠ [] := by lia
      rw [CommonInterleaver.RootSlots.rootSlotInterval_reverse_zero hss_ne]
      rw [CommonInterleaver.RootSlots.reverse_get_zero_eq_getLast hrs_ne]
      exact Set.mem_Ici.mpr <|
        listAlternates_all_le_getLast hrs_ne hrs halt _ (List.getLast_mem hss_ne)

private lemma mem_rootSlotInterval_reverse_of_listAlternates
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs)
    (j : Fin rs.length) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simp [List.length_reverse, hlen]⟩ := by
  by_cases h0 : j.1 = 0
  · have hj :
        j = ⟨0, by
          lia⟩ := by
      apply Fin.ext
      lia
    have hrs_ne : rs ≠ [] := List.length_pos_iff_ne_nil.mp (by lia)
    simpa [hj] using mem_rootSlotInterval_reverse_of_listAlternates_zero hss hrs hlen halt hrs_ne
  · exact mem_rootSlotInterval_reverse_of_listAlternates_interior hlen halt h0

/-- Slot transport from an ascending `Prec` witness to the descending
Chudnovsky--Seymour interval language. This is the core bridge needed to turn
pairwise common interleavers into pairwise-intersecting slot intervals. -/
private lemma mem_rootSlotInterval_of_prec_witness
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·)) (hrs : rs.Pairwise (· ≤ ·))
    (hshape : (ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs))
    (j : Fin rs.length) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈
      rootSlotInterval ss.reverse
        ⟨j.1, by
          grind⟩ := by
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · simpa using mem_rootSlotInterval_reverse_of_listInterlaces hss hrs hlen hint j
  · simpa using mem_rootSlotInterval_reverse_of_listAlternates hss hrs hlen halt j

protected lemma CommonInterleaver.RootSlots.mem_rootSlotInterval_of_prec
    {f g : ℝ[X]} (hfg : Prec f g) (j : Fin g.natDegree) :
    (rootSeqDesc g).get ⟨j.1, by
      rcases hfg with ⟨_, hg, _, _, _, _, _, _, _⟩
      simp [rootSeqDesc, card_roots_of_splits hg.2]⟩ ∈ rootSlotInterval (rootSeqDesc f)
      ⟨j.1, by
        have hdeg := hfg.natDegree_le_succ
        rcases hfg with ⟨hf, hg, _, _, _, _, _, _, _⟩
        simpa [hf.2, hg.2] using lt_of_lt_of_le j.2 hdeg⟩ := by
  have hdeg := hfg.natDegree_le_succ
  rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_desc : rootSeqDesc f = ss.reverse := rootSeqDesc_eq_reverse_of_pairwise hss hss_eq
  have hrs_desc : rootSeqDesc g = rs.reverse := rootSeqDesc_eq_reverse_of_pairwise hrs hrs_eq
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  let jg_desc : Fin (rootSeqDesc g).length := ⟨j.1, by
    simp [rootSeqDesc, card_roots_of_splits hg.2]⟩
  let jg_rev : Fin rs.reverse.length := ⟨j.1, by
    simp [List.length_reverse, hrs_len]⟩
  let jf_desc : Fin ((rootSeqDesc f).length + 1) := ⟨j.1, by
    grind⟩
  let jf_rev : Fin (ss.reverse.length + 1) := ⟨j.1, by
    grind⟩
  have hmem_rev : rs.reverse.get jg_rev ∈ rootSlotInterval ss.reverse jf_rev :=
    mem_rootSlotInterval_of_prec_witness hss hrs hshape ⟨j.1, by lia⟩
  lia

private lemma mem_shifted_rootSlotInterval_reverse_of_listInterlaces
    {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    (j : Fin ss.length) :
    ss.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈
      rootSlotInterval rs.reverse
        ⟨j.1 + 1, by
          simp [List.length_reverse]
          lia⟩ := by
  let k : ℕ := ss.length - 1 - j.1
  have hk : k < ss.length := by
    simp [k]
    lia
  have hksucc : k + 1 < rs.length := by
    simp [k]
    lia
  have hbounds := listInterlaces_get_bounds hint (k := k) hk hksucc
  have h0 : ¬ j.1 + 1 = 0 := by lia
  have hlast : ¬ j.1 + 1 = rs.length := by
    intro hbad
    lia
  have hj1 : j.1 + 1 < rs.reverse.length := by
    simp [List.length_reverse]
    lia
  have hjpred : j.1 + 1 - 1 < rs.reverse.length := by
    simp [List.length_reverse]
    lia
  have hslot :
      rootSlotInterval rs.reverse
          ⟨j.1 + 1, by
            simp [List.length_reverse]
            lia⟩ =
        Set.Icc (rs.reverse.get ⟨j.1 + 1, hj1⟩)
          (rs.reverse.get ⟨j.1 + 1 - 1, hjpred⟩) := by
    simp [rootSlotInterval, hlast, List.length_reverse]
  have hss_rev :
      ss.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ =
        ss.get ⟨k, hk⟩ := by
    simp [k]
  have hrs_rev_lo :
      rs.reverse.get ⟨j.1 + 1, hj1⟩ =
        rs.get ⟨k, by lia⟩ := by
    calc
      rs.reverse.get ⟨j.1 + 1, hj1⟩ =
          rs.get ⟨rs.length - 1 - (j.1 + 1), by
            have hrs_pos : 0 < rs.length := by
              have : 0 < rs.reverse.length := lt_of_le_of_lt (Nat.zero_le _) hj1
              simpa [List.length_reverse] using this
            lia⟩ := CommonInterleaver.RootSlots.get_reverse_eq_get_sub (xs := rs) (k := j.1 + 1)
              (by simpa [List.length_reverse] using hj1)
      _ = rs.get ⟨k, by lia⟩ := by
            apply congrArg (fun i : Fin rs.length => rs.get i)
            apply Fin.ext
            simp [k]
            lia
  have hrs_rev_hi :
      rs.reverse.get ⟨j.1 + 1 - 1, hjpred⟩ =
        rs.get ⟨k + 1, hksucc⟩ := by
    calc
      rs.reverse.get ⟨j.1 + 1 - 1, hjpred⟩ =
          rs.get ⟨rs.length - 1 - (j.1 + 1 - 1), by
            have hrs_pos : 0 < rs.length := by
              have : 0 < rs.reverse.length := lt_of_le_of_lt (Nat.zero_le _) hjpred
              simpa [List.length_reverse] using this
            lia⟩ :=
          CommonInterleaver.RootSlots.get_reverse_eq_get_sub
            (xs := rs) (k := j.1 + 1 - 1) (by simpa [List.length_reverse] using hjpred)
      _ = rs.get ⟨k + 1, hksucc⟩ := by
            apply congrArg (fun i : Fin rs.length => rs.get i)
            apply Fin.ext
            simp [k]
            lia
  rw [hslot, hss_rev, hrs_rev_lo, hrs_rev_hi]
  exact hbounds

private lemma mem_shifted_rootSlotInterval_reverse_of_listAlternates
    {ss rs : List ℝ}
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs)
    (j : Fin ss.length) :
    ss.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈
      rootSlotInterval rs.reverse
        ⟨j.1 + 1, by
          simp [List.length_reverse]
          lia⟩ := by
  let k : ℕ := ss.length - 1 - j.1
  have hk : k < ss.length := by
    simp [k]
    lia
  by_cases hlast : j.1 + 1 = rs.length
  · have hjlast :
        j.1 + 1 =
          rs.reverse.length := by simpa [List.length_reverse] using hlast
    have hk0 : k = 0 := by
      simp [k]
      lia
    have hslot :
        rootSlotInterval rs.reverse
            ⟨j.1 + 1, by
              simp [List.length_reverse]
              lia⟩ =
          Set.Iic (rs.get ⟨0, by
            rw [← hlen]
            simpa [hk0] using hk⟩) := by
      simpa [hjlast] using
        CommonInterleaver.RootSlots.rootSlotInterval_last_eq_reverse_get_zero
          (rs := rs.reverse) (List.reverse_ne_nil_iff.mpr (by
            apply List.ne_nil_of_length_pos
            simp [← hlen]
            lia))
    have hbounds := listAlternates_get_lower halt (k := 0) (by simpa [hk0] using hk)
      (by
        rw [← hlen]
        simpa [hk0] using hk)
    have hss_rev :
        ss.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ =
          ss.get ⟨0, by simpa [hk0] using hk⟩ := by
      simp [k, hk0]
    rw [hslot, hss_rev]
    exact hbounds
  · have h0 : ¬ j.1 + 1 = 0 := by lia
    have hj1 : j.1 + 1 < rs.reverse.length := by
      simp [List.length_reverse]
      lia
    have hjpred : j.1 + 1 - 1 < rs.reverse.length := by
      simp [List.length_reverse]
      lia
    have hslot :
        rootSlotInterval rs.reverse
            ⟨j.1 + 1, by
              simp [List.length_reverse]
              lia⟩ =
          Set.Icc (rs.reverse.get ⟨j.1 + 1, hj1⟩)
            (rs.reverse.get ⟨j.1 + 1 - 1, hjpred⟩) := by
      simp [rootSlotInterval, hlast, List.length_reverse]
    have hkpos : 0 < k := by
      simp [k]
      lia
    have hlow := listAlternates_get_upper halt (k := k - 1) (by lia) (by
      rw [← hlen]
      lia)
    have hup := listAlternates_get_lower halt (k := k) hk (by
      rw [← hlen]
      exact hk)
    have hss_rev :
        ss.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ =
          ss.get ⟨k, hk⟩ := by
      simp [k]
    have hrs_rev_lo :
        rs.reverse.get ⟨j.1 + 1, hj1⟩ =
          rs.get ⟨k - 1, by
            rw [← hlen]
            lia⟩ := by
      calc
        rs.reverse.get ⟨j.1 + 1, hj1⟩ =
            rs.get ⟨rs.length - 1 - (j.1 + 1), by
              have hrs_pos : 0 < rs.length := by
                have : 0 < rs.reverse.length := lt_of_le_of_lt (Nat.zero_le _) hj1
                simpa [List.length_reverse] using this
              lia⟩ := CommonInterleaver.RootSlots.get_reverse_eq_get_sub (xs := rs) (k := j.1 + 1)
                (by simpa [List.length_reverse] using hj1)
        _ = rs.get ⟨k - 1, by
              rw [← hlen]
              lia⟩ := by
              apply congrArg (fun i : Fin rs.length => rs.get i)
              apply Fin.ext
              simp [k, hlen]
              lia
    have hrs_rev_hi :
        rs.reverse.get ⟨j.1 + 1 - 1, hjpred⟩ =
          rs.get ⟨k, by
            rw [← hlen]
            exact hk⟩ := by
      calc
        rs.reverse.get ⟨j.1 + 1 - 1, hjpred⟩ =
            rs.get ⟨rs.length - 1 - (j.1 + 1 - 1), by
              have hrs_pos : 0 < rs.length := by
                have : 0 < rs.reverse.length := lt_of_le_of_lt (Nat.zero_le _) hjpred
                simpa [List.length_reverse] using this
              lia⟩ :=
            CommonInterleaver.RootSlots.get_reverse_eq_get_sub
              (xs := rs) (k := j.1 + 1 - 1) (by simpa [List.length_reverse] using hjpred)
        _ = rs.get ⟨k, by
              rw [← hlen]
              exact hk⟩ := by
              apply congrArg (fun i : Fin rs.length => rs.get i)
              apply Fin.ext
              simp [k, hlen]
    have hlow' :
        rs.get ⟨k - 1, by
          rw [← hlen]
          lia⟩ ≤ ss.get ⟨k, hk⟩ := by
      have hk_sub : k - 1 + 1 = k := by lia
      simpa [hk_sub] using hlow
    rw [hslot, hss_rev, hrs_rev_lo, hrs_rev_hi]
    exact ⟨hlow', hup⟩

protected lemma CommonInterleaver.RootSlots.mem_shifted_rootSlotInterval_of_prec
    {h f : ℝ[X]} (hhf : Prec h f) (j : Fin h.natDegree) :
    (rootSeqDesc h).get ⟨j.1, by
      rcases hhf with ⟨hh, _, _, _, _, _, _, _, _⟩
      simp [rootSeqDesc, card_roots_of_splits hh.2]⟩ ∈
      rootSlotInterval (rootSeqDesc f)
        ⟨j.1 + 1, by
          have hdeg := hhf.natDegree_le
          have hjf : j.1 < f.natDegree := lt_of_lt_of_le j.2 hdeg
          simpa [rootSeqDesc_length hhf.2.1.2] using Nat.succ_lt_succ hjf⟩ := by
  have hdeg_hhf := hhf.natDegree_le
  rcases hhf with ⟨hh, hf, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_desc : rootSeqDesc h = ss.reverse := rootSeqDesc_eq_reverse_of_pairwise hss hss_eq
  have hrs_desc : rootSeqDesc f = rs.reverse := rootSeqDesc_eq_reverse_of_pairwise hrs hrs_eq
  have hss_len : ss.length = h.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hh.2]
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  let jh_desc : Fin (rootSeqDesc h).length := ⟨j.1, by
    simp [rootSeqDesc, card_roots_of_splits hh.2]⟩
  let jh_rev : Fin ss.reverse.length := ⟨j.1, by
    simp [List.length_reverse, hss_len]⟩
  let jf_desc : Fin ((rootSeqDesc f).length + 1) := ⟨j.1 + 1, by
    have hdeg := hdeg_hhf
    have hjf : j.1 < f.natDegree := lt_of_lt_of_le j.2 hdeg
    simpa [rootSeqDesc_length hf.2] using Nat.succ_lt_succ hjf⟩
  let jf_rev : Fin (rs.reverse.length + 1) := ⟨j.1 + 1, by
    have hdeg := hdeg_hhf
    have hjf : j.1 < f.natDegree := lt_of_lt_of_le j.2 hdeg
    simpa [List.length_reverse, hrs_len] using Nat.succ_lt_succ hjf⟩
  have hmem_rev : ss.reverse.get jh_rev ∈ rootSlotInterval rs.reverse jf_rev := by
    rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
    · exact mem_shifted_rootSlotInterval_reverse_of_listInterlaces hlen hint
        ⟨j.1, by simp [hss_len, j.2]⟩
    · exact mem_shifted_rootSlotInterval_reverse_of_listAlternates hlen halt
        ⟨j.1, by simp [hss_len, j.2]⟩
  lia


end
end RealRooted
