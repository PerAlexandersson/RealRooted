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

private lemma getD_eq_get_of_lt (xs : List ℝ) (i : ℕ) (hi : i < xs.length) :
    xs.getD i 0 = xs.get ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

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
  apply listInterlaces_of_getD_bounds ss rs hlen
  · intro k hk
    rw [getD_eq_get_of_lt rs k (by lia), getD_eq_get_of_lt ss k hk]
    exact hlower k hk
  · intro k hk
    rw [getD_eq_get_of_lt ss k hk, getD_eq_get_of_lt rs (k + 1) (by lia)]
    exact hupper k hk

protected lemma CommonInterleaver.RootSlots.listAlternates_of_index_bounds
    {ss rs : List ℝ}
    (hlen : ss.length = rs.length)
    (hlower : ∀ k (hk : k < ss.length),
      ss.get ⟨k, hk⟩ ≤ rs.get ⟨k, by lia⟩)
    (hupper : ∀ k (hk : k + 1 < ss.length),
      rs.get ⟨k, by
        lia⟩ ≤ ss.get ⟨k + 1, hk⟩) :
    ListAlternates ss rs := by
  apply listAlternates_of_getD_bounds ss rs hlen
  · intro k hk
    rw [getD_eq_get_of_lt ss k hk, getD_eq_get_of_lt rs k (by lia)]
    exact hlower k hk
  · intro k hk
    rw [getD_eq_get_of_lt rs k (by lia), getD_eq_get_of_lt ss (k + 1) hk]
    exact hupper k hk

/-- Slot transport from an ascending `StrictInterl` witness to the descending
Chudnovsky--Seymour interval language. This is the core bridge needed to turn
pairwise common interleavers into pairwise-intersecting slot intervals. -/
private lemma mem_rootSlotInterval_of_strictInterl_witness
    {ss rs : List ℝ}
    (hshape : (ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs))
    (j : Fin rs.length) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈
      rootSlotInterval ss.reverse
        ⟨j.1, by
          grind⟩ := by
  obtain ⟨hlower, hupper⟩ := desc_bounds_of_interlacing_shape ss rs hshape
  have hrs : rs ≠ [] := List.length_pos_iff_ne_nil.mp (by have := j.2; lia)
  by_cases h0 : j.1 = 0
  · have hmem : rs.reverse.get ⟨0, by simp; lia⟩ ∈
        rootSlotInterval ss.reverse ⟨0, by simp⟩ := by
      by_cases hss : ss = []
      · subst ss
        simp [rootSlotInterval]
      · rw [CommonInterleaver.RootSlots.rootSlotInterval_reverse_zero hss,
          CommonInterleaver.RootSlots.reverse_get_zero_eq_getLast hrs]
        apply Set.mem_Ici.mpr
        have hb := hlower 0 (List.length_pos_iff_ne_nil.mpr hss)
        rw [getD_eq_get_of_lt ss.reverse 0 (by
            simpa only [List.length_reverse] using List.length_pos_iff_ne_nil.mpr hss),
          getD_eq_get_of_lt rs.reverse 0 (by
            simpa only [List.length_reverse] using List.length_pos_iff_ne_nil.mpr hrs),
          CommonInterleaver.RootSlots.reverse_get_zero_eq_getLast hss,
          CommonInterleaver.RootSlots.reverse_get_zero_eq_getLast hrs] at hb
        exact hb
    simpa only [h0] using hmem
  · by_cases hlast : j.1 = ss.length
    · have hslt : ss.length < rs.length := by lia
      have hmem : rs.reverse.get ⟨ss.length, by
            simpa only [List.length_reverse] using hslt⟩ ∈
          rootSlotInterval ss.reverse ⟨ss.length, by simp⟩ := by
        have hss : ss ≠ [] := List.length_pos_iff_ne_nil.mp (by lia)
        rw [CommonInterleaver.RootSlots.rootSlotInterval_reverse_last hss]
        apply Set.mem_Iic.mpr
        have hj : ss.length - 1 < ss.length := by lia
        have hjr : ss.length - 1 + 1 < rs.length := by lia
        have hb := hupper (ss.length - 1) hj hjr
        rw [getD_eq_get_of_lt rs.reverse (ss.length - 1 + 1)
            (by simpa only [List.length_reverse] using hjr),
          getD_eq_get_of_lt ss.reverse (ss.length - 1)
            (by simpa only [List.length_reverse] using hj)] at hb
        simp only [show ss.length - 1 + 1 = ss.length by lia] at hb
        simpa using hb
      simpa only [hlast] using hmem
    · rw [show rootSlotInterval ss.reverse
          ⟨j.1, by grind⟩ =
          Set.Icc (ss.reverse.get ⟨j.1, by simp; lia⟩)
            (ss.reverse.get ⟨j.1 - 1, by simp; lia⟩) by
        simp [rootSlotInterval, h0, hlast]]
      have hj : j.1 < ss.length := by lia
      have hj' : j.1 - 1 < ss.length := by lia
      have hjr : j.1 - 1 + 1 < rs.length := by lia
      constructor
      · have hb := hlower j.1 hj
        rw [getD_eq_get_of_lt ss.reverse j.1 (by simpa using hj),
          getD_eq_get_of_lt rs.reverse j.1 (by simp)] at hb
        exact hb
      · have hb := hupper (j.1 - 1) hj' hjr
        rw [getD_eq_get_of_lt rs.reverse (j.1 - 1 + 1) (by simpa using hjr),
          getD_eq_get_of_lt ss.reverse (j.1 - 1) (by simpa using hj')] at hb
        have hidx :
            (⟨j.1 - 1 + 1, by simpa using hjr⟩ : Fin rs.reverse.length) =
              ⟨j.1, by simp⟩ := Fin.ext (by lia)
        rw [hidx] at hb
        exact hb

protected lemma CommonInterleaver.RootSlots.mem_rootSlotInterval_of_strictInterl
    {f g : ℝ[X]} (hfg : StrictInterl f g) (j : Fin g.natDegree) :
    (rootSeqDesc g).get ⟨j.1, by
      rcases hfg with ⟨_, hg, _, _, _, _, _, _, _⟩
      simp [rootSeqDesc, Polynomial.splits_iff_card_roots.mp hg.2]⟩ ∈
        rootSlotInterval (rootSeqDesc f)
      ⟨j.1, by
        have hdeg := hfg.natDegree_le_succ
        rcases hfg with ⟨hf, hg, _, _, _, _, _, _, _⟩
        simpa [hf.2, hg.2] using lt_of_lt_of_le j.2 hdeg⟩ := by
  have hdeg := hfg.natDegree_le_succ
  rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_desc : rootSeqDesc f = ss.reverse := rootSeqDesc_eq_reverse_of_pairwise hss hss_eq
  have hrs_desc : rootSeqDesc g = rs.reverse := rootSeqDesc_eq_reverse_of_pairwise hrs hrs_eq
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, Polynomial.splits_iff_card_roots.mp hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, Polynomial.splits_iff_card_roots.mp hg.2]
  let jg_desc : Fin (rootSeqDesc g).length := ⟨j.1, by
    simp [rootSeqDesc, Polynomial.splits_iff_card_roots.mp hg.2]⟩
  let jg_rev : Fin rs.reverse.length := ⟨j.1, by
    simp [List.length_reverse, hrs_len]⟩
  let jf_desc : Fin ((rootSeqDesc f).length + 1) := ⟨j.1, by
    grind⟩
  let jf_rev : Fin (ss.reverse.length + 1) := ⟨j.1, by
    grind⟩
  have hmem_rev : rs.reverse.get jg_rev ∈ rootSlotInterval ss.reverse jf_rev :=
    mem_rootSlotInterval_of_strictInterl_witness hshape ⟨j.1, by lia⟩
  lia

private lemma mem_shifted_rootSlotInterval_of_strictInterl_witness
    {ss rs : List ℝ}
    (hshape : (ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs))
    (j : Fin ss.length) :
    ss.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈
      rootSlotInterval rs.reverse
        ⟨j.1 + 1, by
          simp [List.length_reverse]
          lia⟩ := by
  obtain ⟨hupper, hlower⟩ := desc_bounds_of_interlacing_shape ss rs hshape
  by_cases hlast : j.1 + 1 = rs.length
  · have hrs : rs ≠ [] := by
      intro hrs
      simp [hrs] at hlast
    have hidx :
        (⟨j.1 + 1, by simp [List.length_reverse]; lia⟩ : Fin (rs.reverse.length + 1)) =
          ⟨rs.length, by simp⟩ := Fin.ext (by simp [hlast])
    rw [hidx, CommonInterleaver.RootSlots.rootSlotInterval_reverse_last hrs]
    apply Set.mem_Iic.mpr
    have hb := hupper j.1 j.2
    rw [getD_eq_get_of_lt ss.reverse j.1 (by simp),
      getD_eq_get_of_lt rs.reverse j.1 (by simp; lia)] at hb
    simpa [hlast] using hb
  · rw [show rootSlotInterval rs.reverse
          ⟨j.1 + 1, by simp [List.length_reverse]; lia⟩ =
          Set.Icc (rs.reverse.get ⟨j.1 + 1, by simp; lia⟩)
            (rs.reverse.get ⟨j.1, by simp; lia⟩) by
        simp [rootSlotInterval, hlast]]
    have hjr : j.1 + 1 < rs.length := by lia
    constructor
    · have hb := hlower j.1 j.2 hjr
      rw [getD_eq_get_of_lt rs.reverse (j.1 + 1)
          (by simpa only [List.length_reverse] using hjr),
        getD_eq_get_of_lt ss.reverse j.1 (by simp)] at hb
      exact hb
    · have hb := hupper j.1 j.2
      rw [getD_eq_get_of_lt ss.reverse j.1 (by simp),
        getD_eq_get_of_lt rs.reverse j.1 (by simp; lia)] at hb
      exact hb

protected lemma CommonInterleaver.RootSlots.mem_shifted_rootSlotInterval_of_strictInterl
    {h f : ℝ[X]} (hhf : StrictInterl h f) (j : Fin h.natDegree) :
    (rootSeqDesc h).get ⟨j.1, by
      rcases hhf with ⟨hh, _, _, _, _, _, _, _, _⟩
      simp [rootSeqDesc, Polynomial.splits_iff_card_roots.mp hh.2]⟩ ∈
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
    rw [← Multiset.coe_card, hss_eq, Polynomial.splits_iff_card_roots.mp hh.2]
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, Polynomial.splits_iff_card_roots.mp hf.2]
  let jh_desc : Fin (rootSeqDesc h).length := ⟨j.1, by
    simp [rootSeqDesc, Polynomial.splits_iff_card_roots.mp hh.2]⟩
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
    exact mem_shifted_rootSlotInterval_of_strictInterl_witness hshape
      ⟨j.1, by simp [hss_len, j.2]⟩
  lia

end
end RealRooted
