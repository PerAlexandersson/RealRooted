import RealRooted.CommonInterleaver.RootSlots

/-!
# Common interleavers: finite families

Finite intersections of root-slot intervals, degree extrema for finite families,
and the pairwise root-slot intersection furnished by a common interleaver.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

/-- Finite intersection of a list of sets. -/
def listInter : List (Set ℝ) → Set ℝ
  | [] => Set.univ
  | s :: ss => s ∩ listInter ss

lemma mem_listInter {ss : List (Set ℝ)} {x : ℝ} :
    x ∈ listInter ss ↔ ∀ s ∈ ss, x ∈ s := by
  induction ss with
  | nil =>
      simp [listInter]
  | cons s ss ih =>
      simp [listInter, ih]

/-- Finite Helly property for intervals on `ℝ`, formulated for `OrdConnected`
sets: a finite pairwise-intersecting family of intervals has nonempty total
intersection. -/
lemma listInter_nonempty_of_pairwise_ordConnected
    (ss : List (Set ℝ))
    (hne : ∀ s ∈ ss, s.Nonempty)
    (hconn : ∀ s ∈ ss, Set.OrdConnected s)
    (hpair : ss.Pairwise fun s t => (s ∩ t).Nonempty) :
    (listInter ss).Nonempty := by
  induction ss with
  | nil =>
      simp [listInter]
  | cons s ss ih =>
      cases ss with
      | nil =>
          simpa [listInter] using hne s (by simp)
      | cons t ts =>
          have hhead : ∀ u ∈ t :: ts, (s ∩ u).Nonempty := (List.pairwise_cons.mp hpair).1
          have htail : (t :: ts).Pairwise fun s t => (s ∩ t).Nonempty :=
            (List.pairwise_cons.mp hpair).2
          have htail_ne : (listInter (t :: ts)).Nonempty := by simp_all
          rcases htail_ne with ⟨x, hx⟩
          by_cases hxs : x ∈ s
          · exact ⟨x, by simpa [listInter, hxs] using hx⟩
          · let ys : List ℝ := (List.attach (t :: ts)).map
              (fun u => Classical.choose (hhead u.1 u.2))
            have hys_pos : 0 < ys.length := by simp [ys]
            have hy_mem_s : ∀ y ∈ ys, y ∈ s := by grind
            have hx_mem : ∀ u ∈ t :: ts, x ∈ u :=
              fun u hu => (mem_listInter.mp hx) u hu
            let y0 : ℝ := Classical.choose (hhead t (by simp))
            have hy0s : y0 ∈ s := (Classical.choose_spec (hhead t (by simp))).1
            have hy0_side : y0 < x ∨ x < y0 := by grind
            rcases hy0_side with hy0lt | hxy0
            · let y : ℝ := ys.maximum_of_length_pos hys_pos
              have hy_mem : y ∈ ys := List.maximum_of_length_pos_mem hys_pos
              have hys : y ∈ s := hy_mem_s y hy_mem
              have hall_lt : ∀ z ∈ ys, z < x := by
                intro z hz
                have hzs : z ∈ s := hy_mem_s z hz
                by_cases hzx : z < x
                · lia
                · have hxz : x < z := by grind
                  have hx_in_s : x ∈ s := (hconn s (by simp)).out hy0s hzs ⟨hy0lt.le, hxz.le⟩
                  lia
              refine ⟨y, ?_⟩
              rw [mem_listInter]
              intro u hu
              have hu' : u = s ∨ u ∈ t :: ts := by simp_all
              rcases hu' with rfl | hu
              · lia
              · let yu : ℝ := Classical.choose (hhead u hu)
                have hyu_mem : yu ∈ ys := by
                  have hmem_attach :
                      (⟨u, hu⟩ : {v // v ∈ t :: ts}) ∈ (t :: ts).attach := by
                    grind
                  grind
                have hyu_le : yu ≤ y := List.le_maximum_of_length_pos_of_mem hyu_mem hys_pos
                have hy_lt : y < x := hall_lt y hy_mem
                have hyu_u : yu ∈ u := (Classical.choose_spec (hhead u hu)).2
                have hx_u : x ∈ u := hx_mem u hu
                exact (hconn u (by lia)).out hyu_u hx_u ⟨hyu_le, hy_lt.le⟩
            · let y : ℝ := ys.minimum_of_length_pos hys_pos
              have hy_mem : y ∈ ys := List.minimum_of_length_pos_mem hys_pos
              have hys : y ∈ s := hy_mem_s y hy_mem
              have hall_gt : ∀ z ∈ ys, x < z := by
                intro z hz
                have hzs : z ∈ s := hy_mem_s z hz
                by_cases hxz : x < z
                · lia
                · have hzx : z < x := by grind
                  have hx_in_s : x ∈ s := (hconn s (by simp)).out hzs hy0s ⟨hzx.le, hxy0.le⟩
                  lia
              refine ⟨y, ?_⟩
              rw [mem_listInter]
              intro u hu
              have hu' : u = s ∨ u ∈ t :: ts := by simp_all
              rcases hu' with rfl | hu
              · lia
              · let yu : ℝ := Classical.choose (hhead u hu)
                have hyu_mem : yu ∈ ys := by
                  have hmem_attach :
                      (⟨u, hu⟩ : {v // v ∈ t :: ts}) ∈ (t :: ts).attach := by
                    grind
                  grind
                have hle_yu : y ≤ yu := List.minimum_of_length_pos_le_of_mem hyu_mem hys_pos
                have hx_lt : x < y := hall_gt y hy_mem
                have hyu_u : yu ∈ u := (Classical.choose_spec (hhead u hu)).2
                have hx_u : x ∈ u := hx_mem u hu
                exact (hconn u (by lia)).out hx_u hyu_u ⟨hx_lt.le, hle_yu⟩

/-- The target length `d` in the Chudnovsky--Seymour construction: the maximum
degree occurring in the family. -/
def csDegree (fs : List ℝ[X]) : ℕ :=
  (fs.map Polynomial.natDegree).foldr max 0

lemma natDegree_le_csDegree {fs : List ℝ[X]} {f : ℝ[X]} (hf : f ∈ fs) :
    f.natDegree ≤ csDegree fs := by
  unfold csDegree
  exact List.le_max_of_le (by grind) le_rfl

lemma csDegree_eq_zero_of_nil : csDegree ([] : List ℝ[X]) = 0 := by simp [csDegree]

lemma exists_mem_csDegree_of_ne_nil {fs : List ℝ[X]} (hfs : fs ≠ []) :
    ∃ f ∈ fs, f.natDegree = csDegree fs := by
  induction fs with
  | nil =>
      lia
  | cons f fs ih =>
      cases fs with
      | nil =>
          refine ⟨f, by simp, by simp [csDegree]⟩
      | cons g gs =>
          by_cases htail : csDegree (g :: gs) ≤ f.natDegree
          · refine ⟨f, by simp, ?_⟩
            simpa [csDegree] using htail
          · have hne_tail : g :: gs ≠ [] := by lia
            obtain ⟨p, hp, hpdeg⟩ := ih hne_tail
            refine ⟨p, by simp [hp], ?_⟩
            have hltail : f.natDegree ≤ csDegree (g :: gs) := by lia
            rw [hpdeg]
            simpa [csDegree] using hltail

lemma natDegree_ge_csDegree_sub_one_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]} {f g : ℝ[X]}
    (hf : f ∈ fs) (hg : g ∈ fs)
    (hpair : PairwiseHasCommonInterleaver fs) :
    f.natDegree ≤ g.natDegree + 1 := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
  obtain ⟨j, hgj⟩ := List.mem_iff_get.1 hg
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨h, hfh, hgh⟩ := hpair i j hij
    rw [← hgj]
    exact le_trans hfh.natDegree_le hgh.natDegree_le_succ
  · lia
  · obtain ⟨h, hgh, hfh⟩ := hpair j i hji
    rw [← hgj]
    exact le_trans hfh.natDegree_le hgh.natDegree_le_succ

lemma csDegree_le_natDegree_succ_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]} {f : ℝ[X]}
    (hfs : fs ≠ [])
    (hf : f ∈ fs)
    (hpair : PairwiseHasCommonInterleaver fs) :
    csDegree fs ≤ f.natDegree + 1 := by
  obtain ⟨g, hg, hgmax⟩ := exists_mem_csDegree_of_ne_nil hfs
  have hbound :=
    natDegree_ge_csDegree_sub_one_of_pairwiseHasCommonInterleaver (f := g) (g := f) hg hf hpair
  lia

/-! ### Left-oriented degree bookkeeping -/

/-- The target length for a common left interleaver: the minimum degree
occurring in the family. -/
def leftCsDegree (fs : List ℝ[X]) : ℕ :=
  (fs.map Polynomial.natDegree).foldr Nat.min (csDegree fs)

private lemma foldr_min_le_of_mem {xs : List ℕ} {a seed : ℕ} (ha : a ∈ xs) :
    xs.foldr Nat.min seed ≤ a := by
  induction xs with
  | nil =>
      simp_all
  | cons x xs ih =>
      simp only [List.foldr_cons, List.mem_cons] at ha ⊢
      rcases ha with rfl | ha
      · exact Nat.min_le_left a (xs.foldr Nat.min seed)
      · exact le_trans (Nat.min_le_right x (xs.foldr Nat.min seed)) (ih ha)

lemma leftCsDegree_le_natDegree {fs : List ℝ[X]} {f : ℝ[X]} (hf : f ∈ fs) :
    leftCsDegree fs ≤ f.natDegree := by
  unfold leftCsDegree
  exact foldr_min_le_of_mem (List.mem_map_of_mem (f := Polynomial.natDegree) hf)

private lemma exists_mem_eq_foldr_min_of_forall_le
    {xs : List ℕ} {seed : ℕ} (hxs : xs ≠ []) (hseed : ∀ a ∈ xs, a ≤ seed) :
    ∃ a ∈ xs, a = xs.foldr Nat.min seed := by
  induction xs with
  | nil =>
      simp_all
  | cons x xs ih =>
      cases xs with
      | nil =>
        refine ⟨x, by simp, ?_⟩
        simp [List.foldr_cons, Nat.min_eq_left (hseed x (by simp))]
      | cons y ys =>
        have hseed_tail : ∀ a ∈ y :: ys, a ≤ seed := by
          intro a ha
          exact hseed a (by simp [ha])
        obtain ⟨a, ha, haeq⟩ := ih (by simp) hseed_tail
        by_cases hx : x ≤ (y :: ys).foldr Nat.min seed
        · refine ⟨x, by simp, ?_⟩
          exact (Nat.min_eq_left hx).symm
        · refine ⟨a, by simp [ha], ?_⟩
          have hle : (y :: ys).foldr Nat.min seed ≤ x := by lia
          exact haeq.trans (Nat.min_eq_right hle).symm

lemma exists_mem_leftCsDegree_of_ne_nil {fs : List ℝ[X]} (hfs : fs ≠ []) :
    ∃ f ∈ fs, f.natDegree = leftCsDegree fs := by
  have hmap_ne : fs.map Polynomial.natDegree ≠ [] := by simpa using hfs
  have hseed : ∀ a ∈ fs.map Polynomial.natDegree, a ≤ csDegree fs := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨f, hf, rfl⟩
    exact natDegree_le_csDegree hf
  obtain ⟨d, hd, hd_eq⟩ := exists_mem_eq_foldr_min_of_forall_le hmap_ne hseed
  rcases List.mem_map.mp hd with ⟨f, hf, rfl⟩
  exact ⟨f, hf, hd_eq⟩

lemma natDegree_le_natDegree_succ_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]} {f g : ℝ[X]}
    (hf : f ∈ fs) (hg : g ∈ fs)
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    f.natDegree ≤ g.natDegree + 1 := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
  obtain ⟨j, hgj⟩ := List.mem_iff_get.1 hg
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨h, hhf, hhg⟩ := hpair i j hij
    rw [← hgj]
    exact le_trans hhf.natDegree_le_succ <| Nat.succ_le_succ hhg.natDegree_le
  · lia
  · obtain ⟨h, hhg, hhf⟩ := hpair j i hji
    rw [← hgj]
    exact le_trans hhf.natDegree_le_succ <| Nat.succ_le_succ hhg.natDegree_le

lemma natDegree_le_leftCsDegree_succ_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]} {f : ℝ[X]}
    (hfs : fs ≠ [])
    (hf : f ∈ fs)
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    f.natDegree ≤ leftCsDegree fs + 1 := by
  obtain ⟨g, hg, hgmin⟩ := exists_mem_leftCsDegree_of_ne_nil hfs
  have hbound :=
    natDegree_le_natDegree_succ_of_pairwiseHasCommonLeftInterleaver
      (f := f) (g := g) hf hg hpair
  lia

/-- Pairwise slot intersection for a pair of polynomials sharing a common
interleaver on the right. This is the local input needed for the finite-Helly
step in the Chudnovsky--Seymour proof. -/
theorem rootSlotInterval_inter_nonempty_of_commonInterleaver
    {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (j : ℕ)
    (hjf : j < f.natDegree + 1)
    (hjg : j < g.natDegree + 1) :
    (rootSlotInterval (rootSeqDesc f)
        ⟨j, by simpa [hfh.1.2] using hjf⟩ ∩
      rootSlotInterval (rootSeqDesc g)
        ⟨j, by simpa [hgh.1.2] using hjg⟩).Nonempty := by
  let jf : Fin ((rootSeqDesc f).length + 1) := ⟨j, by simpa [hfh.1.2] using hjf⟩
  let jg : Fin ((rootSeqDesc g).length + 1) := ⟨j, by simpa [hgh.1.2] using hjg⟩
  change (rootSlotInterval (rootSeqDesc f) jf ∩
    rootSlotInterval (rootSeqDesc g) jg).Nonempty
  have hfh_lower := hfh.natDegree_le
  have hfh_upper := hfh.natDegree_le_succ
  have hgh_lower := hgh.natDegree_le
  have hgh_upper := hgh.natDegree_le_succ
  by_cases hjh : j < h.natDegree
  · let jh : Fin h.natDegree := ⟨j, hjh⟩
    let x : ℝ := (rootSeqDesc h).get ⟨j, by
      simpa [hfh.2.1.2] using hjh⟩
    have hmem_f : x ∈ rootSlotInterval (rootSeqDesc f) jf := by
      simpa [x, jf, jh] using (CommonInterleaver.RootSlots.mem_rootSlotInterval_of_prec hfh jh)
    have hmem_g : x ∈ rootSlotInterval (rootSeqDesc g) jg := by
      simpa [x, jg, jh] using (CommonInterleaver.RootSlots.mem_rootSlotInterval_of_prec hgh jh)
    exact ⟨x, ⟨hmem_f, hmem_g⟩⟩
  · have hj_eq_h : j = h.natDegree := by lia
    have hf_eq_h : f.natDegree = h.natDegree := by lia
    have hg_eq_h : g.natDegree = h.natDegree := by lia
    by_cases hdeg0 : h.natDegree = 0
    · have hj0 : j = 0 := by lia
      have hf0 : f.natDegree = 0 := by lia
      have hg0 : g.natDegree = 0 := by lia
      have hf_len0 : (rootSeqDesc f).length = 0 := by simp [hf0, hfh.1.2]
      have hg_len0 : (rootSeqDesc g).length = 0 := by simp [hg0, hgh.1.2]
      exact
        CommonInterleaver.RootSlots.rootSlotInterval_inter_nonempty_of_lengths_eq_zero
          hf_len0 hg_len0 jf jg
    · have hf_pos : 0 < f.natDegree := by lia
      have hg_pos : 0 < g.natDegree := by lia
      have hrevf_ne : (rootSeqDesc f).reverse ≠ [] :=
        CommonInterleaver.rootSeqDesc_reverse_ne_nil_of_natDegree_pos hfh.1.2 hf_pos
      have hrevg_ne : (rootSeqDesc g).reverse ≠ [] :=
        CommonInterleaver.rootSeqDesc_reverse_ne_nil_of_natDegree_pos hgh.1.2 hg_pos
      let af : ℝ := ((rootSeqDesc f).reverse).get
        ⟨0, by grind⟩
      let ag : ℝ := ((rootSeqDesc g).reverse).get
        ⟨0, by grind⟩
      have hslot_f :
          rootSlotInterval (rootSeqDesc f) jf = Set.Iic af := by
        simpa [af, jf, hj_eq_h, hf_eq_h, hfh.1.2] using
          CommonInterleaver.RootSlots.rootSlotInterval_last_eq_reverse_get_zero
            (rs := rootSeqDesc f) (List.reverse_ne_nil_iff.mp hrevf_ne)
      have hslot_g :
          rootSlotInterval (rootSeqDesc g) jg = Set.Iic ag := by
        simpa [ag, jg, hj_eq_h, hg_eq_h, hgh.1.2] using
          CommonInterleaver.RootSlots.rootSlotInterval_last_eq_reverse_get_zero
            (rs := rootSeqDesc g) (List.reverse_ne_nil_iff.mp hrevg_ne)
      simp_all


end
end RealRooted
