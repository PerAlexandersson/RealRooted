module

import Mathlib.Analysis.Convex.Radon
import RealRooted.CommonInterleaver.RootSlots
public import RealRooted.CommonInterleaver.RootSlots.Basic
public import RealRooted.CommonInterleaver.RootDesc

/-!
# Common interleavers: finite families

Finite intersections of root-slot intervals, degree extrema for finite families,
and the pairwise root-slot intersection furnished by a common interleaver.
-/

@[expose] public section

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
  classical
  have htotal := Convex.helly_theorem_set' (𝕜 := ℝ) (F := ss.toFinset)
    (fun s hs => (convex_iff_ordConnected).2 (hconn s (List.mem_toFinset.mp hs)))
  have hsmall : ∀ G : Finset (Set ℝ), G ⊆ ss.toFinset → G.card ≤ 2 →
      (⋂₀ (G : Set (Set ℝ))).Nonempty := by
    intro G hG hc
    rcases lt_or_eq_of_le hc with hc | hc
    · obtain ⟨s, hs⟩ := Finset.card_le_one_iff_subset_singleton.mp (by lia : G.card ≤ 1)
      rcases G.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
      · simp
      · have heq : G = {t} := by
          ext u
          have hut : u ∈ G → u = t := fun hu =>
            Finset.mem_singleton.mp (hs hu) |>.trans (Finset.mem_singleton.mp (hs ht)).symm
          simp only [Finset.mem_singleton]
          exact ⟨hut, fun h => h ▸ ht⟩
        simpa only [heq, Finset.coe_singleton, Set.sInter_singleton] using
          hne t (List.mem_toFinset.mp (hG ht))
    · obtain ⟨s, t, hst, rfl⟩ := Finset.card_eq_two.mp hc
      have hs := List.mem_toFinset.mp (hG (by simp : s ∈ ({s, t} : Finset _)))
      have ht := List.mem_toFinset.mp (hG (by simp : t ∈ ({s, t} : Finset _)))
      have hpair' := hpair.forall_of_forall_of_flip
        (fun s hs => by simpa only [Set.inter_self] using hne s hs)
        (hpair.imp (by intro a b h; simpa only [flip, Set.inter_comm] using h)) hs ht
      simpa using hpair'
  obtain ⟨x, hx⟩ := htotal (by simpa only [Module.finrank_self] using hsmall)
  exact ⟨x, mem_listInter.mpr fun s hs => Set.mem_sInter.mp hx s (by simpa using hs)⟩

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
  have hmap : fs.map Polynomial.natDegree ≠ [] := by simpa using hfs
  have hm : csDegree fs ∈ fs.map Polynomial.natDegree :=
    List.maximum_mem (List.foldr_max_of_ne_nil hmap).symm
  obtain ⟨f, hf, heq⟩ := List.mem_map.mp hm
  exact ⟨f, hf, heq⟩

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

lemma leftCsDegree_le_natDegree {fs : List ℝ[X]} {f : ℝ[X]} (hf : f ∈ fs) :
    leftCsDegree fs ≤ f.natDegree := by
  unfold leftCsDegree
  exact List.min_le_of_le' _ (List.mem_map_of_mem (f := Polynomial.natDegree) hf) le_rfl

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
        have hseed_tail : ∀ a ∈ y :: ys, a ≤ seed :=
          fun a ha => hseed a (by simp [ha])
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
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
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
      simpa [x, jf, jh] using
        (CommonInterleaver.RootSlots.mem_rootSlotInterval_of_strictInterl hfh jh)
    have hmem_g : x ∈ rootSlotInterval (rootSeqDesc g) jg := by
      simpa [x, jg, jh] using
        (CommonInterleaver.RootSlots.mem_rootSlotInterval_of_strictInterl hgh jh)
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
