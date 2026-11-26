/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.CommonInterleaver.PairBridge.Compatibility
public import RealRooted.CommonInterleaver.RootDesc
import RealRooted.CommonInterleaver.SameDegreeRootCount
import Mathlib.Tactic

/-!
# Strict root-slot separation for simple positive pencils

Compatibility gives weak root-slot inequalities. If every positive pencil has
simple roots, adjacent slots of different endpoints cannot touch.
-/

public section

noncomputable section

open Polynomial

namespace RealRooted

private theorem length_filter_gt_get {l : List ℝ} (hs : l.Pairwise (· > ·))
    (i : Fin l.length) : (l.filter (l.get i < ·)).length = i.val := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hs
    refine Fin.cases ?_ (fun j => ?_) i
    · have he : l.filter (a < ·) = [] := List.filter_eq_nil_iff.mpr (by
        intro x hx
        simpa only [decide_eq_true_eq] using not_lt.mpr (ha x hx).le)
      change (List.filter (fun x => decide (a < x)) (a :: l)).length = 0
      rw [List.filter_cons_of_neg (by simp), he]
      rfl
    · have hja : l.get j < a := ha _ (List.get_mem ..)
      change (List.filter (fun x => decide (l.get j < x)) (a :: l)).length = j.val + 1
      rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using hja)]
      exact congrArg (· + 1) (ih hl j)

/-- Simple roots make the canonical descending root list strictly decreasing. -/
theorem rootSeqDesc_pairwise_gt {p : ℝ[X]} (hn : p.roots.Nodup) :
    (rootSeqDesc p).Pairwise (· > ·) := by
  have hcoe : (rootSeqDesc p : Multiset ℝ) = p.roots := by simp [rootSeqDesc]
  have hnd : (rootSeqDesc p).Nodup := by
    rw [← Multiset.coe_nodup, hcoe]
    exact hn
  apply List.pairwise_iff_get.mpr
  intro i j hij
  exact lt_of_le_of_ne (List.pairwise_iff_get.mp rootSeqDesc_pairwise i j hij)
    (Ne.symm (hnd.injective_get.ne (ne_of_lt hij)))

/-- Exactly the preceding indices lie above a simple root in descending order. -/
theorem card_roots_gt_rootSeqDesc_get {p : ℝ[X]} (hn : p.roots.Nodup)
    (i : Fin (rootSeqDesc p).length) :
    (p.roots.filter ((rootSeqDesc p).get i < ·)).card = i.val := by
  have hcoe : (rootSeqDesc p : Multiset ℝ) = p.roots := by simp [rootSeqDesc]
  rw [← hcoe]
  exact length_filter_gt_get (rootSeqDesc_pairwise_gt hn) i

/-- A valid descending-root entry is a root, independently of splitting. -/
theorem rootSeqDesc_getD_mem_roots {p : ℝ[X]} {j : ℕ}
    (hj : j < (rootSeqDesc p).length) : (rootSeqDesc p).getD j 0 ∈ p.roots := by
  have hh := List.get_mem (rootSeqDesc p) ⟨j, hj⟩
  have he : (rootSeqDesc p).getD j 0 = (rootSeqDesc p).get ⟨j, hj⟩ := by
    simp [hj]
  rw [he]
  simpa only [rootSeqDesc, List.mem_reverse, Multiset.mem_sort] using hh

private theorem length_filter_gt_gap {l : List ℝ} (hs : l.Pairwise (· > ·))
    (j : Fin l.length) (c : ℝ) (hc : c < l.get j)
    (hnext : ∀ h : j.val + 1 < l.length, l.get ⟨j.val + 1, h⟩ < c) :
    (l.filter (c < ·)).length = j.val + 1 := by
  induction l with
  | nil => exact Fin.elim0 j
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hs
    revert hc hnext
    refine Fin.cases ?_ (fun i => ?_) j
    · intro hc hnext
      change c < a at hc
      have ht : l.filter (c < ·) = [] := by
        cases l with
        | nil => rfl
        | cons b bs =>
          have hb : b < c := hnext (by simp)
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          have hxlt : x < c := by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hb
            · exact ((List.pairwise_cons.mp hl).1 x hx).trans hb
          simpa only [decide_eq_true_eq] using not_lt.mpr hxlt.le
      change (List.filter (fun x => decide (c < x)) (a :: l)).length = 1
      rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using hc), ht]
      rfl
    · intro hc hnext
      have hac : c < a := hc.trans (ha _ (List.get_mem ..))
      change (List.filter (fun x => decide (c < x)) (a :: l)).length = i.val + 1 + 1
      rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using hac)]
      apply congrArg (· + 1)
      exact ih hl i hc (fun h => hnext (by simpa using h))

/-- The upper root count at a point strictly in the gap after root `j`. -/
theorem card_roots_gt_of_rootSeqDesc_gap {p : ℝ[X]} (hn : p.roots.Nodup)
    (j : Fin (rootSeqDesc p).length) (c : ℝ)
    (hc : c < (rootSeqDesc p).get j)
    (hnext : ∀ h : j.val + 1 < (rootSeqDesc p).length,
      (rootSeqDesc p).get ⟨j.val + 1, h⟩ < c) :
    (p.roots.filter (c < ·)).card = j.val + 1 := by
  have hcoe : (rootSeqDesc p : Multiset ℝ) = p.roots := by simp [rootSeqDesc]
  rw [← hcoe]
  exact length_filter_gt_gap (rootSeqDesc_pairwise_gt hn) j c hc hnext

private theorem quotient_at_simple_root {p : ℝ[X]} (hp : p.Splits)
    (hpos : 0 < p.leadingCoeff) (hn : p.roots.Nodup) {c : ℝ} (hc : p.IsRoot c) :
    ∃ q : ℝ[X], p = (X - C c) * q ∧ q.Splits ∧ 0 < q.leadingCoeff ∧
      ¬ q.IsRoot c ∧ (q.roots.filter (c < ·)).card = (p.roots.filter (c < ·)).card := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hc
  have hpn : p ≠ 0 := by intro hz; simp [hz] at hpos
  have hqn : q ≠ 0 := by intro hz; simp only [hz, mul_zero] at hq; exact hpn hq
  have hr : p.roots = c ::ₘ q.roots := by
    rw [hq, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hqn), roots_X_sub_C]
    rfl
  have hnc : c ∉ q.roots := by rw [hr, Multiset.nodup_cons] at hn; exact hn.1
  refine ⟨q, hq, hp.of_dvd hpn (hq ▸ dvd_mul_left q (X - C c)), ?_, ?_, ?_⟩
  · have he := congrArg leadingCoeff hq
    simp only [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul] at he
    rwa [← he]
  · exact fun hh => hnc ((mem_roots hqn).mpr hh)
  · simp [hr]

/-- For equally sized compatible nonnegative polynomials, simplicity of all
positive pencils makes the adjacent cross-slot inequalities strict. -/
theorem rootSeqDesc_getD_lt_of_simple_posCombo {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g) (hdeg : f.natDegree = g.natDegree)
    (hfn : f.roots.Nodup) (hgn : g.roots.Nodup)
    (hsimple : ∀ u : ℝ, 0 < u → (f + C u * g).roots.Nodup)
    {j : ℕ} (hj : 0 < j) (hjd : j < f.natDegree) :
    (rootSeqDesc f).getD j 0 < (rootSeqDesc g).getD (j - 1) 0 := by
  obtain ⟨h, hfh, hgh⟩ := posComboPairHasCommonInterleaver_of_nonnegCoeffs hf hg hfnn hgnn hfg
  obtain ⟨hfdata, hhdata, hhd, hfl, hfr⟩ := strictInterl_iff_rootSeqDesc.mp hfh
  obtain ⟨hgdata, _, _, hgl, hgr⟩ := strictInterl_iff_rootSeqDesc.mp hgh
  have hjh : j < h.natDegree := by rcases hhd with hh | hh <;> lia
  have hweak := (hfl j hjd).trans (by
    simpa only [Nat.sub_add_cancel hj] using hgr (j - 1) (by lia) (by lia))
  apply lt_of_le_of_ne hweak
  intro he
  let c := (rootSeqDesc f).getD j 0
  have hflength := rootSeqDesc_length hfdata.2
  have hglength := rootSeqDesc_length hgdata.2
  have hfi : (rootSeqDesc f).get ⟨j, by lia⟩ = c := by
    simp [c, show j < (rootSeqDesc f).length by lia]
  have hgi : (rootSeqDesc g).get ⟨j - 1, by lia⟩ = c := by
    simp only [List.get_eq_getElem] at he ⊢
    simpa [c, List.getD_eq_getElem, show j < (rootSeqDesc f).length by lia,
      show j - 1 < (rootSeqDesc g).length by lia] using he.symm
  have hfroot : f.IsRoot c := (mem_roots hf.ne_zero).mp (by
    rw [← hfi]
    have hh := List.get_mem (rootSeqDesc f) ⟨j, by lia⟩
    simpa only [rootSeqDesc, List.mem_reverse, Multiset.mem_sort] using hh)
  have hgroot : g.IsRoot c := (mem_roots hg.ne_zero).mp (by
    rw [← hgi]
    have hh := List.get_mem (rootSeqDesc g) ⟨j - 1, by lia⟩
    simpa only [rootSeqDesc, List.mem_reverse, Multiset.mem_sort] using hh)
  obtain ⟨q, hq, hqs, hqlc, hqc, hqcount⟩ :=
    quotient_at_simple_root hfdata.2 hf hfn hfroot
  obtain ⟨r, hr, hrs, hrlc, hrc, hrcount⟩ :=
    quotient_at_simple_root hgdata.2 hg hgn hgroot
  have hfc : (f.roots.filter (c < ·)).card = j := by
    simpa only [hfi] using card_roots_gt_rootSeqDesc_get hfn ⟨j, by lia⟩
  have hgc : (g.roots.filter (c < ·)).card = j - 1 := by
    simpa only [hgi] using card_roots_gt_rootSeqDesc_get hgn ⟨j - 1, by lia⟩
  have hodd : Odd ((q.roots.filter (c < ·)).card + (r.roots.filter (c < ·)).card) := by
    rw [hqcount, hrcount, hfc, hgc]
    exact ⟨j - 1, by lia⟩
  obtain ⟨u, hμ, hμroot⟩ :=
    (sameDegree_odd_card_roots_gt_add_iff_exists_pos_isRoot_add_right
      hqs hrs hqlc hrlc hqc hrc).mp hodd
  have hcomb : f + C u * g = (X - C c) * (q + C u * r) := by rw [hq, hr]; ring
  have hcombne : q + C u * r ≠ 0 := by
    intro hz
    have hn := (hfg (by positivity : (0 : ℝ) < 1) hμ).1
    simp [hcomb, hz] at hn
  have hnodup := hsimple u hμ
  rw [hcomb, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hcombne), roots_X_sub_C,
    Multiset.singleton_add, Multiset.nodup_cons] at hnodup
  exact hnodup.1 ((mem_roots hcombne).mpr hμroot)

end RealRooted
