module

import RealRooted.Wronskian.Successor.Signs
import RealRooted.Bezoutian.WronskianConverse
import RealRooted.Bezoutian.RootEvaluation
public import RealRooted.Basic.Coefficients

/-!
# Successor-degree Wronskian splitness transfer

A strict Wronskian sign transfers splitness from a positive-leading polynomial
to its one-degree-higher companion.
-/

public section

open Polynomial

namespace RealRooted

/-- Alternating signs on an ordered tuple force a root in every consecutive gap. -/
private lemma exists_root_between_of_alternating_signs {n : ℕ} {g : ℝ[X]}
    (s : Fin (n + 1) → ℝ) (hs_mono : StrictMono s)
    (hsgn : ∀ k : Fin (n + 1), g.eval (s k) * (-1) ^ (n - k.val) < 0) :
    ∀ k : Fin n, ∃ x, s k.castSucc < x ∧ x < s k.succ ∧ g.IsRoot x := by
  intro k
  have hlt : s k.castSucc < s k.succ := hs_mono (by simp)
  have hsc := hsgn k.castSucc
  have hss := hsgn k.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at hsc hss
  rcases Nat.even_or_odd (n - k.val) with hpar | hpar
  · have hkk : n - k.val = n - (k.val + 1) + 1 := by grind
    rw [hpar.neg_one_pow] at hsc
    have hpar' : Odd (n - (k.val + 1)) := by grind
    rw [hpar'.neg_one_pow] at hss
    obtain ⟨x, hx1, hx2, hx3⟩ :=
      exists_root_between_of_eval_neg_pos _ _ hlt (by linarith) (by nlinarith)
    grind
  · have hkk : n - k.val = n - (k.val + 1) + 1 := by grind
    rw [hpar.neg_one_pow] at hsc
    have hpar' : Even (n - (k.val + 1)) := by grind
    rw [hpar'.neg_one_pow] at hss
    obtain ⟨x, hx1, hx2, hx3⟩ :=
      exists_root_between_of_eval_pos_neg _ _ hlt (by nlinarith) (by linarith)
    grind

/-- Roots before, between, and after an ordered tuple account for the full degree. -/
private lemma splits_of_roots_around_strictMono {n : ℕ} {g : ℝ[X]}
    (hg_deg : g.natDegree = n + 2) (s : Fin (n + 1) → ℝ) (hs_mono : StrictMono s)
    (hbelow : ∃ x, x < s 0 ∧ g.IsRoot x)
    (habove : ∃ x, s (Fin.last n) < x ∧ g.IsRoot x)
    (hinternal : ∀ k : Fin n, ∃ x, s k.castSucc < x ∧ x < s k.succ ∧ g.IsRoot x) :
    g.Splits := by
  obtain ⟨xb, hxb_lt, hxb_root⟩ := hbelow
  obtain ⟨xa, hxa_gt, hxa_root⟩ := habove
  choose xi hxi_lo hxi_hi hxi_root using hinternal
  let gr : Fin (n + 2) → ℝ := Fin.cons xb (Fin.snoc xi xa)
  have hgr_root : ∀ j, g.IsRoot (gr j) := by
    intro j
    refine Fin.cases hxb_root (fun i ↦ ?_) j
    simp only [gr, Fin.cons_succ]
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simpa only [Fin.snoc_last] using hxa_root
    · simpa only [Fin.snoc_castSucc] using hxi_root k
  have hxi_mono : StrictMono xi := by
    intro a b hab
    have hs_le : s a.succ ≤ s b.castSucc := hs_mono.monotone (by simp_all)
    linarith [hxi_hi a, hxi_lo b]
  have hxi_xa : ∀ j : Fin n, xi j < xa := by
    intro j
    have hs_le : s j.succ ≤ s (Fin.last n) := hs_mono.monotone (by grind)
    linarith [hxi_hi j, hxa_gt]
  have hsnoc : StrictMono (Fin.snoc xi xa) := by
    rw [← Fin.insertNth_last' xa xi]
    apply (Fin.strictMono_insertNth_iff (Fin.last n) xa xi).mpr
    refine ⟨hxi_mono, fun i _ ↦ hxi_xa i, ?_⟩
    intro i hi
    exact (not_le_of_gt i.castSucc_lt_last hi).elim
  have hgr_mono : StrictMono gr := by
    apply Fin.strictMono_cons.mpr
    refine ⟨?_, hsnoc⟩
    intro j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · have hs_le : s 0 ≤ s (Fin.last n) := hs_mono.monotone (by simp)
      simpa only [Fin.snoc_last] using (hxb_lt.trans_le hs_le |>.trans hxa_gt)
    · have hs_le : s 0 ≤ s k.castSucc := hs_mono.monotone (by simp)
      simpa only [Fin.snoc_castSucc] using (hxb_lt.trans_le hs_le |>.trans (hxi_lo k))
  have hg_ne : g ≠ 0 := by
    intro hg
    rw [hg, natDegree_zero] at hg_deg
    lia
  have hsub : Finset.image gr Finset.univ ⊆ g.roots.toFinset := by
    rw [Finset.image_subset_iff]
    simp_all
  have hcard : n + 2 ≤ g.roots.toFinset.card := by
    calc
      n + 2 = (Finset.image gr Finset.univ).card := by
        rw [Finset.card_image_of_injective _ hgr_mono.injective, Finset.card_univ,
          Fintype.card_fin]
      _ ≤ g.roots.toFinset.card := Finset.card_le_card hsub
  apply Polynomial.splits_iff_card_roots.mpr
  refine le_antisymm (card_roots' g) ?_
  rw [hg_deg]
  exact hcard.trans (Multiset.toFinset_card_le _)

/-- A strict negative Wronskian transfers splitness from `f` to its
positive-leading one-degree-higher companion `g`. -/
theorem splits_of_wronskian_neg_succ {n : ℕ}
    {f g : ℝ[X]} (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg : f.natDegree = n + 1) (hg_deg : g.natDegree = n + 2)
    (hf_splits : f.Splits)
    (hW : ∀ t : ℝ, f.derivative.eval t * g.eval t - f.eval t * g.derivative.eval t < 0) :
    g.Splits := by
  have hf_ne : f ≠ 0 := leadingCoeff_ne_zero.mp hf_pos.ne'
  have hf_nodup : f.roots.Nodup := by
    apply Polynomial.roots_nodup_of_splits_and_simple
    intro r hr hd
    have hsign := hW r
    simp_all
  obtain ⟨s, hs_mono, hs_roots⟩ :
      ∃ s : Fin (n + 1) → ℝ, StrictMono s ∧ ∀ k, f.IsRoot (s k) :=
    Polynomial.exists_strictMono_roots hf_splits hf_deg hf_nodup
  have hgsign := wronskian_sign_at_roots_of_neg_succ
    (f := f) (g := g) hf_pos hf_deg hW s hs_mono hs_roots
  have hbelow : ∃ x, x < s 0 ∧ g.IsRoot x :=
    exists_root_lt_of_posLeadingCoeff_eval_mul_negOnePow_neg hg_pos hg_deg (s 0)
      (by simpa using hgsign 0)
  have hlast_sign : g.eval (s (Fin.last n)) < 0 := by
    have hsign := hgsign (Fin.last n)
    simp_all
  have habove : ∃ x, s (Fin.last n) < x ∧ g.IsRoot x :=
    exists_root_gt_of_posLeadingCoeff_eval_neg hg_pos hg_deg (s (Fin.last n)) hlast_sign
  have hinternal : ∀ k : Fin n,
      ∃ x, s k.castSucc < x ∧ x < s k.succ ∧ g.IsRoot x :=
    exists_root_between_of_alternating_signs s hs_mono hgsign
  exact splits_of_roots_around_strictMono hg_deg s hs_mono hbelow habove hinternal

end RealRooted
