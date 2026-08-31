import RealRooted.Wronskian.Successor.Signs

/-!
# Successor-degree Wronskian splitness transfer

A strict Wronskian sign transfers splitness from a positive-leading polynomial
to its one-degree-higher companion.
-/

open Polynomial

namespace RealRooted

/-- A strict negative Wronskian transfers splitness from `f` to its
positive-leading one-degree-higher companion `g`. -/
theorem splits_of_wronskian_neg_succ {n : ℕ}
    {f g : ℝ[X]} (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg : f.natDegree = n + 1) (hg_deg : g.natDegree = n + 2)
    (hf_splits : f.Splits)
    (hW : ∀ t : ℝ, f.derivative.eval t * g.eval t - f.eval t * g.derivative.eval t < 0) :
    g.Splits := by
  have hf_ne : f ≠ 0 := leadingCoeff_ne_zero.mp hf_pos.ne'
  have hg_ne : g ≠ 0 := leadingCoeff_ne_zero.mp hg_pos.ne'
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
      ∃ x, s k.castSucc < x ∧ x < s k.succ ∧ g.IsRoot x := by
    intro k
    have hlt : s k.castSucc < s k.succ := hs_mono (by simp)
    have hsc := hgsign k.castSucc
    have hss := hgsign k.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at hsc hss
    rcases Nat.even_or_odd (n - k.val) with hpar | hpar
    · have hkk : (n - k.val) = (n - (k.val + 1)) + 1 := by grind
      rw [hpar.neg_one_pow] at hsc
      have hpar' : Odd (n - (k.val + 1)) := by grind
      rw [hpar'.neg_one_pow] at hss
      obtain ⟨x, hx1, hx2, hx3⟩ :=
        exists_root_between_of_eval_neg_pos _ _ hlt (by linarith) (by nlinarith)
      grind
    · have hkk : (n - k.val) = (n - (k.val + 1)) + 1 := by grind
      rw [hpar.neg_one_pow] at hsc
      have hpar' : Even (n - (k.val + 1)) := by grind
      rw [hpar'.neg_one_pow] at hss
      obtain ⟨x, hx1, hx2, hx3⟩ :=
        exists_root_between_of_eval_pos_neg _ _ hlt (by nlinarith) (by linarith)
      grind
  obtain ⟨xb, hxb_lt, hxb_root⟩ := hbelow
  obtain ⟨xa, hxa_gt, hxa_root⟩ := habove
  choose xi hxi_lo hxi_hi hxi_root using hinternal
  set gr : Fin (n + 2) → ℝ := Fin.cons xb (Fin.snoc xi xa) with hgr_def
  have hgr_root : ∀ j, g.IsRoot (gr j) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simp_all
    · intro i
      simp only [hgr_def, Fin.cons_succ]
      refine Fin.lastCases ?_ ?_ i
      · simpa using hxa_root
      · simp_all
  have hxi_mono : StrictMono xi := by
    intro a b hab
    have h1 : xi a < s a.succ := hxi_hi a
    have h2 : s b.castSucc < xi b := hxi_lo b
    have h3 : s a.succ ≤ s b.castSucc := hs_mono.monotone (by simp_all)
    linarith
  have hxb_xi : ∀ j : Fin n, xb < xi j := by
    intro j
    have h1 := hxi_lo j
    have h2 : s 0 ≤ s j.castSucc := hs_mono.monotone (by simp)
    grind
  have hxi_xa : ∀ j : Fin n, xi j < xa := by
    intro j
    have h1 := hxi_hi j
    have h2 : s j.succ ≤ s (Fin.last n) := hs_mono.monotone (by grind)
    grind
  have hxb_xa : xb < xa := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · grind
    · exact lt_trans (hxb_xi ⟨0, hn⟩) (hxi_xa ⟨0, hn⟩)
  have hgr_mono : StrictMono gr := by
    have hgr_val : ∀ j : Fin (n + 2), gr j =
        if hj : j.val = 0 then xb
        else if hj' : j.val = n + 1 then xa
        else xi ⟨j.val - 1, by lia⟩ := by
      intro j
      simp only [hgr_def]
      refine Fin.cases ?_ ?_ j
      · simp
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last, Fin.val_last]
        · intro k
          rw [Fin.cons_succ, Fin.snoc_castSucc]
          have hval : (k.castSucc.succ : Fin (n + 2)).val = k.val + 1 := rfl
          rw [dif_neg (by simp), dif_neg (by grind)]
          simp
    intro a b hab
    rw [hgr_val a, hgr_val b]
    have hlt : a.val < b.val := hab
    split_ifs with ha0 hbn1 hb0 hbn1' ha1 hbn2 ha2
    all_goals first
      | exact hxb_xa
      | exact hxb_xi _
      | rfl
      | lia
      | exact hxi_xa _
      | apply hxi_mono
        rw [Fin.lt_def]
        simp
        lia
  have hinj : Function.Injective gr := hgr_mono.injective
  have hsub : Finset.image gr Finset.univ ⊆ g.roots.toFinset := by
    rw [Finset.image_subset_iff]
    simp_all
  have hcard : n + 2 ≤ g.roots.toFinset.card := by
    calc n + 2 = (Finset.image gr Finset.univ).card := by
              rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      _ ≤ g.roots.toFinset.card := Finset.card_le_card hsub
  have hcard_roots : g.roots.card = g.natDegree := by
    refine le_antisymm (card_roots' g) ?_
    rw [hg_deg]
    exact le_trans hcard (Multiset.toFinset_card_le _)
  exact splits_of_card_roots hcard_roots

end RealRooted
