module

import RealRooted.Wronskian.Successor.Gap
import RealRooted.Bezoutian.WronskianConverse
import RealRooted.Bezoutian.RootEvaluation
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Successor-degree Wronskian interlacing

Strict Wronskian signs at the roots of the higher-degree polynomial force
strict interlacing across a one-degree increase.
-/

public section

open Polynomial

namespace RealRooted

/-- Fin-indexed successor-degree root gaps give the legacy list-interlacing
shape. -/
lemma listInterlaces_ofFn_succ :
    ∀ {n : ℕ} (s : Fin n → ℝ) (r : Fin (n + 1) → ℝ),
    StrictMono r →
    (∀ k : Fin n, r k.castSucc < s k ∧ s k < r k.succ) →
    ListInterlaces (List.ofFn s) (List.ofFn r)
  | 0, s, r, _, _ => by
      rw [show List.ofFn s = [] from by simp,
          show List.ofFn r = [r 0] from by simp]
      trivial
  | (n + 1), s, r, hr, hgap => by
      have ih := listInterlaces_ofFn_succ (fun i : Fin n => s i.succ)
        (fun i : Fin (n + 1) => r i.succ) (fun a b h => hr (by grind))
        (fun k => by grind)
      rw [List.ofFn_succ]
      rw [show (List.ofFn r) = r 0 :: r (Fin.succ 0) ::
            List.ofFn (fun i : Fin n => r i.succ.succ) by simp]
      refine ⟨?_, ?_, ?_⟩
      · have hzero := (hgap 0).1
        simpa using hzero.le
      · grind
      · simp_all

/-- A strictly increasing full-degree family of roots forces the root multiset to be nodup. -/
private lemma roots_nodup_of_strictMono_isRoot {n : ℕ} {p : ℝ[X]}
    (hp_ne : p ≠ 0) (hp_deg : p.natDegree = n) (x : Fin n → ℝ)
    (hx_mono : StrictMono x) (hx_root : ∀ k, p.IsRoot (x k)) : p.roots.Nodup := by
  have hx_sub : Finset.image x Finset.univ ⊆ p.roots.toFinset := by
    rw [Finset.image_subset_iff]
    intro k _
    exact Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hp_ne, hx_root k⟩)
  have hx_card : n ≤ p.roots.toFinset.card := by
    calc n = (Finset.image x Finset.univ).card := by
            rw [Finset.card_image_of_injective _ hx_mono.injective, Finset.card_univ,
              Fintype.card_fin]
      _ ≤ p.roots.toFinset.card := Finset.card_le_card hx_sub
  have hp_roots_card : p.roots.card = n := by
    refine le_antisymm ?_ ?_
    · rw [← hp_deg]
      exact card_roots' p
    · exact le_trans hx_card (Multiset.toFinset_card_le _)
  have h_toFinset_n : p.roots.toFinset.card = n :=
    le_antisymm (le_trans (Multiset.toFinset_card_le _) hp_roots_card.le) hx_card
  have h_dedup_card : Multiset.card p.roots.dedup = Multiset.card p.roots := by
    rw [← Multiset.toFinset_val]
    simp only [Finset.card] at h_toFinset_n
    lia
  have h_dedup_eq : p.roots.dedup = p.roots :=
    Multiset.eq_of_le_of_card_le (Multiset.dedup_le _) (le_of_eq h_dedup_card.symm)
  rw [← h_dedup_eq]
  simp

/-- A strict Wronskian sign at every root of the higher-degree polynomial
forces strict interlacing across a one-degree increase. -/
theorem interlaces_of_wronskian_neg_succ_atRoots {n : ℕ}
    {f g : ℝ[X]} (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg : f.natDegree = n) (hg_deg : g.natDegree = n + 1)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hW_roots : ∀ r : ℝ, g.IsRoot r →
      f.derivative.eval r * g.eval r - f.eval r * g.derivative.eval r < 0) :
    Interlaces f g := by
  have hf_ne : f ≠ 0 := leadingCoeff_ne_zero.mp hf_pos.ne'
  have hg_ne : g ≠ 0 := leadingCoeff_ne_zero.mp hg_pos.ne'
  have hW_roots' : ∀ r : ℝ, g.IsRoot r →
      0 < g.derivative.eval r * f.eval r - g.eval r * f.derivative.eval r := by
    grind
  have hg_nodup : g.roots.Nodup := by
    apply Polynomial.roots_nodup_of_splits_and_simple
    intro r hr hd
    have hsign := hW_roots' r hr
    simp_all
  obtain ⟨r, hr_mono, hr_roots⟩ :
      ∃ r : Fin (n + 1) → ℝ, StrictMono r ∧ ∀ k, g.IsRoot (r k) :=
    Polynomial.exists_strictMono_roots hg_splits hg_deg hg_nodup
  have h_gap := has_gap_root_of_wronskian_pos_succ_atRoots (p := f) hg_pos hg_deg
    r hr_mono hr_roots (fun k => by simp_all)
  choose x hx_root hx_lo hx_hi using h_gap
  have hx_mono : StrictMono x := by
    intro a b hab
    calc x a < r a.succ := hx_hi a
      _ ≤ r b.castSucc := hr_mono.monotone (by simp_all)
      _ < x b := hx_lo b
  have hf_nodup := roots_nodup_of_strictMono_isRoot hf_ne hf_deg x hx_mono hx_root
  obtain ⟨s, hs_mono, hs_roots⟩ :
      ∃ s : Fin n → ℝ, StrictMono s ∧ ∀ k, f.IsRoot (s k) :=
    Polynomial.exists_strictMono_roots hf_splits hf_deg hf_nodup
  have hs_surj : ∀ y ∈ f.roots, ∃ k, s k = y :=
    exists_index_eq_of_mem_roots s hs_mono hs_roots hf_ne hf_deg.le
  have hxs_eq : ∀ k, x k = s k := by
    obtain ⟨σ, hσ⟩ : ∃ σ : Fin n → Fin n, ∀ k, s (σ k) = x k := by
      refine ⟨fun k => Classical.choose (hs_surj (x k)
        (mem_roots'.mpr ⟨hf_ne, hx_root k⟩)), ?_⟩
      exact fun k => Classical.choose_spec (hs_surj (x k)
        (mem_roots'.mpr ⟨hf_ne, hx_root k⟩))
    have hσ_mono : StrictMono σ := by
      intro a b hab
      have hlt : s (σ a) < s (σ b) := by
        rw [hσ a, hσ b]
        exact hx_mono hab
      exact hs_mono.lt_iff_lt.mp hlt
    have hσ_id : ∀ k, σ k = k := fun k =>
      le_antisymm (StrictMono.apply_le hσ_mono) (StrictMono.le_apply hσ_mono)
    simp_all
  have h_gap_s : ∀ k : Fin n, r k.castSucc < s k ∧ s k < r k.succ := by
    simp_all
  refine ⟨⟨hg_ne, hg_splits⟩, ⟨hf_ne, hf_splits⟩, by simp_all, ?_⟩
  refine ⟨List.ofFn r, List.ofFn s, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_ofFn]
    exact fun i j hij => hr_mono.monotone hij.le
  · rw [List.pairwise_ofFn]
    exact fun i j hij => hs_mono.monotone hij.le
  · rw [List.ofFn_eq_map,
      ← Polynomial.roots_sort_eq_of_isRoot hg_ne hg_deg r hr_roots hr_mono]
    simp
  · rw [List.ofFn_eq_map,
      ← Polynomial.roots_sort_eq_of_isRoot hf_ne hf_deg s hs_roots hs_mono]
    simp
  · exact listInterlaces_ofFn_succ s r hr_mono h_gap_s

/-- A global strict Wronskian sign implies the root-local hypothesis of
`interlaces_of_wronskian_neg_succ_atRoots`. -/
theorem interlaces_of_wronskian_neg_succ {n : ℕ}
    {f g : ℝ[X]} (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg : f.natDegree = n) (hg_deg : g.natDegree = n + 1)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hW : ∀ t : ℝ, f.derivative.eval t * g.eval t - f.eval t * g.derivative.eval t < 0) :
    Interlaces f g :=
  interlaces_of_wronskian_neg_succ_atRoots hf_pos hg_pos hf_deg hg_deg hf_splits hg_splits
    fun r _ ↦ hW r

end RealRooted
