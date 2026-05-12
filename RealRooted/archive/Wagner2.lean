/-
# Wagner's lemma, form (2)

If `Prec h f` and `Prec h g` with positive leading coefficients
and `IsCoprime f g`, then `Prec h (f+g)`.

This handles all four cases: both differ-by-1, mixed (f differ-by-1 /
g same-degree and vice versa), and both same-degree.
-/
import RealRooted.Basic
import RealRooted.Interlacing
import RealRooted.SignLemmas
import RealRooted.Wagner1
import RealRooted.Wagner2Helper

open Polynomial

noncomputable section

namespace RealRooted

/-- Wagner (2): If h precedes both f and g with positive leading coefficients,
    and f, g are coprime, then h precedes their sum. -/
theorem prec_add_of_prec_left {f g h : ℝ[X]}
    (hhf : Prec h f) (hhg : Prec h g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg_rr : IsRealRooted (f + g))
    (hcop : IsCoprime f g) :
    Prec h (f + g) := by
  -- For now, handle the both differ-by-1 case
  obtain ⟨hh, hf, ss_h, rs_f, hss_h_sorted, hrs_f_sorted, hss_h_eq, hrs_f_eq, hcase_f⟩ := hhf
  obtain ⟨_, hg, ss_h2, rs_g, hss_h2_sorted, hrs_g_sorted, hss_h2_eq, hrs_g_eq, hcase_g⟩ := hhg
  -- Unify the h-root lists
  have hss_eq : ss_h = ss_h2 := by
    apply List.Perm.eq_of_pairwise' hss_h_sorted hss_h2_sorted
    exact Multiset.coe_eq_coe.mp (hss_h_eq.trans hss_h2_eq.symm)
  subst hss_eq
  rcases hcase_f with ⟨hlen_f, hint_f⟩ | ⟨hlen_f_alt, halt_f⟩
  · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · -- Both differ-by-1: use wagner2_roots_exist
      obtain ⟨rf, rest_f, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with | nil => simp at hlen_f | cons r rs => exact ⟨r, rs, rfl⟩
      obtain ⟨rg, rest_g, rfl⟩ : ∃ a l, rs_g = a :: l := by
        cases rs_g with | nil => simp at hlen_g | cons r rs => exact ⟨r, rs, rfl⟩
      have hlen_f' : rest_f.length = ss_h.length := by
        simp only [List.length_cons] at hlen_f; omega
      have hlen_g' : rest_g.length = ss_h.length := by
        simp only [List.length_cons] at hlen_g; omega
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, _⟩ :=
        wagner2_roots_exist f g hf hg hf_pos hg_pos hcop 0 0
          rf rg rest_f rest_g ss_h hlen_f' hlen_g'
          hint_f hint_g (by simp [hrs_f_eq]) (by simp [hrs_g_eq])
          (by simp) (by simp) (by simp) (by simp)
      -- us exhausts roots of f+g
      have hus_nodup : us.Nodup := hus_pw.imp ne_of_lt
      have hus_sub : (↑us : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
        intro u hu
        exact (mem_roots hfg_rr.1).mpr (hus_root u (Multiset.mem_coe.mp hu))
      have hfg_deg : (f + g).natDegree = f.natDegree := by
        have hf_deg : (rf :: rest_f).length = f.natDegree := by
          have := hf.2; rw [← hrs_f_eq, Multiset.coe_card] at this; exact this
        have hg_deg : (rg :: rest_g).length = g.natDegree := by
          have := hg.2; rw [← hrs_g_eq, Multiset.coe_card] at this; exact this
        have hdeg_eq : f.natDegree = g.natDegree := by
          simp [List.length_cons] at hf_deg hg_deg hlen_f hlen_g; omega
        apply le_antisymm
        · have h := natDegree_add_le f g; rwa [max_eq_left hdeg_eq.symm.le] at h
        · apply le_natDegree_of_ne_zero; rw [coeff_add]
          have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
          have hgc : g.coeff f.natDegree = g.leadingCoeff := by
            unfold leadingCoeff; rw [← hdeg_eq]
          rw [hfc, hgc]
          exact ne_of_gt (by unfold HasPosLeadingCoeff at hf_pos hg_pos; linarith)
      have hfg_natDeg : (f + g).natDegree = us.length := by
        rw [hus_len, hfg_deg]
        have := hf.2; rw [← hrs_f_eq, Multiset.coe_card] at this
        simp [List.length_cons] at this ⊢; omega
      have hus_eq : (↑us : Multiset ℝ) = (f + g).roots :=
        Multiset.eq_of_le_of_card_le hus_sub (by
          rw [Multiset.coe_card, hfg_rr.2]; omega)
      exact ⟨hh, hfg_rr, ss_h, us,
        hss_h_sorted, hus_pw.imp le_of_lt, hss_h_eq, hus_eq,
        Or.inl ⟨by omega, hus_int⟩⟩
    · -- f differ-by-1, g same-degree
      cases rs_g with
      | nil =>
        -- g degree 0, h degree 0, f degree 1
        simp only [List.length_nil] at hlen_g_alt
        have hss_nil : ss_h.length = 0 := by omega
        have hrs_nil : ss_h = [] := by cases ss_h <;> simp_all
        subst hrs_nil
        simp only [List.length_nil] at hlen_f
        obtain ⟨rf, rfl⟩ : ∃ a, rs_f = [a] := by
          cases rs_f with
          | nil => simp_all
          | cons a t =>
            simp only [List.length_cons] at hlen_f
            have : t = [] := by cases t <;> simp_all
            subst this; exact ⟨a, rfl⟩
        -- f+g has exactly 1 root
        have hfnd : f.natDegree = 1 := by
          have := hf.2; rw [← hrs_f_eq, Multiset.coe_card] at this; omega
        have hgnd : g.natDegree = 0 := by
          have := hg.2; rw [← hrs_g_eq, Multiset.coe_card] at this; omega
        have hfgnd : (f + g).natDegree = 1 := by
          apply le_antisymm
          · have := natDegree_add_le f g; rw [hfnd, hgnd] at this; simpa using this
          · rw [← hfnd]; apply le_natDegree_of_ne_zero; rw [coeff_add]
            have : g.coeff f.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
            rw [this, add_zero]; exact ne_of_gt hf_pos
        have hcard1 : (f + g).roots.card = 1 := by rw [hfg_rr.2, hfgnd]
        obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < (f+g).roots.card)
        have hfg_eq : (↑[u] : Multiset ℝ) = (f + g).roots := by
          apply Multiset.eq_of_le_of_card_le
          · rw [Multiset.le_iff_subset (by simp)]
            intro w hw; simp at hw; rwa [hw]
          · simp [hcard1]
        exact ⟨hh, hfg_rr, [], [u], List.Pairwise.nil, List.pairwise_singleton _ _,
          hss_h_eq, hfg_eq, Or.inl ⟨by simp, trivial⟩⟩
      | cons r₁_g rest_g =>
        obtain ⟨s₁, rest_ss, rfl⟩ : ∃ a l, ss_h = a :: l := by
          cases ss_h with
          | nil => simp only [List.length_nil, List.length_cons] at hlen_g_alt; omega
          | cons s rest => exact ⟨s, rest, rfl⟩
        obtain ⟨rf, rf2, rest_f', rfl⟩ : ∃ a b l, rs_f = a :: b :: l := by
          rcases rs_f with _ | ⟨a, _ | ⟨b, l⟩⟩
          · simp only [List.length_nil, List.length_cons] at hlen_f; omega
          · simp only [List.length_nil, List.length_cons] at hlen_f; omega
          · exact ⟨a, b, l, rfl⟩
        obtain ⟨hs₁_r₁g, hint_g_tail⟩ := halt_g
        obtain ⟨hrfs₁, hs₁rf2, hint_f_tail⟩ := hint_f
        have hrf_root : f.IsRoot rf :=
          (mem_roots hf.1).mp (by rw [← hrs_f_eq]; simp)
        have hr₁g_root : g.IsRoot r₁_g :=
          (mem_roots hg.1).mp (by rw [← hrs_g_eq]; simp)
        -- Degrees
        have hf_deg : (rf :: rf2 :: rest_f').length = f.natDegree := by
          have := hf.2; rw [← hrs_f_eq, Multiset.coe_card] at this; exact this
        have hg_deg : (r₁_g :: rest_g).length = g.natDegree := by
          have := hg.2; rw [← hrs_g_eq, Multiset.coe_card] at this; exact this
        have hdeg : g.natDegree + 1 = f.natDegree := by
          simp [List.length_cons] at hf_deg hg_deg hlen_f hlen_g_alt; omega
        have hdeg_lt : g.natDegree < f.natDegree := by omega
        have hfg_deg : (f + g).natDegree = f.natDegree := by
          apply le_antisymm
          · have h := natDegree_add_le f g; rwa [max_eq_left hdeg_lt.le] at h
          · apply le_natDegree_of_ne_zero; rw [coeff_add,
              coeff_eq_zero_of_natDegree_lt hdeg_lt, add_zero]
            exact ne_of_gt hf_pos
        have hfg_pos : HasPosLeadingCoeff (f + g) := by
          show 0 < (f + g).leadingCoeff
          simp only [leadingCoeff, hfg_deg, coeff_add,
            coeff_eq_zero_of_natDegree_lt hdeg_lt, add_zero]; exact hf_pos
        -- All g-roots > rf (coprimality)
        have hg_gt_rf : ∀ t ∈ g.roots, rf < t := by
          intro t ht; rw [← hrs_g_eq] at ht
          have ht_ge : s₁ ≤ t := by
            rcases Multiset.mem_coe.mp ht with ht'
            rcases List.mem_cons.mp ht' with rfl | ht''
            · exact hs₁_r₁g
            · exact le_trans hs₁_r₁g
                (listInterlaces_rs_all_ge rest_ss rest_g r₁_g hint_g_tail t ht'')
          rcases lt_or_eq_of_le (le_trans hrfs₁ ht_ge) with h | h
          · exact h
          · exfalso
            have hft : Polynomial.eval t f = 0 :=
              (mem_roots hf.1).mp (hrs_f_eq ▸ Multiset.mem_coe.mpr (by rw [h]; exact List.mem_cons_self ..))
            have hgt : Polynomial.eval t g = 0 := (mem_roots hg.1).mp (hrs_g_eq ▸ ht)
            obtain ⟨p, q, hpq⟩ := hcop
            have := congr_arg (Polynomial.eval t) hpq
            simp [eval_add, eval_mul, eval_one, hft, hgt] at this
        have hcard : g.roots.card + 1 = (g + f).roots.card := by
          rw [hg.2, show g + f = f + g from add_comm g f, hfg_rr.2, hfg_deg, hdeg]
        obtain ⟨u₀, hu₀_le, hu₀_root_gf⟩ :=
          exists_root_le_of_mixed hg (by rwa [add_comm] : IsRealRooted (g + f))
            hg_pos (by rw [show g + f = f + g from add_comm g f]; exact hfg_pos)
            hcop.symm hrf_root hg_gt_rf hcard
        have hu₀_root : (f + g).IsRoot u₀ := by rwa [add_comm] at hu₀_root_gf
        -- Use wagner2_roots_exist on rf2 :: rest_f' and r₁_g :: rest_g with rest_ss
        have hlen_f' : rest_f'.length = rest_ss.length := by
          simp only [List.length_cons] at hlen_f; omega
        have hlen_g' : rest_g.length = rest_ss.length := by
          simp only [List.length_cons] at hlen_g_alt; omega
        have hrs_f_eq' : (↑(rf2 :: rest_f') : Multiset ℝ) + ↑[rf] = f.roots := by
          rw [← hrs_f_eq, Multiset.coe_add]
          exact Multiset.coe_eq_coe.mpr List.perm_append_comm
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
          wagner2_roots_exist f g hf hg hf_pos hg_pos hcop ↑[rf] 0
            rf2 r₁_g rest_f' rest_g rest_ss hlen_f' hlen_g'
            hint_f_tail hint_g_tail hrs_f_eq' (by simp [hrs_g_eq])
            (by intro r hr; simp at hr; subst hr; exact le_trans hrfs₁ hs₁rf2)
            (by simp)
            (by intro r hr; simp at hr; subst hr; exact le_trans hrfs₁ hs₁_r₁g)
            (by simp)
        -- u₀ < s₁ (coprimality)
        have hu₀_lt_s₁ : u₀ < s₁ := by
          rcases lt_or_eq_of_le (le_trans hu₀_le hrfs₁) with h | h
          · exact h
          · exfalso
            have hrf_s₁ : rf = s₁ := le_antisymm hrfs₁ (h ▸ hu₀_le)
            have hfs₁ : Polynomial.eval s₁ f = 0 := by rw [← hrf_s₁]; exact hrf_root
            have hgs₁ : Polynomial.eval s₁ g = 0 := by
              have := h ▸ hu₀_root
              rw [Polynomial.IsRoot.def, Polynomial.eval_add, hfs₁, zero_add] at this; exact this
            obtain ⟨p, q, hpq⟩ := hcop
            have := congr_arg (Polynomial.eval s₁) hpq
            simp [eval_add, eval_mul, eval_one, hfs₁, hgs₁] at this
        -- us elements ≥ min(rf2, r₁_g) ≥ s₁
        have hus_ge_s₁ : ∀ w ∈ us, s₁ ≤ w := by
          intro w hw; exact le_trans (le_min hs₁rf2 hs₁_r₁g) (hus_lb w hw)
        obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
          cases us with | nil => simp at hus_len | cons a l => exact ⟨a, l, rfl⟩
        -- Build interlacing: u₀ ≤ s₁ ≤ u1, then ListInterlaces rest_ss (u1 :: us_tail)
        have hnodup := ((List.pairwise_cons.mpr ⟨fun w hw =>
          lt_of_lt_of_le hu₀_lt_s₁ (hus_ge_s₁ w hw), hus_pw⟩).imp ne_of_lt :
          (u₀ :: u1 :: us_tail).Nodup)
        have hsub : (↑(u₀ :: u1 :: us_tail) : Multiset ℝ) ≤ (f + g).roots := by
          rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
          intro u hu
          exact (mem_roots hfg_rr.1).mpr
            ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root)
              (hus_root u))
        have hroots_eq : (↑(u₀ :: u1 :: us_tail) : Multiset ℝ) = (f + g).roots :=
          Multiset.eq_of_le_of_card_le hsub (by
            rw [Multiset.coe_card]; simp only [List.length_cons]
            have h1 := hfg_rr.2; rw [hfg_deg] at h1
            simp [List.length_cons] at hf_deg hus_len; omega)
        exact ⟨hh, hfg_rr, s₁ :: rest_ss, u₀ :: u1 :: us_tail,
          hss_h_sorted, (List.pairwise_cons.mpr ⟨fun w hw =>
            lt_of_lt_of_le hu₀_lt_s₁ (hus_ge_s₁ w hw), hus_pw⟩).imp le_of_lt,
          hss_h_eq, hroots_eq,
          Or.inl ⟨by simp only [List.length_cons] at hlen_f hus_len ⊢; omega,
                   ⟨le_trans hu₀_le hrfs₁, hus_ge_s₁ u1 (List.mem_cons_self ..), hus_int⟩⟩⟩
  · -- f same-degree
    rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · -- f same-degree, g differ-by-1 (symmetric to f differ-by-1, g same-degree above)
      cases rs_f with
      | nil =>
        -- f degree 0, h degree 0, g degree 1
        simp only [List.length_nil] at hlen_f_alt
        have hss_nil : ss_h.length = 0 := by omega
        have hrs_nil : ss_h = [] := by cases ss_h <;> simp_all
        subst hrs_nil
        simp only [List.length_nil] at hlen_g
        obtain ⟨rg, rfl⟩ : ∃ a, rs_g = [a] := by
          cases rs_g with
          | nil => simp_all
          | cons a t =>
            simp only [List.length_cons] at hlen_g
            have : t = [] := by cases t <;> simp_all
            subst this; exact ⟨a, rfl⟩
        have hfnd : f.natDegree = 0 := by
          have := hf.2; rw [← hrs_f_eq, Multiset.coe_card] at this; omega
        have hgnd : g.natDegree = 1 := by
          have := hg.2; rw [← hrs_g_eq, Multiset.coe_card] at this; omega
        have hfgnd : (f + g).natDegree = 1 := by
          apply le_antisymm
          · have := natDegree_add_le f g; rw [hfnd, hgnd] at this; simpa using this
          · rw [← hgnd]; apply le_natDegree_of_ne_zero; rw [coeff_add]
            have : f.coeff g.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
            rw [this, zero_add]; exact ne_of_gt hg_pos
        have hcard1 : (f + g).roots.card = 1 := by rw [hfg_rr.2, hfgnd]
        obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < (f+g).roots.card)
        have hfg_eq : (↑[u] : Multiset ℝ) = (f + g).roots := by
          apply Multiset.eq_of_le_of_card_le
          · rw [Multiset.le_iff_subset (by simp)]
            intro w hw; simp at hw; rwa [hw]
          · simp [hcard1]
        exact ⟨hh, hfg_rr, [], [u], List.Pairwise.nil, List.pairwise_singleton _ _,
          hss_h_eq, hfg_eq, Or.inl ⟨by simp, trivial⟩⟩
      | cons r₁_f rest_f =>
        -- Main case: f same-degree, g differ-by-1
        obtain ⟨s₁, rest_ss, rfl⟩ : ∃ a l, ss_h = a :: l := by
          cases ss_h with
          | nil => simp only [List.length_nil, List.length_cons] at hlen_f_alt; omega
          | cons s rest => exact ⟨s, rest, rfl⟩
        obtain ⟨rg, rg2, rest_g', rfl⟩ : ∃ a b l, rs_g = a :: b :: l := by
          rcases rs_g with _ | ⟨a, _ | ⟨b, l⟩⟩
          · simp only [List.length_nil, List.length_cons] at hlen_g; omega
          · simp only [List.length_nil, List.length_cons] at hlen_g; omega
          · exact ⟨a, b, l, rfl⟩
        obtain ⟨hs₁_r₁f, hint_f_tail⟩ := halt_f
        obtain ⟨hrgs₁, hs₁rg2, hint_g_tail⟩ := hint_g
        have hr₁f_root : f.IsRoot r₁_f :=
          (mem_roots hf.1).mp (by rw [← hrs_f_eq]; simp)
        have hrg_root : g.IsRoot rg :=
          (mem_roots hg.1).mp (by rw [← hrs_g_eq]; simp)
        -- Degrees
        have hf_deg : (r₁_f :: rest_f).length = f.natDegree := by
          have := hf.2; rw [← hrs_f_eq, Multiset.coe_card] at this; exact this
        have hg_deg : (rg :: rg2 :: rest_g').length = g.natDegree := by
          have := hg.2; rw [← hrs_g_eq, Multiset.coe_card] at this; exact this
        have hdeg : f.natDegree + 1 = g.natDegree := by
          simp [List.length_cons] at hf_deg hg_deg hlen_f_alt hlen_g; omega
        have hdeg_lt : f.natDegree < g.natDegree := by omega
        have hfg_deg : (f + g).natDegree = g.natDegree := by
          apply le_antisymm
          · have h := natDegree_add_le f g; rwa [max_eq_right hdeg_lt.le] at h
          · apply le_natDegree_of_ne_zero; rw [coeff_add,
              coeff_eq_zero_of_natDegree_lt hdeg_lt, zero_add]
            exact ne_of_gt hg_pos
        have hfg_pos : HasPosLeadingCoeff (f + g) := by
          show 0 < (f + g).leadingCoeff
          simp only [leadingCoeff, hfg_deg, coeff_add,
            coeff_eq_zero_of_natDegree_lt hdeg_lt, zero_add]; exact hg_pos
        -- All f-roots > rg (coprimality)
        have hf_gt_rg : ∀ t ∈ f.roots, rg < t := by
          intro t ht; rw [← hrs_f_eq] at ht
          have ht_ge : s₁ ≤ t := by
            rcases Multiset.mem_coe.mp ht with ht'
            rcases List.mem_cons.mp ht' with rfl | ht''
            · exact hs₁_r₁f
            · exact le_trans hs₁_r₁f
                (listInterlaces_rs_all_ge rest_ss rest_f r₁_f hint_f_tail t ht'')
          rcases lt_or_eq_of_le (le_trans hrgs₁ ht_ge) with h | h
          · exact h
          · exfalso
            have hgt : Polynomial.eval t g = 0 :=
              (mem_roots hg.1).mp (hrs_g_eq ▸ Multiset.mem_coe.mpr
                (by rw [h]; exact List.mem_cons_self ..))
            have hft : Polynomial.eval t f = 0 :=
              (mem_roots hf.1).mp (hrs_f_eq ▸ ht)
            obtain ⟨p, q, hpq⟩ := hcop
            have := congr_arg (Polynomial.eval t) hpq
            simp [eval_add, eval_mul, eval_one, hft, hgt] at this
        have hcard : f.roots.card + 1 = (f + g).roots.card := by
          rw [hf.2, hfg_rr.2, hfg_deg, hdeg]
        obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
          exists_root_le_of_mixed hf hfg_rr hf_pos hfg_pos hcop hrg_root hf_gt_rg hcard
        -- Use wagner2_roots_exist on r₁_f :: rest_f and rg2 :: rest_g' with rest_ss
        have hlen_f' : rest_f.length = rest_ss.length := by
          simp only [List.length_cons] at hlen_f_alt; omega
        have hlen_g' : rest_g'.length = rest_ss.length := by
          simp only [List.length_cons] at hlen_g; omega
        have hrs_g_eq' : (↑(rg2 :: rest_g') : Multiset ℝ) + ↑[rg] = g.roots := by
          rw [← hrs_g_eq, Multiset.coe_add]
          exact Multiset.coe_eq_coe.mpr List.perm_append_comm
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
          wagner2_roots_exist f g hf hg hf_pos hg_pos hcop 0 ↑[rg]
            r₁_f rg2 rest_f rest_g' rest_ss hlen_f' hlen_g'
            hint_f_tail hint_g_tail (by simp [hrs_f_eq]) hrs_g_eq'
            (by simp)
            (by intro r hr; simp at hr; subst hr; exact le_trans hrgs₁ hs₁rg2)
            (by simp)
            (by intro r hr; simp at hr; subst hr; exact le_trans hrgs₁ hs₁_r₁f)
        -- u₀ < s₁ (coprimality)
        have hu₀_lt_s₁ : u₀ < s₁ := by
          rcases lt_or_eq_of_le (le_trans hu₀_le hrgs₁) with h | h
          · exact h
          · exfalso
            have hrg_s₁ : rg = s₁ := le_antisymm hrgs₁ (h ▸ hu₀_le)
            have hgs₁ : Polynomial.eval s₁ g = 0 := by rw [← hrg_s₁]; exact hrg_root
            have hfs₁ : Polynomial.eval s₁ f = 0 := by
              have := h ▸ hu₀_root
              rw [Polynomial.IsRoot.def, Polynomial.eval_add, hgs₁, add_zero] at this
              exact this
            obtain ⟨p, q, hpq⟩ := hcop
            have := congr_arg (Polynomial.eval s₁) hpq
            simp [eval_add, eval_mul, eval_one, hfs₁, hgs₁] at this
        -- us elements ≥ min(r₁_f, rg2) ≥ s₁
        have hus_ge_s₁ : ∀ w ∈ us, s₁ ≤ w := by
          intro w hw; exact le_trans (le_min hs₁_r₁f hs₁rg2) (hus_lb w hw)
        obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
          cases us with | nil => simp at hus_len | cons a l => exact ⟨a, l, rfl⟩
        -- Build interlacing
        have hnodup := ((List.pairwise_cons.mpr ⟨fun w hw =>
          lt_of_lt_of_le hu₀_lt_s₁ (hus_ge_s₁ w hw), hus_pw⟩).imp ne_of_lt :
          (u₀ :: u1 :: us_tail).Nodup)
        have hsub : (↑(u₀ :: u1 :: us_tail) : Multiset ℝ) ≤ (f + g).roots := by
          rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
          intro u hu
          exact (mem_roots hfg_rr.1).mpr
            ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root)
              (hus_root u))
        have hroots_eq : (↑(u₀ :: u1 :: us_tail) : Multiset ℝ) = (f + g).roots :=
          Multiset.eq_of_le_of_card_le hsub (by
            rw [Multiset.coe_card]; simp only [List.length_cons]
            have h1 := hfg_rr.2; rw [hfg_deg] at h1
            simp [List.length_cons] at hg_deg hus_len; omega)
        exact ⟨hh, hfg_rr, s₁ :: rest_ss, u₀ :: u1 :: us_tail,
          hss_h_sorted, (List.pairwise_cons.mpr ⟨fun w hw =>
            lt_of_lt_of_le hu₀_lt_s₁ (hus_ge_s₁ w hw), hus_pw⟩).imp le_of_lt,
          hss_h_eq, hroots_eq,
          Or.inl ⟨by simp only [List.length_cons] at hlen_g hus_len ⊢; omega,
                   ⟨le_trans hu₀_le hrgs₁, hus_ge_s₁ u1 (List.mem_cons_self ..), hus_int⟩⟩⟩
    · -- f same-degree, g same-degree
      cases ss_h with
      | nil =>
        -- Degenerate: all degree 0
        simp only [List.length_nil] at hlen_f_alt hlen_g_alt
        have hrf_nil : rs_f = [] := by
          cases rs_f with | nil => rfl | cons _ _ => simp at hlen_f_alt
        have hrg_nil : rs_g = [] := by
          cases rs_g with | nil => rfl | cons _ _ => simp at hlen_g_alt
        subst hrf_nil; subst hrg_nil
        have hfnd : f.natDegree = 0 := by
          have := hf.2; rw [← hrs_f_eq, Multiset.coe_card] at this; omega
        have hgnd : g.natDegree = 0 := by
          have := hg.2; rw [← hrs_g_eq, Multiset.coe_card] at this; omega
        have hfgnd : (f + g).natDegree = 0 := by
          have := natDegree_add_le f g; omega
        have hfg_roots_eq : (↑([] : List ℝ) : Multiset ℝ) = (f + g).roots := by
          have h := hfg_rr.2; rw [hfgnd] at h
          exact (Multiset.card_eq_zero.mp h).symm
        exact ⟨hh, hfg_rr, [], [], List.Pairwise.nil, List.Pairwise.nil,
          hss_h_eq, hfg_roots_eq, Or.inr ⟨rfl, trivial⟩⟩
      | cons s₁ rest_ss =>
        -- Non-degenerate: both same-degree
        obtain ⟨r₁_f, rest_f, rfl⟩ : ∃ a l, rs_f = a :: l := by
          cases rs_f with
          | nil => simp only [List.length_nil, List.length_cons] at hlen_f_alt; omega
          | cons a l => exact ⟨a, l, rfl⟩
        obtain ⟨r₁_g, rest_g, rfl⟩ : ∃ a l, rs_g = a :: l := by
          cases rs_g with
          | nil => simp only [List.length_nil, List.length_cons] at hlen_g_alt; omega
          | cons a l => exact ⟨a, l, rfl⟩
        obtain ⟨hs₁_r₁f, hint_f_tail⟩ := halt_f
        obtain ⟨hs₁_r₁g, hint_g_tail⟩ := halt_g
        have hlen_f' : rest_f.length = rest_ss.length := by
          simp only [List.length_cons] at hlen_f_alt; omega
        have hlen_g' : rest_g.length = rest_ss.length := by
          simp only [List.length_cons] at hlen_g_alt; omega
        -- Degrees
        have hf_deg : (r₁_f :: rest_f).length = f.natDegree := by
          have := hf.2; rw [← hrs_f_eq, Multiset.coe_card] at this; exact this
        have hg_deg : (r₁_g :: rest_g).length = g.natDegree := by
          have := hg.2; rw [← hrs_g_eq, Multiset.coe_card] at this; exact this
        have hdeg_eq : f.natDegree = g.natDegree := by
          simp [List.length_cons] at hf_deg hg_deg hlen_f_alt hlen_g_alt; omega
        have hfg_deg : (f + g).natDegree = f.natDegree := by
          apply le_antisymm
          · have h := natDegree_add_le f g; rwa [max_eq_left hdeg_eq.symm.le] at h
          · apply le_natDegree_of_ne_zero; rw [coeff_add]
            have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
            have hgc : g.coeff f.natDegree = g.leadingCoeff := by
              unfold leadingCoeff; rw [← hdeg_eq]
            rw [hfc, hgc]
            exact ne_of_gt (by unfold HasPosLeadingCoeff at hf_pos hg_pos; linarith)
        -- Call wagner2_roots_exist with empty consumed sets
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
          wagner2_roots_exist f g hf hg hf_pos hg_pos hcop 0 0
            r₁_f r₁_g rest_f rest_g rest_ss hlen_f' hlen_g'
            hint_f_tail hint_g_tail (by simp [hrs_f_eq]) (by simp [hrs_g_eq])
            (by simp) (by simp) (by simp) (by simp)
        -- us exhausts roots of f+g
        have hus_nodup : us.Nodup := hus_pw.imp ne_of_lt
        have hus_sub : (↑us : Multiset ℝ) ≤ (f + g).roots := by
          rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
          intro u hu
          exact (mem_roots hfg_rr.1).mpr (hus_root u (Multiset.mem_coe.mp hu))
        have hus_eq : (↑us : Multiset ℝ) = (f + g).roots :=
          Multiset.eq_of_le_of_card_le hus_sub (by
            rw [Multiset.coe_card, hfg_rr.2, hfg_deg]
            simp [List.length_cons] at hf_deg hus_len; omega)
        -- Extract head of us for ListAlternates
        obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
          cases us with | nil => simp at hus_len | cons a l => exact ⟨a, l, rfl⟩
        have hs₁_u1 : s₁ ≤ u1 :=
          le_trans (le_min hs₁_r₁f hs₁_r₁g) (hus_lb u1 (List.mem_cons_self ..))
        exact ⟨hh, hfg_rr, s₁ :: rest_ss, u1 :: us_tail,
          hss_h_sorted, hus_pw.imp le_of_lt, hss_h_eq, hus_eq,
          Or.inr ⟨by simp only [List.length_cons] at hlen_f_alt hus_len ⊢; omega,
                   ⟨hs₁_u1, hus_int⟩⟩⟩

end RealRooted
