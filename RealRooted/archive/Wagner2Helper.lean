/-
# Wagner (2) recursive helper

`wagner2_roots_exist`: given h-roots interlacing into both f-roots and g-roots,
find roots of f+g that interlace with h-roots. Uses consumed multisets to track
roots already processed in prior intervals.
-/
import RealRooted.Basic
import RealRooted.Interlacing
import RealRooted.SignLemmas
import RealRooted.Wagner1

open Polynomial

noncomputable section

namespace RealRooted

/-- Core of Wagner (2): given h's roots (ss) interlacing into both f's roots (rs_f)
    and g's roots (rs_g), find roots us of f+g with ListInterlaces ss us.
    The consumed multisets track roots already processed. -/
lemma wagner2_roots_exist (f g : ℝ[X])
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hcop : IsCoprime f g)
    (consumed_f consumed_g : Multiset ℝ) :
    ∀ (rf rg : ℝ) (rest_f rest_g ss : List ℝ),
    rest_f.length = ss.length →
    rest_g.length = ss.length →
    ListInterlaces ss (rf :: rest_f) →
    ListInterlaces ss (rg :: rest_g) →
    (↑(rf :: rest_f) : Multiset ℝ) + consumed_f = f.roots →
    (↑(rg :: rest_g) : Multiset ℝ) + consumed_g = g.roots →
    (∀ r ∈ consumed_f, r ≤ rf) →
    (∀ r ∈ consumed_g, r ≤ rg) →
    (∀ r ∈ consumed_f, r ≤ rg) →
    (∀ r ∈ consumed_g, r ≤ rf) →
    ∃ us : List ℝ, us.length = ss.length + 1 ∧ ListInterlaces ss us ∧
      (∀ u ∈ us, (f + g).IsRoot u) ∧ us.Pairwise (· < ·) ∧
      ∀ u ∈ us, min rf rg ≤ u
  | rf, rg, [], [], [], _, _, _, _, hrf_eq, hrg_eq,
    hcons_f, hcons_g, hcons_f2, hcons_g2 => by
    have hrf_root : f.IsRoot rf := (mem_roots hf.1).mp (by rw [← hrf_eq]; simp)
    have hrg_root : g.IsRoot rg := (mem_roots hg.1).mp (by rw [← hrg_eq]; simp)
    have hf_roots : f.roots = rf ::ₘ consumed_f := by
      rw [← hrf_eq, ← Multiset.cons_coe, Multiset.cons_add]; simp
    have hg_roots : g.roots = rg ::ₘ consumed_g := by
      rw [← hrg_eq, ← Multiset.cons_coe, Multiset.cons_add]; simp
    have hf_erase : f.roots.erase rf = consumed_f := by
      rw [hf_roots, Multiset.erase_cons_head]
    have hg_erase : g.roots.erase rg = consumed_g := by
      rw [hg_roots, Multiset.erase_cons_head]
    -- Use sign lemma with a = min(rf,rg), b = max(rf,rg) + 1
    have hab : min rf rg ≤ max rf rg + 1 := by
      have := @min_le_max ℝ _ rf rg; linarith
    have has : min rf rg ≤ rf := min_le_left rf rg
    have hat : min rf rg ≤ rg := min_le_right rf rg
    have hsb : rf ≤ max rf rg + 1 := by linarith [le_max_left rf rg]
    have htb : rg ≤ max rf rg + 1 := by linarith [le_max_right rf rg]
    have hcons_f_min : ∀ r ∈ consumed_f, r ≤ min rf rg :=
      fun r hr => le_min (hcons_f r hr) (hcons_f2 r hr)
    have hcons_g_min : ∀ r ∈ consumed_g, r ≤ min rf rg :=
      fun r hr => le_min (hcons_g2 r hr) (hcons_g r hr)
    have hf_dich : ∀ r ∈ f.roots.erase rf, r ≤ min rf rg ∨ max rf rg + 1 ≤ r := by
      rw [hf_erase]; intro r hr; exact Or.inl (hcons_f_min r hr)
    have hg_dich : ∀ r ∈ g.roots.erase rg, r ≤ min rf rg ∨ max rf rg + 1 ≤ r := by
      rw [hg_erase]; intro r hr; exact Or.inl (hcons_g_min r hr)
    have hcount_eq : (g.roots.erase rg).countP (max rf rg + 1 ≤ ·) =
        (f.roots.erase rf).countP (max rf rg + 1 ≤ ·) := by
      rw [hf_erase, hg_erase]
      have h1 : consumed_f.countP (max rf rg + 1 ≤ ·) = 0 :=
        Multiset.countP_eq_zero.mpr (fun r hr => not_le.mpr (by
          linarith [hcons_f r hr, le_max_left rf rg]))
      have h2 : consumed_g.countP (max rf rg + 1 ≤ ·) = 0 :=
        Multiset.countP_eq_zero.mpr (fun r hr => not_le.mpr (by
          linarith [hcons_g2 r hr, le_max_left rf rg]))
      rw [h1, h2]
    rcases le_or_gt rf rg with hrfrg | hrfrg
    · have hsign := opposite_sign_at_interlacing_roots hf hg hf_pos hg_pos hab
        has hsb hat htb hrfrg hrf_root hrg_root hf_dich hg_dich hcount_eq
      obtain ⟨u, huf, hug, hu_root⟩ := sum_has_root_between hrfrg hrf_root hrg_root hsign
      exact ⟨[u], rfl, trivial, fun v hv => by simp at hv; rw [hv]; exact hu_root,
        List.pairwise_singleton _ _,
        fun v hv => by simp at hv; rw [hv]; exact le_trans (min_le_left rf rg) huf⟩
    · have hrgrf := le_of_lt hrfrg
      have hsign := opposite_sign_at_interlacing_roots hg hf hg_pos hf_pos hab
        hat htb has hsb hrgrf hrg_root hrf_root hg_dich hf_dich hcount_eq.symm
      obtain ⟨u, hug, huf, hu_root⟩ := sum_has_root_between hrgrf hrg_root hrf_root
        (by linarith [mul_comm (Polynomial.eval rf g) (Polynomial.eval rg f)])
      have hu_root' : (f + g).IsRoot u := by rwa [add_comm]
      exact ⟨[u], rfl, trivial, fun v hv => by simp at hv; rw [hv]; exact hu_root',
        List.pairwise_singleton _ _,
        fun v hv => by simp at hv; rw [hv]; exact le_trans (min_le_right rf rg) hug⟩
  | rf, rg, rf2 :: rest_f, rg2 :: rest_g, s :: rest_ss,
    hlen_f, hlen_g, hint_f, hint_g, hrs_f_eq, hrs_g_eq,
    hcons_f, hcons_g, hcons_f2, hcons_g2 => by
    obtain ⟨hrfs, hsrf2, hint_f_tail⟩ := hint_f
    obtain ⟨hrgs, hsrg2, hint_g_tail⟩ := hint_g
    have hrf_root : f.IsRoot rf := (mem_roots hf.1).mp (by rw [← hrs_f_eq]; simp)
    have hrg_root : g.IsRoot rg := (mem_roots hg.1).mp (by rw [← hrs_g_eq]; simp)
    have hf_roots : f.roots = rf ::ₘ (↑(rf2 :: rest_f) + consumed_f) := by
      rw [← hrs_f_eq, ← Multiset.cons_coe, Multiset.cons_add]
    have hg_roots : g.roots = rg ::ₘ (↑(rg2 :: rest_g) + consumed_g) := by
      rw [← hrs_g_eq, ← Multiset.cons_coe, Multiset.cons_add]
    have hf_erase : f.roots.erase rf = ↑(rf2 :: rest_f) + consumed_f := by
      rw [hf_roots, Multiset.erase_cons_head]
    have hg_erase : g.roots.erase rg = ↑(rg2 :: rest_g) + consumed_g := by
      rw [hg_roots, Multiset.erase_cons_head]
    -- All tail elements are ≥ s
    have hrf_tail_ge : ∀ r ∈ (rf2 :: rest_f), s ≤ r := by
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr'
      · exact hsrf2
      · exact le_trans hsrf2 (listInterlaces_rs_all_ge rest_ss rest_f rf2 hint_f_tail r hr')
    have hrg_tail_ge : ∀ r ∈ (rg2 :: rest_g), s ≤ r := by
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr'
      · exact hsrg2
      · exact le_trans hsrg2 (listInterlaces_rs_all_ge rest_ss rest_g rg2 hint_g_tail r hr')
    -- Dichotomy
    have hf_dich : ∀ r ∈ f.roots.erase rf, r ≤ min rf rg ∨ s ≤ r := by
      rw [hf_erase]; intro r hr
      rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
      · exact Or.inr (hrf_tail_ge r (Multiset.mem_coe.mp hr_rest))
      · exact Or.inl (le_min (hcons_f r hr_cons) (hcons_f2 r hr_cons))
    have hg_dich : ∀ r ∈ g.roots.erase rg, r ≤ min rf rg ∨ s ≤ r := by
      rw [hg_erase]; intro r hr
      rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
      · exact Or.inr (hrg_tail_ge r (Multiset.mem_coe.mp hr_rest))
      · exact Or.inl (le_min (hcons_g2 r hr_cons) (hcons_g r hr_cons))
    -- Count equality
    have hcount_eq : (g.roots.erase rg).countP (s ≤ ·) =
        (f.roots.erase rf).countP (s ≤ ·) := by
      rw [hf_erase, hg_erase, Multiset.countP_add, Multiset.countP_add]
      have hcf := Multiset.countP_eq_card.mpr (fun r hr =>
        hrf_tail_ge r (Multiset.mem_coe.mp hr))
      have hcg := Multiset.countP_eq_card.mpr (fun r hr =>
        hrg_tail_ge r (Multiset.mem_coe.mp hr))
      -- consumed roots are all < s (coprimality prevents = s)
      have hcf_cons : consumed_f.countP (s ≤ ·) = 0 := by
        apply Multiset.countP_eq_zero.mpr
        intro r hr
        simp only [not_le]
        rcases lt_or_eq_of_le (le_trans (hcons_f r hr) hrfs) with h | h
        · exact h
        · exfalso
          have hfr : Polynomial.eval r f = 0 :=
            (mem_roots hf.1).mp (hrs_f_eq ▸ Multiset.mem_add.mpr (Or.inr hr))
          have hrg_s : rg = s := le_antisymm hrgs (h ▸ hcons_f2 r hr)
          have hgr : Polynomial.eval r g = 0 := by rw [h, ← hrg_s]; exact hrg_root
          obtain ⟨p, q, hpq⟩ := hcop
          have h1 := congr_arg (Polynomial.eval r) hpq
          simp [eval_add, eval_mul, eval_one, hfr, hgr] at h1
      have hcg_cons : consumed_g.countP (s ≤ ·) = 0 := by
        apply Multiset.countP_eq_zero.mpr
        intro r hr
        simp only [not_le]
        rcases lt_or_eq_of_le (le_trans (hcons_g r hr) hrgs) with h | h
        · exact h
        · exfalso
          have hgr : Polynomial.eval r g = 0 :=
            (mem_roots hg.1).mp (hrs_g_eq ▸ Multiset.mem_add.mpr (Or.inr hr))
          have hrf_s : rf = s := le_antisymm hrfs (h ▸ hcons_g2 r hr)
          have hfr : Polynomial.eval r f = 0 := by rw [h, ← hrf_s]; exact hrf_root
          obtain ⟨p, q, hpq⟩ := hcop
          have h1 := congr_arg (Polynomial.eval r) hpq
          simp [eval_add, eval_mul, eval_one, hfr, hgr] at h1
      rw [hcg, hcf, hcg_cons, hcf_cons, Multiset.coe_card, Multiset.coe_card]
      simp only [List.length_cons] at hlen_f hlen_g ⊢; omega
    -- Sign lemma + IVT
    have hab : min rf rg ≤ s := le_trans (min_le_left rf rg) hrfs
    rcases le_or_gt rf rg with hrfrg | hrfrg
    · have hsign := opposite_sign_at_interlacing_roots hf hg hf_pos hg_pos hab
        (min_le_left rf rg) hrfs (min_le_right rf rg) hrgs hrfrg
        hrf_root hrg_root hf_dich hg_dich hcount_eq
      obtain ⟨u, huf, hug, hu_root⟩ := sum_has_root_between hrfrg hrf_root hrg_root hsign
      -- u < s (coprimality)
      have hu_lt_s : u < s := by
        rcases lt_or_eq_of_le (le_trans hug hrgs) with h | h
        · exact h
        · exfalso
          have hrg_s : rg = s := le_antisymm hrgs (h ▸ hug)
          have hgs : Polynomial.eval s g = 0 := by rw [← hrg_s]; exact hrg_root
          have hfs : Polynomial.eval s f = 0 := by
            have := h ▸ hu_root
            rw [Polynomial.IsRoot.def, Polynomial.eval_add, hgs, add_zero] at this; exact this
          obtain ⟨p, q, hpq⟩ := hcop
          have := congr_arg (Polynomial.eval s) hpq
          simp [eval_add, eval_mul, eval_one, hfs, hgs] at this
      -- Recursive call
      have hlen_f' : rest_f.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_f; omega
      have hlen_g' : rest_g.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_g; omega
      have hrs_f_eq' : (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f) = f.roots :=
        calc (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f)
            = rf ::ₘ consumed_f + ↑(rf2 :: rest_f) := add_comm _ _
          _ = rf ::ₘ (consumed_f + ↑(rf2 :: rest_f)) := Multiset.cons_add ..
          _ = rf ::ₘ (↑(rf2 :: rest_f) + consumed_f) := by rw [add_comm consumed_f]
          _ = f.roots := by rw [← hf_roots]
      have hrs_g_eq' : (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g) = g.roots :=
        calc (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g)
            = rg ::ₘ consumed_g + ↑(rg2 :: rest_g) := add_comm _ _
          _ = rg ::ₘ (consumed_g + ↑(rg2 :: rest_g)) := Multiset.cons_add ..
          _ = rg ::ₘ (↑(rg2 :: rest_g) + consumed_g) := by rw [add_comm consumed_g]
          _ = g.roots := by rw [← hg_roots]
      have hcons_f' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rf2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrfs hsrf2
        · exact le_trans (hcons_f r hr) (le_trans hrfs hsrf2)
      have hcons_g' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rg2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrgs hsrg2
        · exact le_trans (hcons_g r hr) (le_trans hrgs hsrg2)
      have hcons_f2' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rg2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrfs hsrg2
        · exact le_trans (hcons_f2 r hr) (le_trans hrgs hsrg2)
      have hcons_g2' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rf2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrgs hsrf2
        · exact le_trans (hcons_g2 r hr) (le_trans hrfs hsrf2)
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
        wagner2_roots_exist f g hf hg hf_pos hg_pos hcop
          (rf ::ₘ consumed_f) (rg ::ₘ consumed_g)
          rf2 rg2 rest_f rest_g rest_ss hlen_f' hlen_g'
          hint_f_tail hint_g_tail hrs_f_eq' hrs_g_eq'
          hcons_f' hcons_g' hcons_f2' hcons_g2'
      -- us elements ≥ min rf2 rg2 ≥ s
      have hus_ge_s : ∀ w ∈ us, s ≤ w := by
        intro w hw; exact le_trans (le_min hsrf2 hsrg2) (hus_lb w hw)
      -- Construct interlacing: need u ≤ s ≤ us.head
      obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
        cases us with | nil => simp at hus_len | cons a l => exact ⟨a, l, rfl⟩
      have hu_le_s : u ≤ s := le_trans hug hrgs
      have hs_le_u1 : s ≤ u1 := hus_ge_s u1 (List.mem_cons_self ..)
      have hint_result : ListInterlaces (s :: rest_ss) (u :: u1 :: us_tail) :=
        ⟨hu_le_s, hs_le_u1, hus_int⟩
      exact ⟨u :: u1 :: us_tail, by simp [hus_len],
        hint_result,
        fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hu_root) (hus_root v),
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu_lt_s (hus_ge_s w hw), hus_pw⟩,
        fun v hv => (List.mem_cons.mp hv).elim
          (fun h => h ▸ le_trans (min_le_left rf rg) huf)
          (fun h => le_trans (le_trans (min_le_left rf rg) hrfs) (le_trans (le_min hsrf2 hsrg2) (hus_lb v h)))⟩
    · -- rg < rf: symmetric
      have hrgrf := le_of_lt hrfrg
      have hsign := opposite_sign_at_interlacing_roots hg hf hg_pos hf_pos hab
        (min_le_right rf rg) hrgs (min_le_left rf rg) hrfs hrgrf
        hrg_root hrf_root hg_dich hf_dich hcount_eq.symm
      obtain ⟨u, hug, huf, hu_root⟩ := sum_has_root_between hrgrf hrg_root hrf_root
        (by linarith [mul_comm (Polynomial.eval rf g) (Polynomial.eval rg f)])
      have hu_root' : (f + g).IsRoot u := by rwa [add_comm]
      have hu_lt_s : u < s := by
        rcases lt_or_eq_of_le (le_trans huf hrfs) with h | h
        · exact h
        · exfalso
          have hrf_s : rf = s := le_antisymm hrfs (h ▸ huf)
          have hfs : Polynomial.eval s f = 0 := by rw [← hrf_s]; exact hrf_root
          have hgs : Polynomial.eval s g = 0 := by
            have := h ▸ hu_root'
            rw [Polynomial.IsRoot.def, Polynomial.eval_add, hfs, zero_add] at this; exact this
          obtain ⟨p, q, hpq⟩ := hcop
          have := congr_arg (Polynomial.eval s) hpq
          simp [eval_add, eval_mul, eval_one, hfs, hgs] at this
      have hlen_f' : rest_f.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_f; omega
      have hlen_g' : rest_g.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_g; omega
      have hrs_f_eq' : (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f) = f.roots :=
        calc (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f)
            = rf ::ₘ consumed_f + ↑(rf2 :: rest_f) := add_comm _ _
          _ = rf ::ₘ (consumed_f + ↑(rf2 :: rest_f)) := Multiset.cons_add ..
          _ = rf ::ₘ (↑(rf2 :: rest_f) + consumed_f) := by rw [add_comm consumed_f]
          _ = f.roots := by rw [← hf_roots]
      have hrs_g_eq' : (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g) = g.roots :=
        calc (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g)
            = rg ::ₘ consumed_g + ↑(rg2 :: rest_g) := add_comm _ _
          _ = rg ::ₘ (consumed_g + ↑(rg2 :: rest_g)) := Multiset.cons_add ..
          _ = rg ::ₘ (↑(rg2 :: rest_g) + consumed_g) := by rw [add_comm consumed_g]
          _ = g.roots := by rw [← hg_roots]
      have hcons_f' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rf2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrfs hsrf2
        · exact le_trans (hcons_f r hr) (le_trans hrfs hsrf2)
      have hcons_g' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rg2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrgs hsrg2
        · exact le_trans (hcons_g r hr) (le_trans hrgs hsrg2)
      have hcons_f2' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rg2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrfs hsrg2
        · exact le_trans (hcons_f2 r hr) (le_trans hrgs hsrg2)
      have hcons_g2' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rf2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrgs hsrf2
        · exact le_trans (hcons_g2 r hr) (le_trans hrfs hsrf2)
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
        wagner2_roots_exist f g hf hg hf_pos hg_pos hcop
          (rf ::ₘ consumed_f) (rg ::ₘ consumed_g)
          rf2 rg2 rest_f rest_g rest_ss hlen_f' hlen_g'
          hint_f_tail hint_g_tail hrs_f_eq' hrs_g_eq'
          hcons_f' hcons_g' hcons_f2' hcons_g2'
      have hus_ge_s : ∀ w ∈ us, s ≤ w := by
        intro w hw; exact le_trans (le_min hsrf2 hsrg2) (hus_lb w hw)
      obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
        cases us with | nil => simp at hus_len | cons a l => exact ⟨a, l, rfl⟩
      have hu_le_s : u ≤ s := le_trans huf hrfs
      have hs_le_u1 : s ≤ u1 := hus_ge_s u1 (List.mem_cons_self ..)
      exact ⟨u :: u1 :: us_tail, by simp [hus_len],
        (⟨hu_le_s, hs_le_u1, hus_int⟩ : ListInterlaces (s :: rest_ss) (u :: u1 :: us_tail)),
        fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hu_root') (hus_root v),
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu_lt_s (hus_ge_s w hw), hus_pw⟩,
        fun v hv => (List.mem_cons.mp hv).elim
          (fun h => h ▸ le_trans (min_le_right rf rg) hug)
          (fun h => le_trans (le_trans (min_le_right rf rg) hrgs) (le_trans (le_min hsrf2 hsrg2) (hus_lb v h)))⟩
    /- obtain ⟨hrfs, hsrf2, hint_f_tail⟩ := hint_f
    obtain ⟨hrgs, hsrg2, hint_g_tail⟩ := hint_g
    have hrf_root : f.IsRoot rf := (mem_roots hf.1).mp (by rw [← hrs_f_eq]; simp)
    have hrg_root : g.IsRoot rg := (mem_roots hg.1).mp (by rw [← hrs_g_eq]; simp)
    have hf_roots : f.roots = rf ::ₘ (↑(rf2 :: rest_f) + consumed_f) := by
      rw [← hrs_f_eq, ← Multiset.cons_coe, Multiset.cons_add]
    have hg_roots : g.roots = rg ::ₘ (↑(rg2 :: rest_g) + consumed_g) := by
      rw [← hrs_g_eq, ← Multiset.cons_coe, Multiset.cons_add]
    have hf_erase : f.roots.erase rf = ↑(rf2 :: rest_f) + consumed_f := by
      rw [hf_roots, Multiset.erase_cons_head]
    have hg_erase : g.roots.erase rg = ↑(rg2 :: rest_g) + consumed_g := by
      rw [hg_roots, Multiset.erase_cons_head]
    -- All tail elements are ≥ s
    have hrf_tail_ge : ∀ r ∈ (rf2 :: rest_f), s ≤ r := by
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr'
      · exact hsrf2
      · exact le_trans hsrf2 (listInterlaces_rs_all_ge rest_ss rest_f rf2 hint_f_tail r hr')
    have hrg_tail_ge : ∀ r ∈ (rg2 :: rest_g), s ≤ r := by
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr'
      · exact hsrg2
      · exact le_trans hsrg2 (listInterlaces_rs_all_ge rest_ss rest_g rg2 hint_g_tail r hr')
    -- Dichotomy and count
    have hcons_f_min : ∀ r ∈ consumed_f, r ≤ min rf rg :=
      fun r hr => le_min (hcons_f r hr) (hcons_f2 r hr)
    have hcons_g_min : ∀ r ∈ consumed_g, r ≤ min rf rg :=
      fun r hr => le_min (hcons_g2 r hr) (hcons_g r hr)
    have hf_dich : ∀ r ∈ f.roots.erase rf, r ≤ min rf rg ∨ s ≤ r := by
      rw [hf_erase]; intro r hr
      rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
      · exact Or.inr (hrf_tail_ge r (Multiset.mem_coe.mp hr_rest))
      · exact Or.inl (hcons_f_min r hr_cons)
    have hg_dich : ∀ r ∈ g.roots.erase rg, r ≤ min rf rg ∨ s ≤ r := by
      rw [hg_erase]; intro r hr
      rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
      · exact Or.inr (hrg_tail_ge r (Multiset.mem_coe.mp hr_rest))
      · exact Or.inl (hcons_g_min r hr_cons)
    have hcount_eq : (g.roots.erase rg).countP (s ≤ ·) =
        (f.roots.erase rf).countP (s ≤ ·) := by
      rw [hf_erase, hg_erase, Multiset.countP_add, Multiset.countP_add]
      have hcf := Multiset.countP_eq_card.mpr (fun r hr =>
        hrf_tail_ge r (Multiset.mem_coe.mp hr))
      have hcg := Multiset.countP_eq_card.mpr (fun r hr =>
        hrg_tail_ge r (Multiset.mem_coe.mp hr))
      -- consumed roots are all < s (coprimality prevents = s)
      have hcf_cons : consumed_f.countP (s ≤ ·) = 0 := by
        apply Multiset.countP_eq_zero.mpr
        intro r hr
        simp only [not_le]
        rcases lt_or_eq_of_le (le_trans (hcons_f r hr) hrfs) with h | h
        · exact h
        · exfalso
          have hfr : Polynomial.eval r f = 0 :=
            (mem_roots hf.1).mp (hrs_f_eq ▸ Multiset.mem_add.mpr (Or.inr hr))
          have hrg_s : rg = s := le_antisymm hrgs (h ▸ hcons_f2 r hr)
          have hgr : Polynomial.eval r g = 0 := by rw [h, ← hrg_s]; exact hrg_root
          obtain ⟨p, q, hpq⟩ := hcop
          have h1 := congr_arg (Polynomial.eval r) hpq
          simp [eval_add, eval_mul, eval_one, hfr, hgr] at h1
      have hcg_cons : consumed_g.countP (s ≤ ·) = 0 := by
        apply Multiset.countP_eq_zero.mpr
        intro r hr
        simp only [not_le]
        rcases lt_or_eq_of_le (le_trans (hcons_g r hr) hrgs) with h | h
        · exact h
        · exfalso
          have hgr : Polynomial.eval r g = 0 :=
            (mem_roots hg.1).mp (hrs_g_eq ▸ Multiset.mem_add.mpr (Or.inr hr))
          have hrf_s : rf = s := le_antisymm hrfs (h ▸ hcons_g2 r hr)
          have hfr : Polynomial.eval r f = 0 := by rw [h, ← hrf_s]; exact hrf_root
          obtain ⟨p, q, hpq⟩ := hcop
          have h1 := congr_arg (Polynomial.eval r) hpq
          simp [eval_add, eval_mul, eval_one, hfr, hgr] at h1
      rw [hcg, hcf, hcg_cons, hcf_cons, Multiset.coe_card, Multiset.coe_card]
      simp only [List.length_cons] at hlen_f hlen_g ⊢; omega
    -- Sign lemma + IVT
    have hab : min rf rg ≤ s := le_trans (min_le_left rf rg) hrfs
    rcases le_or_gt rf rg with hrfrg | hrfrg
    · have hsign := opposite_sign_at_interlacing_roots hf hg hf_pos hg_pos hab
        (min_le_left rf rg) hrfs (min_le_right rf rg) hrgs hrfrg
        hrf_root hrg_root hf_dich hg_dich hcount_eq
      obtain ⟨u, huf, hug, hu_root⟩ := sum_has_root_between hrfrg hrf_root hrg_root hsign
      have hu_lt_s : u < s := by
        rcases lt_or_eq_of_le (le_trans hug hrgs) with h | h
        · exact h
        · exfalso
          have hrg_s : rg = s := le_antisymm hrgs (h ▸ hug)
          have hgs : Polynomial.eval s g = 0 := by rw [← hrg_s]; exact hrg_root
          have hfs : Polynomial.eval s f = 0 := by
            have := h ▸ hu_root
            rw [Polynomial.IsRoot.def, Polynomial.eval_add, hgs, add_zero] at this; exact this
          obtain ⟨p, q, hpq⟩ := hcop
          have := congr_arg (Polynomial.eval s) hpq
          simp [eval_add, eval_mul, eval_one, hfs, hgs] at this
      -- Recursive call setup
      have hlen_f' : rest_f.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_f; omega
      have hlen_g' : rest_g.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_g; omega
      have hrs_f_eq' : (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f) = f.roots :=
        calc (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f)
            = rf ::ₘ consumed_f + ↑(rf2 :: rest_f) := add_comm _ _
          _ = rf ::ₘ (consumed_f + ↑(rf2 :: rest_f)) := Multiset.cons_add ..
          _ = rf ::ₘ (↑(rf2 :: rest_f) + consumed_f) := by rw [add_comm consumed_f]
          _ = f.roots := by rw [← hf_roots]
      have hrs_g_eq' : (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g) = g.roots :=
        calc (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g)
            = rg ::ₘ consumed_g + ↑(rg2 :: rest_g) := add_comm _ _
          _ = rg ::ₘ (consumed_g + ↑(rg2 :: rest_g)) := Multiset.cons_add ..
          _ = rg ::ₘ (↑(rg2 :: rest_g) + consumed_g) := by rw [add_comm consumed_g]
          _ = g.roots := by rw [← hg_roots]
      have hcons_f' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rf2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrfs hsrf2
        · exact le_trans (hcons_f r hr) (le_trans hrfs hsrf2)
      have hcons_g' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rg2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrgs hsrg2
        · exact le_trans (hcons_g r hr) (le_trans hrgs hsrg2)
      have hcons_f2' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rg2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrfs hsrg2
        · exact le_trans (hcons_f2 r hr) (le_trans hrgs hsrg2)
      have hcons_g2' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rf2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrgs hsrf2
        · exact le_trans (hcons_g2 r hr) (le_trans hrfs hsrf2)
      have hcount' : (rf ::ₘ consumed_f).card = (rg ::ₘ consumed_g).card := by
        simp [hcount]
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner2_roots_exist f g hf hg hf_pos hg_pos hcop
          (rf ::ₘ consumed_f) (rg ::ₘ consumed_g)
          rf2 rg2 rest_f rest_g rest_ss hlen_f' hlen_g'
          hint_f_tail hint_g_tail hrs_f_eq' hrs_g_eq'
          hcons_f' hcons_g' hcons_f2' hcons_g2' hcount'
      have hus_ge_s : ∀ w ∈ us, s ≤ w :=
        fun w hw => listInterlaces_all_ge us rest_ss s hus_int w hw
      exact ⟨u :: us, by simp [hus_len],
        ⟨le_trans hrfs huf, le_trans hug hrgs, hus_int⟩,
        fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hu_root) (hus_root v),
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu_lt_s (hus_ge_s w hw), hus_pw⟩⟩
    · -- rg < rf: symmetric
      have hrgrf := le_of_lt hrfrg
      have hsign := opposite_sign_at_interlacing_roots hg hf hg_pos hf_pos hab
        (min_le_right rf rg) hrgs (min_le_left rf rg) hrfs hrgrf
        hrg_root hrf_root hg_dich hf_dich hcount_eq.symm
      obtain ⟨u, hug, huf, hu_root⟩ := sum_has_root_between hrgrf hrg_root hrf_root
        (by linarith [mul_comm (Polynomial.eval rf g) (Polynomial.eval rg f)])
      have hu_root' : (f + g).IsRoot u := by rwa [add_comm]
      have hu_lt_s : u < s := by
        rcases lt_or_eq_of_le (le_trans huf hrfs) with h | h
        · exact h
        · exfalso
          have hrf_s : rf = s := le_antisymm hrfs (h ▸ huf)
          have hfs : Polynomial.eval s f = 0 := by rw [← hrf_s]; exact hrf_root
          have hgs : Polynomial.eval s g = 0 := by
            have := h ▸ hu_root'
            rw [Polynomial.IsRoot.def, Polynomial.eval_add, hfs, zero_add] at this; exact this
          obtain ⟨p, q, hpq⟩ := hcop
          have := congr_arg (Polynomial.eval s) hpq
          simp [eval_add, eval_mul, eval_one, hfs, hgs] at this
      have hlen_f' : rest_f.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_f; omega
      have hlen_g' : rest_g.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_g; omega
      have hrs_f_eq' : (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f) = f.roots :=
        calc (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f)
            = rf ::ₘ consumed_f + ↑(rf2 :: rest_f) := add_comm _ _
          _ = rf ::ₘ (consumed_f + ↑(rf2 :: rest_f)) := Multiset.cons_add ..
          _ = rf ::ₘ (↑(rf2 :: rest_f) + consumed_f) := by rw [add_comm consumed_f]
          _ = f.roots := by rw [← hf_roots]
      have hrs_g_eq' : (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g) = g.roots :=
        calc (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g)
            = rg ::ₘ consumed_g + ↑(rg2 :: rest_g) := add_comm _ _
          _ = rg ::ₘ (consumed_g + ↑(rg2 :: rest_g)) := Multiset.cons_add ..
          _ = rg ::ₘ (↑(rg2 :: rest_g) + consumed_g) := by rw [add_comm consumed_g]
          _ = g.roots := by rw [← hg_roots]
      have hcons_f' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rf2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrfs hsrf2
        · exact le_trans (hcons_f r hr) (le_trans hrfs hsrf2)
      have hcons_g' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rg2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrgs hsrg2
        · exact le_trans (hcons_g r hr) (le_trans hrgs hsrg2)
      have hcons_f2' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rg2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrfs hsrg2
        · exact le_trans (hcons_f2 r hr) (le_trans hrgs hsrg2)
      have hcons_g2' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rf2 := by
        intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact le_trans hrgs hsrf2
        · exact le_trans (hcons_g2 r hr) (le_trans hrfs hsrf2)
      have hcount' : (rf ::ₘ consumed_f).card = (rg ::ₘ consumed_g).card := by
        simp [hcount]
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner2_roots_exist f g hf hg hf_pos hg_pos hcop
          (rf ::ₘ consumed_f) (rg ::ₘ consumed_g)
          rf2 rg2 rest_f rest_g rest_ss hlen_f' hlen_g'
          hint_f_tail hint_g_tail hrs_f_eq' hrs_g_eq'
          hcons_f' hcons_g' hcons_f2' hcons_g2' hcount'
      have hus_ge_s : ∀ w ∈ us, s ≤ w :=
        fun w hw => listInterlaces_all_ge us rest_ss s hus_int w hw
      exact ⟨u :: us, by simp [hus_len],
        ⟨le_trans hrgs hug, le_trans huf hrfs, hus_int⟩,
        fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hu_root') (hus_root v),
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu_lt_s (hus_ge_s w hw), hus_pw⟩⟩ -/
  | _, _, [], _, _ :: _, hlen_f, _, _, _, _, _, _, _, _, _ => by simp at hlen_f
  | _, _, _ :: _, [], _ :: _, _, hlen_g, _, _, _, _, _, _, _, _ => by simp at hlen_g
  | _, _, [], _ :: _, [], hlen_f, _, _, _, _, _, _, _, _, _ => by
    have := hlen_f; simp_all
  | _, _, _ :: _, [], [], _, hlen_g, _, _, _, _, _, _, _, _ => by
    have := hlen_g; simp_all
  | _, _, _ :: _, _ :: _, [], hlen_f, _, _, _, _, _, _, _, _, _ => by
    have := hlen_f; simp_all

end RealRooted
