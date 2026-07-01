import RealRooted.WagnerRightSum

/-!
# Wagner (2): Common-left addition theorems

If h ≪ f and h ≪ g with positive leading coefficients, then h ≪ (f + g).
Includes SumCompatibleLeft for recursive n-summand assembly.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted

section

/-- Core of Wagner (2): given h's roots (ss) interlacing into both f's roots (rs_f)
    and g's roots (rs_g), find roots us of f+g with ListInterlaces ss us.
    The consumed multisets track roots already processed. -/
private lemma wagner2_roots_exist (f g : ℝ[X])
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
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
    have hrf_root : f.IsRoot rf := (mem_roots hf_ne).mp (by rw [← hrf_eq]; simp)
    have hrg_root : g.IsRoot rg := (mem_roots hg_ne).mp (by rw [← hrg_eq]; simp)
    have hf_roots : f.roots = rf ::ₘ consumed_f := by
      simp_all
    have hg_roots : g.roots = rg ::ₘ consumed_g := by
      simp_all
    have hf_erase : f.roots.erase rf = consumed_f := by
      simp_all
    have hg_erase : g.roots.erase rg = consumed_g := by
      simp_all
    -- Use sign lemma with a = min(rf,rg), b = max(rf,rg) + 1
    have hab : min rf rg ≤ max rf rg + 1 := by
      grind
    have has : min rf rg ≤ rf := min_le_left rf rg
    have hat : min rf rg ≤ rg := min_le_right rf rg
    have hsb : rf ≤ max rf rg + 1 := by grind
    have htb : rg ≤ max rf rg + 1 := by grind
    have hcons_f_min : ∀ r ∈ consumed_f, r ≤ min rf rg :=
      fun r hr => le_min (hcons_f r hr) (hcons_f2 r hr)
    have hcons_g_min : ∀ r ∈ consumed_g, r ≤ min rf rg :=
      fun r hr => le_min (hcons_g2 r hr) (hcons_g r hr)
    have hf_dich : ∀ r ∈ f.roots.erase rf, r ≤ min rf rg ∨ max rf rg + 1 ≤ r := by
      simp_all
    have hg_dich : ∀ r ∈ g.roots.erase rg, r ≤ min rf rg ∨ max rf rg + 1 ≤ r := by
      simp_all
    have hcount_eq : (g.roots.erase rg).countP (max rf rg + 1 ≤ ·) =
        (f.roots.erase rf).countP (max rf rg + 1 ≤ ·) := by
      rw [hf_erase, hg_erase]
      have h1 : consumed_f.countP (max rf rg + 1 ≤ ·) = 0 :=
        Multiset.countP_eq_zero.mpr (fun r hr => not_le.mpr (by
          grind))
      have h2 : consumed_g.countP (max rf rg + 1 ≤ ·) = 0 :=
        Multiset.countP_eq_zero.mpr (fun r hr => not_le.mpr (by
          grind))
      lia
    rcases le_or_gt rf rg with hrfrg | hrfrg
    · have hsign :=
        opposite_sign_at_interlacing_roots hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos
        has hsb hat htb hrf_root hrg_root hf_dich hg_dich hcount_eq
      obtain ⟨u, huf, hug, hu_root⟩ := sum_has_root_between hrfrg hrf_root hrg_root hsign
      exact ⟨[u], rfl, trivial, fun v hv => by
        simp_all,
        List.pairwise_singleton _ _,
        fun v hv => by
          simp_all⟩
    · have hrgrf := le_of_lt hrfrg
      have hsign :=
          opposite_sign_at_interlacing_roots hg_ne hg_splits hf_ne hf_splits hg_pos hf_pos
        hat htb has hsb hrg_root hrf_root hg_dich hf_dich hcount_eq.symm
      obtain ⟨u, hug, huf, hu_root⟩ := sum_has_root_between hrgrf hrg_root hrf_root
        (by lia)
      have hu_root' : (f + g).IsRoot u := by rwa [add_comm]
      exact ⟨[u], rfl, trivial, fun v hv => by
        simp_all,
        List.pairwise_singleton _ _,
        fun v hv => by
          simp_all⟩
  | rf, rg, rf2 :: rest_f, rg2 :: rest_g, s :: rest_ss,
    hlen_f, hlen_g, hint_f, hint_g, hrs_f_eq, hrs_g_eq,
    hcons_f, hcons_g, hcons_f2, hcons_g2 => by
    obtain ⟨hrfs, hsrf2, hint_f_tail⟩ := hint_f
    obtain ⟨hrgs, hsrg2, hint_g_tail⟩ := hint_g
    have hrf_root : f.IsRoot rf := (mem_roots hf_ne).mp (by rw [← hrs_f_eq]; simp)
    have hrg_root : g.IsRoot rg := (mem_roots hg_ne).mp (by rw [← hrs_g_eq]; simp)
    have hf_roots : f.roots = rf ::ₘ (↑(rf2 :: rest_f) + consumed_f) := by
      rw [← hrs_f_eq, ← Multiset.cons_coe, Multiset.cons_add]
    have hg_roots : g.roots = rg ::ₘ (↑(rg2 :: rest_g) + consumed_g) := by
      rw [← hrs_g_eq, ← Multiset.cons_coe, Multiset.cons_add]
    have hf_erase : f.roots.erase rf = ↑(rf2 :: rest_f) + consumed_f := by
      simp_all
    have hg_erase : g.roots.erase rg = ↑(rg2 :: rest_g) + consumed_g := by
      simp_all
    -- All tail elements are ≥ s
    have hrf_tail_ge : ∀ r ∈ (rf2 :: rest_f), s ≤ r := by
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr'
      · lia
      · exact le_trans hsrf2 (listInterlaces_rs_all_ge rest_ss rest_f rf2 hint_f_tail r hr')
    have hrg_tail_ge : ∀ r ∈ (rg2 :: rest_g), s ≤ r := by
      intro r hr; rcases List.mem_cons.mp hr with rfl | hr'
      · lia
      · exact le_trans hsrg2 (listInterlaces_rs_all_ge rest_ss rest_g rg2 hint_g_tail r hr')
    -- Dichotomy
    have hf_dich : ∀ r ∈ f.roots.erase rf, r ≤ min rf rg ∨ s ≤ r := by
      rw [hf_erase]; intro r hr
      rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
      · exact Or.inr (hrf_tail_ge r (Multiset.mem_coe.mp hr_rest))
      · simp_all
    have hg_dich : ∀ r ∈ g.roots.erase rg, r ≤ min rf rg ∨ s ≤ r := by
      rw [hg_erase]; intro r hr
      rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
      · exact Or.inr (hrg_tail_ge r (Multiset.mem_coe.mp hr_rest))
      · simp_all
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
        · lia
        · exfalso
          have hfr : Polynomial.eval r f = 0 :=
            (mem_roots hf_ne).mp (hrs_f_eq ▸ Multiset.mem_add.mpr (Or.inr hr))
          have hrg_s : rg = s := le_antisymm hrgs (h ▸ hcons_f2 r hr)
          have hgr : Polynomial.eval r g = 0 := by simp_all
          obtain ⟨p, q, hpq⟩ := hcop
          have h1 := congr_arg (Polynomial.eval r) hpq
          simp [eval_add, eval_mul, eval_one, hfr, hgr] at h1
      have hcg_cons : consumed_g.countP (s ≤ ·) = 0 := by
        apply Multiset.countP_eq_zero.mpr
        intro r hr
        simp only [not_le]
        rcases lt_or_eq_of_le (le_trans (hcons_g r hr) hrgs) with h | h
        · lia
        · exfalso
          have hgr : Polynomial.eval r g = 0 :=
            (mem_roots hg_ne).mp (hrs_g_eq ▸ Multiset.mem_add.mpr (Or.inr hr))
          have hrf_s : rf = s := le_antisymm hrfs (h ▸ hcons_g2 r hr)
          have hfr : Polynomial.eval r f = 0 := by simp_all
          obtain ⟨p, q, hpq⟩ := hcop
          have h1 := congr_arg (Polynomial.eval r) hpq
          simp [eval_add, eval_mul, eval_one, hfr, hgr] at h1
      simp_all
    -- Sign lemma + IVT
    have hab : min rf rg ≤ s := le_trans (min_le_left rf rg) hrfs
    rcases le_or_gt rf rg with hrfrg | hrfrg
    · have hsign :=
        opposite_sign_at_interlacing_roots hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos
        (min_le_left rf rg) hrfs (min_le_right rf rg) hrgs
        hrf_root hrg_root hf_dich hg_dich hcount_eq
      obtain ⟨u, huf, hug, hu_root⟩ := sum_has_root_between hrfrg hrf_root hrg_root hsign
      -- u < s (coprimality)
      have hu_lt_s : u < s := by
        rcases lt_or_eq_of_le (le_trans hug hrgs) with h | h
        · lia
        · exfalso
          have hrg_s : rg = s := le_antisymm hrgs (h ▸ hug)
          have hgs : Polynomial.eval s g = 0 := by simp_all
          have hfs : Polynomial.eval s f = 0 := by
            simp_all
          obtain ⟨p, q, hpq⟩ := hcop
          have := congr_arg (Polynomial.eval s) hpq
          simp [eval_add, eval_mul, eval_one, hfs, hgs] at this
      -- Recursive call
      have hlen_f' : rest_f.length = rest_ss.length := by
        simp_all
      have hlen_g' : rest_g.length = rest_ss.length := by
        simp_all
      have hrs_f_eq' : (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f) = f.roots :=
        calc (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f)
            = rf ::ₘ consumed_f + ↑(rf2 :: rest_f) := add_comm _ _
          _ = rf ::ₘ (consumed_f + ↑(rf2 :: rest_f)) := Multiset.cons_add ..
          _ = rf ::ₘ (↑(rf2 :: rest_f) + consumed_f) := by grind
          _ = f.roots := by lia
      have hrs_g_eq' : (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g) = g.roots :=
        calc (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g)
            = rg ::ₘ consumed_g + ↑(rg2 :: rest_g) := add_comm _ _
          _ = rg ::ₘ (consumed_g + ↑(rg2 :: rest_g)) := Multiset.cons_add ..
          _ = rg ::ₘ (↑(rg2 :: rest_g) + consumed_g) := by grind
          _ = g.roots := by lia
      have hcons_f' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rf2 := by
        grind
      have hcons_g' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rg2 := by
        grind
      have hcons_f2' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rg2 := by
        grind
      have hcons_g2' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rf2 := by
        grind
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
        wagner2_roots_exist f g hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hcop
          (rf ::ₘ consumed_f) (rg ::ₘ consumed_g)
          rf2 rg2 rest_f rest_g rest_ss hlen_f' hlen_g'
          hint_f_tail hint_g_tail hrs_f_eq' hrs_g_eq'
          hcons_f' hcons_g' hcons_f2' hcons_g2'
      -- us elements ≥ min rf2 rg2 ≥ s
      have hus_ge_s : ∀ w ∈ us, s ≤ w := by
        grind
      -- Construct interlacing: need u ≤ s ≤ us.head
      obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
        cases us with | nil => simp at hus_len | cons a l => lia
      have hu_le_s : u ≤ s := le_trans hug hrgs
      have hs_le_u1 : s ≤ u1 := hus_ge_s u1 (List.mem_cons_self ..)
      have hint_result : ListInterlaces (s :: rest_ss) (u :: u1 :: us_tail) :=
        ⟨hu_le_s, hs_le_u1, hus_int⟩
      grind
    · -- rg < rf: symmetric
      have hrgrf := le_of_lt hrfrg
      have hsign :=
          opposite_sign_at_interlacing_roots hg_ne hg_splits hf_ne hf_splits hg_pos hf_pos
        (min_le_right rf rg) hrgs (min_le_left rf rg) hrfs
        hrg_root hrf_root hg_dich hf_dich hcount_eq.symm
      obtain ⟨u, hug, huf, hu_root⟩ := sum_has_root_between hrgrf hrg_root hrf_root
        (by lia)
      have hu_root' : (f + g).IsRoot u := by rwa [add_comm]
      have hu_lt_s : u < s := by
        rcases lt_or_eq_of_le (le_trans huf hrfs) with h | h
        · lia
        · exfalso
          have hrf_s : rf = s := le_antisymm hrfs (h ▸ huf)
          have hfs : Polynomial.eval s f = 0 := by simp_all
          have hgs : Polynomial.eval s g = 0 := by
            simp_all
          obtain ⟨p, q, hpq⟩ := hcop
          have := congr_arg (Polynomial.eval s) hpq
          simp [eval_add, eval_mul, eval_one, hfs, hgs] at this
      have hlen_f' : rest_f.length = rest_ss.length := by
        simp_all
      have hlen_g' : rest_g.length = rest_ss.length := by
        simp_all
      have hrs_f_eq' : (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f) = f.roots :=
        calc (↑(rf2 :: rest_f) : Multiset ℝ) + (rf ::ₘ consumed_f)
            = rf ::ₘ consumed_f + ↑(rf2 :: rest_f) := add_comm _ _
          _ = rf ::ₘ (consumed_f + ↑(rf2 :: rest_f)) := Multiset.cons_add ..
          _ = rf ::ₘ (↑(rf2 :: rest_f) + consumed_f) := by grind
          _ = f.roots := by lia
      have hrs_g_eq' : (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g) = g.roots :=
        calc (↑(rg2 :: rest_g) : Multiset ℝ) + (rg ::ₘ consumed_g)
            = rg ::ₘ consumed_g + ↑(rg2 :: rest_g) := add_comm _ _
          _ = rg ::ₘ (consumed_g + ↑(rg2 :: rest_g)) := Multiset.cons_add ..
          _ = rg ::ₘ (↑(rg2 :: rest_g) + consumed_g) := by grind
          _ = g.roots := by lia
      have hcons_f' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rf2 := by
        grind
      have hcons_g' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rg2 := by
        grind
      have hcons_f2' : ∀ r ∈ rf ::ₘ consumed_f, r ≤ rg2 := by
        grind
      have hcons_g2' : ∀ r ∈ rg ::ₘ consumed_g, r ≤ rf2 := by
        grind
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
        wagner2_roots_exist f g hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hcop
          (rf ::ₘ consumed_f) (rg ::ₘ consumed_g)
          rf2 rg2 rest_f rest_g rest_ss hlen_f' hlen_g'
          hint_f_tail hint_g_tail hrs_f_eq' hrs_g_eq'
          hcons_f' hcons_g' hcons_f2' hcons_g2'
      have hus_ge_s : ∀ w ∈ us, s ≤ w := by
        grind
      obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
        cases us with | nil => simp at hus_len | cons a l => lia
      have hu_le_s : u ≤ s := le_trans huf hrfs
      have hs_le_u1 : s ≤ u1 := hus_ge_s u1 (List.mem_cons_self ..)
      exact ⟨u :: u1 :: us_tail, by simp [hus_len],
        (⟨hu_le_s, hs_le_u1, hus_int⟩ : ListInterlaces (s :: rest_ss) (u :: u1 :: us_tail)),
        fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hu_root') (hus_root v),
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu_lt_s (hus_ge_s w hw), hus_pw⟩,
        fun v hv => (List.mem_cons.mp hv).elim
          (fun h => h ▸ le_trans (min_le_right rf rg) hug)
          (fun h =>
            le_trans (le_trans (min_le_right rf rg) hrgs)
              (le_trans (le_min hsrf2 hsrg2) (hus_lb v h)))⟩
    /- obtain ⟨hrfs, hsrf2, hint_f_tail⟩ := hint_f
    obtain ⟨hrgs, hsrg2, hint_g_tail⟩ := hint_g
    have hrf_root : f.IsRoot rf := (mem_roots hf_ne).mp (by rw [← hrs_f_eq]; simp)
    have hrg_root : g.IsRoot rg := (mem_roots hg_ne).mp (by rw [← hrs_g_eq]; simp)
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
            (mem_roots hf_ne).mp (hrs_f_eq ▸ Multiset.mem_add.mpr (Or.inr hr))
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
            (mem_roots hg_ne).mp (hrs_g_eq ▸ Multiset.mem_add.mpr (Or.inr hr))
          have hrf_s : rf = s := le_antisymm hrfs (h ▸ hcons_g2 r hr)
          have hfr : Polynomial.eval r f = 0 := by rw [h, ← hrf_s]; exact hrf_root
          obtain ⟨p, q, hpq⟩ := hcop
          have h1 := congr_arg (Polynomial.eval r) hpq
          simp [eval_add, eval_mul, eval_one, hfr, hgr] at h1
      rw [hcg, hcf, hcg_cons, hcf_cons, Multiset.coe_card, Multiset.coe_card]
      simp only [List.length_cons] at hlen_f hlen_g ⊢; lia
    -- Sign lemma + IVT
    have hab : min rf rg ≤ s := le_trans (min_le_left rf rg) hrfs
    rcases le_or_gt rf rg with hrfrg | hrfrg
    · have hsign :=
        opposite_sign_at_interlacing_roots hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hab
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
        simp only [List.length_cons] at hlen_f; lia
      have hlen_g' : rest_g.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_g; lia
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
        wagner2_roots_exist f g hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hcop
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
      have hsign :=
          opposite_sign_at_interlacing_roots hg_ne hg_splits hf_ne hf_splits hg_pos hf_pos hab
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
        simp only [List.length_cons] at hlen_f; lia
      have hlen_g' : rest_g.length = rest_ss.length := by
        simp only [List.length_cons] at hlen_g; lia
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
        wagner2_roots_exist f g hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hcop
          (rf ::ₘ consumed_f) (rg ::ₘ consumed_g)
          rf2 rg2 rest_f rest_g rest_ss hlen_f' hlen_g'
          hint_f_tail hint_g_tail hrs_f_eq' hrs_g_eq'
          hcons_f' hcons_g' hcons_f2' hcons_g2' hcount'
      have hus_ge_s : ∀ w ∈ us, s ≤ w :=
        fun w hw => listInterlaces_all_ge us rest_ss s hus_int w hw
      exact ⟨u :: us, by simp [hus_len],
        ⟨le_trans hrgs hug, le_trans huf hrfs, hus_int⟩,
        fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hu_root') (hus_root v),
        List.pairwise_cons.mpr
          ⟨fun w hw => lt_of_lt_of_le hu_lt_s (hus_ge_s w hw), hus_pw⟩⟩ -/
  | _, _, [], _, _ :: _, hlen_f, _, _, _, _, _, _, _, _, _ => by simp at hlen_f
  | _, _, _ :: _, [], _ :: _, _, hlen_g, _, _, _, _, _, _, _, _ => by simp at hlen_g
  | _, _, [], _ :: _, [], hlen_f, _, _, _, _, _, _, _, _, _ => by
    simp_all
  | _, _, _ :: _, [], [], _, hlen_g, _, _, _, _, _, _, _, _ => by
    simp_all
  | _, _, _ :: _, _ :: _, [], hlen_f, _, _, _, _, _, _, _, _, _ => by
    simp_all

/-- Wagner (2): If h precedes both f and g with positive leading coefficients,
    and f, g are coprime, then h precedes their sum. -/
theorem prec_add_of_prec_left {f g h : ℝ[X]}
    (hhf : Prec h f) (hhg : Prec h g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg_rr_ne : (f + g) ≠ 0) (hfg_rr_splits : (f + g).Splits)
    (hcop : IsCoprime f g) :
    Prec h (f + g) := by
  have hfg_rr : (f + g) ≠ 0 ∧ (f + g).Splits := ⟨hfg_rr_ne, hfg_rr_splits⟩
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
        cases rs_f with | nil => simp at hlen_f | cons r rs => lia
      obtain ⟨rg, rest_g, rfl⟩ : ∃ a l, rs_g = a :: l := by
        cases rs_g with | nil => simp at hlen_g | cons r rs => lia
      have hlen_f' : rest_f.length = ss_h.length := by
        simp_all
      have hlen_g' : rest_g.length = ss_h.length := by
        simp_all
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, _⟩ :=
        wagner2_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop 0 0
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
          rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hf.2]
        have hg_deg : (rg :: rest_g).length = g.natDegree := by
          rw [← Multiset.coe_card, hrs_g_eq, card_roots_of_splits hg.2]
        have hdeg_eq : f.natDegree = g.natDegree := by
          lia
        apply le_antisymm
        · have h := natDegree_add_le f g; simp_all
        · apply le_natDegree_of_ne_zero; rw [coeff_add]
          have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
          have hgc : g.coeff f.natDegree = g.leadingCoeff := by
            simp_all
          rw [hfc, hgc]
          exact ne_of_gt (by unfold HasPosLeadingCoeff at hf_pos hg_pos; grind)
      have hfg_natDeg : (f + g).natDegree = us.length := by
        rw [hus_len, hfg_deg]
        have := card_roots_of_splits hf.2
        rw [← hrs_f_eq, Multiset.coe_card] at this
        lia
      have hus_eq : (↑us : Multiset ℝ) = (f + g).roots :=
        Multiset.eq_of_le_of_card_le hus_sub (by
          rw [Multiset.coe_card, card_roots_of_splits hfg_rr.2]; lia)
      exact ⟨hh, hfg_rr, ss_h, us,
        hss_h_sorted, hus_pw.imp le_of_lt, hss_h_eq, hus_eq,
        Or.inl ⟨by lia, hus_int⟩⟩
    · -- f differ-by-1, g same-degree
      cases rs_g with
      | nil =>
        -- g degree 0, h degree 0, f degree 1
        simp only [List.length_nil] at hlen_g_alt
        have hss_nil : ss_h.length = 0 := by lia
        have hrs_nil : ss_h = [] := by simp_all
        subst hrs_nil
        simp only [List.length_nil] at hlen_f
        obtain ⟨rf, rfl⟩ : ∃ a, rs_f = [a] := by
          cases rs_f with
          | nil => lia
          | cons a t =>
            simp_all
        -- f+g has exactly 1 root
        have hfnd : f.natDegree = 1 := by
          have := card_roots_of_splits hf.2
          rw [← hrs_f_eq, Multiset.coe_card] at this
          lia
        have hgnd : g.natDegree = 0 := by
          have := card_roots_of_splits hg.2
          rw [← hrs_g_eq, Multiset.coe_card] at this
          lia
        have hfgnd : (f + g).natDegree = 1 := by
          apply le_antisymm
          · have := natDegree_add_le f g; simp_all
          · rw [← hfnd]; apply le_natDegree_of_ne_zero; rw [coeff_add]
            have : g.coeff f.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
            rw [this, add_zero]; exact ne_of_gt hf_pos
        have hcard1 : (f + g).roots.card = 1 := by
          rw [card_roots_of_splits hfg_rr.2, hfgnd]
        obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (by lia : 0 < (f + g).roots.card)
        have hfg_eq : (↑[u] : Multiset ℝ) = (f + g).roots := by
          apply Multiset.eq_of_le_of_card_le
          · simp_all
          · simp [hcard1]
        exact ⟨hh, hfg_rr, [], [u], List.Pairwise.nil, List.pairwise_singleton _ _,
          hss_h_eq, hfg_eq, Or.inl ⟨by simp, trivial⟩⟩
      | cons r₁_g rest_g =>
        obtain ⟨s₁, rest_ss, rfl⟩ : ∃ a l, ss_h = a :: l := by
          cases ss_h with
          | nil => simp_all
          | cons s rest => lia
        obtain ⟨rf, rf2, rest_f', rfl⟩ : ∃ a b l, rs_f = a :: b :: l := by
          rcases rs_f with _ | ⟨a, _ | ⟨b, l⟩⟩
          · simp_all
          · simp_all
          · lia
        obtain ⟨hs₁_r₁g, hint_g_tail⟩ := halt_g
        obtain ⟨hrfs₁, hs₁rf2, hint_f_tail⟩ := hint_f
        have hrf_root : f.IsRoot rf :=
          (mem_roots hf.1).mp (by rw [← hrs_f_eq]; simp)
        have hr₁g_root : g.IsRoot r₁_g :=
          (mem_roots hg.1).mp (by rw [← hrs_g_eq]; simp)
        -- Degrees
        have hf_deg : (rf :: rf2 :: rest_f').length = f.natDegree := by
          rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hf.2]
        have hg_deg : (r₁_g :: rest_g).length = g.natDegree := by
          rw [← Multiset.coe_card, hrs_g_eq, card_roots_of_splits hg.2]
        have hdeg : g.natDegree + 1 = f.natDegree := by
          lia
        have hdeg_lt : g.natDegree < f.natDegree := by lia
        have hfg_deg : (f + g).natDegree = f.natDegree :=
          natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hf_pos
        have hfg_pos : HasPosLeadingCoeff (f + g) :=
          hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg_lt hf_pos
        -- All g-roots > rf (coprimality)
        have hg_gt_rf : ∀ t ∈ g.roots, rf < t := by
          intro t ht; rw [← hrs_g_eq] at ht
          have ht_ge : s₁ ≤ t := by
            rcases Multiset.mem_coe.mp ht with ht'
            rcases List.mem_cons.mp ht' with rfl | ht''
            · lia
            · exact le_trans hs₁_r₁g
                (listInterlaces_rs_all_ge rest_ss rest_g r₁_g hint_g_tail t ht'')
          rcases lt_or_eq_of_le (le_trans hrfs₁ ht_ge) with h | h
          · lia
          · exfalso
            have hft : Polynomial.eval t f = 0 :=
              (mem_roots hf.1).mp
                (hrs_f_eq ▸ Multiset.mem_coe.mpr
                  (by simp_all))
            have hgt : Polynomial.eval t g = 0 := (mem_roots hg.1).mp (hrs_g_eq ▸ ht)
            obtain ⟨p, q, hpq⟩ := hcop
            have := congr_arg (Polynomial.eval t) hpq
            simp [eval_add, eval_mul, eval_one, hft, hgt] at this
        obtain ⟨u₀, hu₀_le, hu₀_root_gf⟩ :=
          exists_root_le_of_mixed hg.1 hg_pos
            (by rw [show g + f = f + g from add_comm g f]; lia)
            hrf_root hg_gt_rf (by
              rw [show g + f = f + g from add_comm g f, hfg_deg, hdeg])
        have hu₀_root : (f + g).IsRoot u₀ := by rwa [add_comm] at hu₀_root_gf
        -- Use wagner2_roots_exist on rf2 :: rest_f' and r₁_g :: rest_g with rest_ss
        have hlen_f' : rest_f'.length = rest_ss.length := by
          grind
        have hlen_g' : rest_g.length = rest_ss.length := by
          grind
        have hrs_f_eq' : (↑(rf2 :: rest_f') : Multiset ℝ) + ↑[rf] = f.roots := by
          rw [← hrs_f_eq, Multiset.coe_add]
          exact Multiset.coe_eq_coe.mpr List.perm_append_comm
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
          wagner2_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop ↑[rf] 0
            rf2 r₁_g rest_f' rest_g rest_ss hlen_f' hlen_g'
            hint_f_tail hint_g_tail hrs_f_eq' (by simp [hrs_g_eq])
            (by
               simp_all)
            (by simp)
            (by
               intro r hr
               simp only [Multiset.coe_singleton, Multiset.mem_singleton] at hr
               grind)
            (by simp)
        -- u₀ < s₁ (coprimality)
        have hu₀_lt_s₁ : u₀ < s₁ := by
          rcases lt_or_eq_of_le (le_trans hu₀_le hrfs₁) with h | h
          · lia
          · exfalso
            have hrf_s₁ : rf = s₁ := le_antisymm hrfs₁ (h ▸ hu₀_le)
            have hfs₁ : Polynomial.eval s₁ f = 0 := by simp_all
            have hgs₁ : Polynomial.eval s₁ g = 0 := by
              simp_all
            obtain ⟨p, q, hpq⟩ := hcop
            have := congr_arg (Polynomial.eval s₁) hpq
            simp [eval_add, eval_mul, eval_one, hfs₁, hgs₁] at this
        -- us elements ≥ min(rf2, r₁_g) ≥ s₁
        have hus_ge_s₁ : ∀ w ∈ us, s₁ ≤ w := by
          grind
        obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
          cases us with | nil => simp at hus_len | cons a l => lia
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
            have h1 := card_roots_of_splits hfg_rr.2
            simp_all)
        exact ⟨hh, hfg_rr, s₁ :: rest_ss, u₀ :: u1 :: us_tail,
          hss_h_sorted, (List.pairwise_cons.mpr ⟨fun w hw =>
            lt_of_lt_of_le hu₀_lt_s₁ (hus_ge_s₁ w hw), hus_pw⟩).imp le_of_lt,
          hss_h_eq, hroots_eq,
          Or.inl ⟨by simp_all,
            ⟨le_trans hu₀_le hrfs₁,
              hus_ge_s₁ u1 (List.mem_cons_self ..), hus_int⟩⟩⟩
  · -- f same-degree
    rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · -- f same-degree, g differ-by-1 (symmetric to f differ-by-1, g same-degree above)
      cases rs_f with
      | nil =>
        -- f degree 0, h degree 0, g degree 1
        simp only [List.length_nil] at hlen_f_alt
        have hss_nil : ss_h.length = 0 := by lia
        have hrs_nil : ss_h = [] := by simp_all
        subst hrs_nil
        simp only [List.length_nil] at hlen_g
        obtain ⟨rg, rfl⟩ : ∃ a, rs_g = [a] := by
          cases rs_g with
          | nil => lia
          | cons a t =>
            simp_all
        have hfnd : f.natDegree = 0 := by
          have := card_roots_of_splits hf.2
          rw [← hrs_f_eq, Multiset.coe_card] at this
          lia
        have hgnd : g.natDegree = 1 := by
          have := card_roots_of_splits hg.2
          rw [← hrs_g_eq, Multiset.coe_card] at this
          lia
        have hfgnd : (f + g).natDegree = 1 := by
          apply le_antisymm
          · have := natDegree_add_le f g; simp_all
          · rw [← hgnd]; apply le_natDegree_of_ne_zero; rw [coeff_add]
            have : f.coeff g.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
            rw [this, zero_add]; exact ne_of_gt hg_pos
        have hcard1 : (f + g).roots.card = 1 := by
          rw [card_roots_of_splits hfg_rr.2, hfgnd]
        obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (by lia : 0 < (f + g).roots.card)
        have hfg_eq : (↑[u] : Multiset ℝ) = (f + g).roots := by
          apply Multiset.eq_of_le_of_card_le
          · simp_all
          · simp [hcard1]
        exact ⟨hh, hfg_rr, [], [u], List.Pairwise.nil, List.pairwise_singleton _ _,
          hss_h_eq, hfg_eq, Or.inl ⟨by simp, trivial⟩⟩
      | cons r₁_f rest_f =>
        -- Main case: f same-degree, g differ-by-1
        obtain ⟨s₁, rest_ss, rfl⟩ : ∃ a l, ss_h = a :: l := by
          cases ss_h with
          | nil => simp_all
          | cons s rest => lia
        obtain ⟨rg, rg2, rest_g', rfl⟩ : ∃ a b l, rs_g = a :: b :: l := by
          rcases rs_g with _ | ⟨a, _ | ⟨b, l⟩⟩
          · simp_all
          · simp_all
          · lia
        obtain ⟨hs₁_r₁f, hint_f_tail⟩ := halt_f
        obtain ⟨hrgs₁, hs₁rg2, hint_g_tail⟩ := hint_g
        have hr₁f_root : f.IsRoot r₁_f :=
          (mem_roots hf.1).mp (by rw [← hrs_f_eq]; simp)
        have hrg_root : g.IsRoot rg :=
          (mem_roots hg.1).mp (by rw [← hrs_g_eq]; simp)
        -- Degrees
        have hf_deg : (r₁_f :: rest_f).length = f.natDegree := by
          rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hf.2]
        have hg_deg : (rg :: rg2 :: rest_g').length = g.natDegree := by
          rw [← Multiset.coe_card, hrs_g_eq, card_roots_of_splits hg.2]
        have hdeg : f.natDegree + 1 = g.natDegree := by
          lia
        have hdeg_lt : f.natDegree < g.natDegree := by lia
        have hfg_deg : (f + g).natDegree = g.natDegree :=
          natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hg_pos
        have hfg_pos : HasPosLeadingCoeff (f + g) :=
          hasPosLeadingCoeff_add_of_natDegree_lt_right hdeg_lt hg_pos
        -- All f-roots > rg (coprimality)
        have hf_gt_rg : ∀ t ∈ f.roots, rg < t := by
          intro t ht; rw [← hrs_f_eq] at ht
          have ht_ge : s₁ ≤ t := by
            rcases Multiset.mem_coe.mp ht with ht'
            rcases List.mem_cons.mp ht' with rfl | ht''
            · lia
            · exact le_trans hs₁_r₁f
                (listInterlaces_rs_all_ge rest_ss rest_f r₁_f hint_f_tail t ht'')
          rcases lt_or_eq_of_le (le_trans hrgs₁ ht_ge) with h | h
          · lia
          · exfalso
            have hgt : Polynomial.eval t g = 0 :=
              (mem_roots hg.1).mp (hrs_g_eq ▸ Multiset.mem_coe.mpr
                (by simp_all))
            have hft : Polynomial.eval t f = 0 :=
              (mem_roots hf.1).mp (hrs_f_eq ▸ ht)
            obtain ⟨p, q, hpq⟩ := hcop
            have := congr_arg (Polynomial.eval t) hpq
            simp [eval_add, eval_mul, eval_one, hft, hgt] at this
        obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
          exists_root_le_of_mixed hf.1 hf_pos hfg_pos hrg_root hf_gt_rg (by
            lia)
        -- Use wagner2_roots_exist on r₁_f :: rest_f and rg2 :: rest_g' with rest_ss
        have hlen_f' : rest_f.length = rest_ss.length := by
          grind
        have hlen_g' : rest_g'.length = rest_ss.length := by
          grind
        have hrs_g_eq' : (↑(rg2 :: rest_g') : Multiset ℝ) + ↑[rg] = g.roots := by
          rw [← hrs_g_eq, Multiset.coe_add]
          exact Multiset.coe_eq_coe.mpr List.perm_append_comm
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
          wagner2_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop 0 ↑[rg]
            r₁_f rg2 rest_f rest_g' rest_ss hlen_f' hlen_g'
            hint_f_tail hint_g_tail (by simp [hrs_f_eq]) hrs_g_eq'
            (by simp)
            (by
               simp_all)
            (by simp)
            (by
               intro r hr
               simp only [Multiset.coe_singleton, Multiset.mem_singleton] at hr
               grind)
        -- u₀ < s₁ (coprimality)
        have hu₀_lt_s₁ : u₀ < s₁ := by
          rcases lt_or_eq_of_le (le_trans hu₀_le hrgs₁) with h | h
          · lia
          · exfalso
            have hrg_s₁ : rg = s₁ := le_antisymm hrgs₁ (h ▸ hu₀_le)
            have hgs₁ : Polynomial.eval s₁ g = 0 := by simp_all
            have hfs₁ : Polynomial.eval s₁ f = 0 := by
              simp_all
            obtain ⟨p, q, hpq⟩ := hcop
            have := congr_arg (Polynomial.eval s₁) hpq
            simp [eval_add, eval_mul, eval_one, hfs₁, hgs₁] at this
        -- us elements ≥ min(r₁_f, rg2) ≥ s₁
        have hus_ge_s₁ : ∀ w ∈ us, s₁ ≤ w := by
          grind
        obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
          cases us with | nil => simp at hus_len | cons a l => lia
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
            have h1 := card_roots_of_splits hfg_rr.2
            simp_all)
        exact ⟨hh, hfg_rr, s₁ :: rest_ss, u₀ :: u1 :: us_tail,
          hss_h_sorted, (List.pairwise_cons.mpr ⟨fun w hw =>
            lt_of_lt_of_le hu₀_lt_s₁ (hus_ge_s₁ w hw), hus_pw⟩).imp le_of_lt,
          hss_h_eq, hroots_eq,
          Or.inl ⟨by simp_all,
            ⟨le_trans hu₀_le hrgs₁,
              hus_ge_s₁ u1 (List.mem_cons_self ..), hus_int⟩⟩⟩
    · -- f same-degree, g same-degree
      cases ss_h with
      | nil =>
        -- Degenerate: all degree 0
        simp only [List.length_nil] at hlen_f_alt hlen_g_alt
        have hrf_nil : rs_f = [] := by
          grind
        have hrg_nil : rs_g = [] := by
          grind
        subst hrf_nil; subst hrg_nil
        have hfnd : f.natDegree = 0 := by
          have := card_roots_of_splits hf.2
          rw [← hrs_f_eq, Multiset.coe_card] at this
          lia
        have hgnd : g.natDegree = 0 := by
          have := card_roots_of_splits hg.2
          rw [← hrs_g_eq, Multiset.coe_card] at this
          lia
        have hfgnd : (f + g).natDegree = 0 := by grind [natDegree_add_le f g]
        have hfg_roots_eq : (↑([] : List ℝ) : Multiset ℝ) = (f + g).roots := by
          have h := card_roots_of_splits hfg_rr.2
          rw [hfgnd] at h
          exact (Multiset.card_eq_zero.mp h).symm
        exact ⟨hh, hfg_rr, [], [], List.Pairwise.nil, List.Pairwise.nil,
          hss_h_eq, hfg_roots_eq, Or.inr ⟨rfl, trivial⟩⟩
      | cons s₁ rest_ss =>
        -- Non-degenerate: both same-degree
        obtain ⟨r₁_f, rest_f, rfl⟩ : ∃ a l, rs_f = a :: l := by
          cases rs_f with
          | nil => grind
          | cons a l => lia
        obtain ⟨r₁_g, rest_g, rfl⟩ : ∃ a l, rs_g = a :: l := by
          cases rs_g with
          | nil => simp_all
          | cons a l => lia
        obtain ⟨hs₁_r₁f, hint_f_tail⟩ := halt_f
        obtain ⟨hs₁_r₁g, hint_g_tail⟩ := halt_g
        have hlen_f' : rest_f.length = rest_ss.length := by
          simp_all
        have hlen_g' : rest_g.length = rest_ss.length := by
          simp_all
        -- Degrees
        have hf_deg : (r₁_f :: rest_f).length = f.natDegree := by
          rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hf.2]
        have hg_deg : (r₁_g :: rest_g).length = g.natDegree := by
          rw [← Multiset.coe_card, hrs_g_eq, card_roots_of_splits hg.2]
        have hdeg_eq : f.natDegree = g.natDegree := by
          lia
        have hfg_deg : (f + g).natDegree = f.natDegree := by
          apply le_antisymm
          · have h := natDegree_add_le f g; simp_all
          · apply le_natDegree_of_ne_zero; rw [coeff_add]
            have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
            have hgc : g.coeff f.natDegree = g.leadingCoeff := by
              simp_all
            rw [hfc, hgc]
            exact ne_of_gt (by unfold HasPosLeadingCoeff at hf_pos hg_pos; grind)
        -- Call wagner2_roots_exist with empty consumed sets
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw, hus_lb⟩ :=
          wagner2_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop 0 0
            r₁_f r₁_g rest_f rest_g rest_ss hlen_f' hlen_g'
            hint_f_tail hint_g_tail (by simp [hrs_f_eq]) (by simp [hrs_g_eq])
            (by simp) (by simp) (by simp) (by simp)
        -- us exhausts roots of f+g
        have hus_nodup : us.Nodup := hus_pw.imp ne_of_lt
        have hus_sub : (↑us : Multiset ℝ) ≤ (f + g).roots := by
          rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
          intro u hu
          simp_all
        have hus_eq : (↑us : Multiset ℝ) = (f + g).roots :=
          Multiset.eq_of_le_of_card_le hus_sub (by
            rw [Multiset.coe_card, card_roots_of_splits hfg_rr.2, hfg_deg]
            simp_all)
        -- Extract head of us for ListAlternates
        obtain ⟨u1, us_tail, rfl⟩ : ∃ a l, us = a :: l := by
          cases us with | nil => simp at hus_len | cons a l => lia
        have hs₁_u1 : s₁ ≤ u1 :=
          le_trans (le_min hs₁_r₁f hs₁_r₁g) (hus_lb u1 (List.mem_cons_self ..))
        exact ⟨hh, hfg_rr, s₁ :: rest_ss, u1 :: us_tail,
          hss_h_sorted, hus_pw.imp le_of_lt, hss_h_eq, hus_eq,
          Or.inr ⟨by simp_all,
                   ⟨hs₁_u1, hus_int⟩⟩⟩

/-- A common-factor version of Wagner (2). If `h', f', g'` satisfy the
left-hand addition theorem, then multiplying the whole picture by a common
real-rooted factor preserves the conclusion. -/
theorem prec_add_of_prec_left_of_common_factor {d f g h : ℝ[X]}
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    {f' g' h' : ℝ[X]}
    (hf_def : f = d * f') (hg_def : g = d * g') (hh_def : h = d * h')
    (hhf : Prec h' f') (hhg : Prec h' g')
    (hf'_pos : HasPosLeadingCoeff f') (hg'_pos : HasPosLeadingCoeff g')
    (hfg'_rr_ne : (f' + g') ≠ 0) (hfg'_rr_splits : (f' + g').Splits)
    (hcop : IsCoprime f' g') :
    Prec h (f + g) := by
  subst hf_def hg_def hh_def
  have hsum : Prec h' (f' + g') :=
    prec_add_of_prec_left hhf hhg hf'_pos hg'_pos hfg'_rr_ne hfg'_rr_splits hcop
  have hmul : Prec (d * h') (d * (f' + g')) := prec_mul_common_factor hd_ne hd_splits hsum
  simpa [left_distrib, right_distrib, mul_add, add_comm, add_left_comm, add_assoc] using hmul

/-- Recursive compatibility data for iterating Wagner (2) along a nonempty
list. Each new head term must precede the same left bound, have positive
leading coefficient, and satisfy the Wagner-2 compatibility hypotheses with the
sum of the already-compatible tail. -/
inductive SumCompatibleLeft (h : ℝ[X]) : List ℝ[X] → Prop
  | singleton {p : ℝ[X]}
      (hprec : Prec h p) (hpos : HasPosLeadingCoeff p) :
      SumCompatibleLeft h [p]
  | cons {p : ℝ[X]} {l : List ℝ[X]}
      (hprec : Prec h p) (hpos : HasPosLeadingCoeff p)
      (hl : SumCompatibleLeft h l)
      (hrr_ne : (p + l.sum) ≠ 0) (hrr_splits : (p + l.sum).Splits)
      (hcop : IsCoprime p l.sum) :
      SumCompatibleLeft h (p :: l)

namespace SumCompatibleLeft

lemma hasPosLeadingCoeff_sum {h : ℝ[X]} :
    ∀ {l : List ℝ[X]}, SumCompatibleLeft h l → HasPosLeadingCoeff l.sum
  | _, singleton _ hpos => by
      simp_all
  | _, @cons _ p l _ hpos hl _ _ _ => by
      have htail_pos : HasPosLeadingCoeff l.sum := hasPosLeadingCoeff_sum hl
      rcases lt_trichotomy p.natDegree l.sum.natDegree with hlt | heq | hgt
      · simpa using hasPosLeadingCoeff_add_of_natDegree_lt_right hlt htail_pos
      · simpa [List.sum_cons] using hasPosLeadingCoeff_add_of_same_natDegree heq hpos htail_pos
      · simpa using hasPosLeadingCoeff_add_of_natDegree_lt_left hgt hpos

lemma prec_sum {h : ℝ[X]} :
    ∀ {l : List ℝ[X]}, SumCompatibleLeft h l → Prec h l.sum
  | _, singleton hprec _ => by
      simp_all
  | _, @cons _ p l hprec hpos hl hrr_ne hrr_splits hcop =>
      prec_add_of_prec_left hprec (prec_sum hl)
        hpos (hasPosLeadingCoeff_sum hl) hrr_ne hrr_splits hcop

end SumCompatibleLeft

/-- Recursive Wagner (2): a nonempty list of pairwise-compatible summands,
assembled one term at a time from the left, is interlaced by the common left
bound. -/
theorem prec_sum_of_compatible_left {h : ℝ[X]} {l : List ℝ[X]}
    (hl : SumCompatibleLeft h l) :
    Prec h l.sum :=
  hl.prec_sum

end
end RealRooted
