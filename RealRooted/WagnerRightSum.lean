import RealRooted.WagnerRightSum.Sign

/-!
# Wagner (1): Common-right addition theorems

If f ≪ h and g ≪ h with positive leading coefficients, then (f + g) ≪ h.
Generalizes to n summands by induction.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted

section

/-- Core of Wagner (1): given interlacing lists ss_f, ss_g into rs (differ-by-1),
    there exist roots us of f+g with ListInterlaces us rs.
    The `consumed_f/consumed_g` multisets track roots already processed in prior
    intervals; they satisfy `↑ss_f + consumed = f.roots` and are all `≤ rs.head`. -/
private lemma wagner1_roots_exist (f g : ℝ[X])
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hcop : IsCoprime f g)
    (consumed_f consumed_g : Multiset ℝ) :
    ∀ (ss_f ss_g rs : List ℝ),
    ss_f.length + 1 = rs.length →
    ss_g.length + 1 = rs.length →
    ListInterlaces ss_f rs →
    ListInterlaces ss_g rs →
    (↑ss_f : Multiset ℝ) + consumed_f = f.roots →
    (↑ss_g : Multiset ℝ) + consumed_g = g.roots →
    (∀ r ∈ consumed_f, r ≤ rs.head!) →
    (∀ r ∈ consumed_g, r ≤ rs.head!) →
    ∃ us : List ℝ, us.length = ss_f.length ∧ ListInterlaces us rs ∧
      (∀ u ∈ us, (f + g).IsRoot u) ∧ us.Pairwise (· < ·)
  | [], [], [_], _, _, _, _, _, _, _, _ => by
      grind
  | sf :: rest_f, sg :: rest_g, a :: b :: rest_rs,
    hlen_f, hlen_g, hint_f, hint_g, hss_f_eq, hss_g_eq,
    hcons_f, hcons_g => by
    -- Extract bounds on sf and sg from interlacing
    obtain ⟨hasf, hsfb, hint_f_tail⟩ := hint_f
    obtain ⟨hasg, hsgb, hint_g_tail⟩ := hint_g
    have hab : a ≤ b := le_trans hasf hsfb
    -- Erase sf from f.roots: f.roots = {sf} + ↑rest_f + consumed_f
    have hf_roots_erase : f.roots.erase sf = ↑rest_f + consumed_f := by
      have h := hss_f_eq.symm
      rw [← Multiset.cons_coe] at h
      rw [Multiset.cons_add] at h
      simp_all
    have hg_roots_erase : g.roots.erase sg = ↑rest_g + consumed_g := by
      have h := hss_g_eq.symm
      rw [← Multiset.cons_coe] at h
      rw [Multiset.cons_add] at h
      simp_all
    -- Consumed roots are ≤ a (from hypothesis, since rs.head! = a)
    have hcons_f_le : ∀ r ∈ consumed_f, r ≤ a := hcons_f
    have hcons_g_le : ∀ r ∈ consumed_g, r ≤ a := hcons_g
    -- sf is a root of f, sg is a root of g
    have hsf_root : f.IsRoot sf := by
      have : sf ∈ f.roots := by rw [← hss_f_eq]; simp [Multiset.mem_add]
      simp_all
    have hsg_root : g.IsRoot sg := by
      have : sg ∈ g.roots := by rw [← hss_g_eq]; simp [Multiset.mem_add]
      simp_all
    -- Shared recursive call arguments
    have hlen_f' : rest_f.length + 1 = (b :: rest_rs).length := by grind
    have hlen_g' : rest_g.length + 1 = (b :: rest_rs).length := by grind
    have hss_f_eq' : (↑rest_f : Multiset ℝ) + (sf ::ₘ consumed_f) = f.roots :=
      calc (↑rest_f : Multiset ℝ) + (sf ::ₘ consumed_f)
          = sf ::ₘ consumed_f + ↑rest_f := add_comm _ _
        _ = sf ::ₘ (consumed_f + ↑rest_f) := Multiset.cons_add ..
        _ = sf ::ₘ (↑rest_f + consumed_f) := by grind
        _ = sf ::ₘ ↑rest_f + consumed_f := (Multiset.cons_add ..).symm
        _ = (↑(sf :: rest_f) : Multiset ℝ) + consumed_f := by simp
        _ = f.roots := hss_f_eq
    have hss_g_eq' : (↑rest_g : Multiset ℝ) + (sg ::ₘ consumed_g) = g.roots :=
      calc (↑rest_g : Multiset ℝ) + (sg ::ₘ consumed_g)
          = sg ::ₘ consumed_g + ↑rest_g := add_comm _ _
        _ = sg ::ₘ (consumed_g + ↑rest_g) := Multiset.cons_add ..
        _ = sg ::ₘ (↑rest_g + consumed_g) := by grind
        _ = sg ::ₘ ↑rest_g + consumed_g := (Multiset.cons_add ..).symm
        _ = (↑(sg :: rest_g) : Multiset ℝ) + consumed_g := by simp
        _ = g.roots := hss_g_eq
    have hcons_f' : ∀ r ∈ (sf ::ₘ consumed_f), r ≤ b := by grind
    have hcons_g' : ∀ r ∈ (sg ::ₘ consumed_g), r ≤ b := by grind
    -- Case split: a = b (trivial root) vs a < b (sign lemma)
    rcases eq_or_lt_of_le hab with hab_eq | hab_lt
    · -- a = b: sf = sg = a, but then f(a) = 0 = g(a), contradicting IsCoprime f g
      have hsf_eq : sf = a := le_antisymm (hab_eq.symm ▸ hsfb) hasf
      have hsg_eq : sg = a := le_antisymm (hab_eq.symm ▸ hsgb) hasg
      exfalso
      have hfa : f.eval a = 0 := by simp_all
      have hga : g.eval a = 0 := by simp_all
      obtain ⟨p, q, hpq⟩ := hcop
      have h1 := congr_arg (Polynomial.eval a) hpq
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hfa, hga] at h1
    · -- a < b: consumed roots are all < b, so countP (b ≤ ·) = 0
      have hf_dichotomy : ∀ r ∈ f.roots.erase sf, r ≤ a ∨ b ≤ r := by
        rw [hf_roots_erase]; intro r hr
        rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
        · right; exact listInterlaces_all_ge rest_f rest_rs b hint_f_tail r
              (Multiset.mem_coe.mp hr_rest)
        · grind
      have hg_dichotomy : ∀ r ∈ g.roots.erase sg, r ≤ a ∨ b ≤ r := by
        rw [hg_roots_erase]; intro r hr
        rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
        · right; exact listInterlaces_all_ge rest_g rest_rs b hint_g_tail r
              (Multiset.mem_coe.mp hr_rest)
        · grind
      have hcount_eq :
          (g.roots.erase sg).countP (b ≤ ·) = (f.roots.erase sf).countP (b ≤ ·) := by
        rw [hf_roots_erase, hg_roots_erase, Multiset.countP_add, Multiset.countP_add]
        have hcf_rest := Multiset.countP_eq_card.mpr (fun r hr =>
          listInterlaces_all_ge rest_f rest_rs b hint_f_tail r (Multiset.mem_coe.mp hr))
        have hcg_rest := Multiset.countP_eq_card.mpr (fun r hr =>
          listInterlaces_all_ge rest_g rest_rs b hint_g_tail r (Multiset.mem_coe.mp hr))
        have hcf_cons : consumed_f.countP (b ≤ ·) = 0 :=
          Multiset.countP_eq_zero.mpr (fun r hr => not_le.mpr
            (lt_of_le_of_lt (hcons_f_le r hr) hab_lt))
        have hcg_cons : consumed_g.countP (b ≤ ·) = 0 :=
          Multiset.countP_eq_zero.mpr (fun r hr => not_le.mpr
            (lt_of_le_of_lt (hcons_g_le r hr) hab_lt))
        simp_all
      -- Sign lemma + IVT
      rcases le_or_gt sf sg with hsfsg | hsfsg
      · have hsign :=
          opposite_sign_at_interlacing_roots hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos
          hasf hsfb hasg hsgb hsf_root hsg_root hf_dichotomy hg_dichotomy hcount_eq
        obtain ⟨u, huf, hub, hufg⟩ := sum_has_root_between hsfsg hsf_root hsg_root hsign
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
          wagner1_roots_exist f g hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hcop
            (sf ::ₘ consumed_f) (sg ::ₘ consumed_g)
            rest_f rest_g (b :: rest_rs) hlen_f' hlen_g' hint_f_tail hint_g_tail
            hss_f_eq' hss_g_eq' hcons_f' hcons_g'
        -- Under IsCoprime, u < b: if u = b then sg = b, forcing g(b) = f(b) = 0
        have hu_lt_b : u < b := by
          rcases lt_or_eq_of_le (le_trans hub hsgb) with h | h
          · lia
          · exfalso
            -- h : u = b
            have hsg_b : sg = b := le_antisymm hsgb (h ▸ hub)
            have hgb : g.eval b = 0 := by simp_all
            have hfb : f.eval b = 0 := by simp_all
            obtain ⟨p, q, hpq⟩ := hcop
            have h1 := congr_arg (Polynomial.eval b) hpq
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
                  hfb, hgb] at h1
        -- u < b ≤ every element of us (from interlacing), so u :: us is strictly sorted
        have hus_pw' : (u :: us).Pairwise (· < ·) :=
          List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu_lt_b
              (listInterlaces_all_ge us rest_rs b hus_int w hw), hus_pw⟩
        exact ⟨u :: us, by simp [hus_len],
          ⟨le_trans hasf huf, le_trans hub hsgb, hus_int⟩,
          fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hufg) (hus_root v),
          hus_pw'⟩
      · have hsgf := le_of_lt hsfsg
        have hsign :=
          opposite_sign_at_interlacing_roots hg_ne hg_splits hf_ne hf_splits hg_pos hf_pos
          hasg hsgb hasf hsfb hsg_root hsf_root hg_dichotomy hf_dichotomy
          (hcount_eq.symm)
        obtain ⟨u, hug, huf, hufg⟩ := sum_has_root_between hsgf hsg_root hsf_root
          (by lia)
        have hufg' : (f + g).IsRoot u := by rwa [add_comm]
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
          wagner1_roots_exist f g hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos hcop
            (sf ::ₘ consumed_f) (sg ::ₘ consumed_g)
            rest_f rest_g (b :: rest_rs) hlen_f' hlen_g' hint_f_tail hint_g_tail
            hss_f_eq' hss_g_eq' hcons_f' hcons_g'
        -- Under IsCoprime, u < b: if u = b then sf = b, forcing f(b) = g(b) = 0
        have hu_lt_b : u < b := by
          rcases lt_or_eq_of_le (le_trans huf hsfb) with h | h
          · lia
          · exfalso
            -- h : u = b
            have hsf_b : sf = b := le_antisymm hsfb (h ▸ huf)
            have hfb : f.eval b = 0 := by simp_all
            have hgb : g.eval b = 0 := by simp_all
            obtain ⟨p, q, hpq⟩ := hcop
            have h1 := congr_arg (Polynomial.eval b) hpq
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
                  hfb, hgb] at h1
        -- u < b ≤ every element of us (from interlacing), so u :: us is strictly sorted
        have hus_pw' : (u :: us).Pairwise (· < ·) :=
          List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu_lt_b
              (listInterlaces_all_ge us rest_rs b hus_int w hw), hus_pw⟩
        exact ⟨u :: us, by simp [hus_len],
          ⟨le_trans hasg hug, le_trans huf hsfb, hus_int⟩,
          fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hufg') (hus_root v),
          hus_pw'⟩
  -- All remaining arms are impossible: contradictory length hypotheses.
  | [], [], [], hlen_f, _, _, _, _, _, _, _ => by
      lia
  | [], [], _ :: _ :: _, hlen_f, _, _, _, _, _, _, _ => by
      grind
  | [], _ :: _, _, hlen_f, hlen_g, _, _, _, _, _, _ => by
      grind
  | _ :: _, [], _, hlen_f, hlen_g, _, _, _, _, _, _ => by
      grind
  | _ :: _, _ :: _, [], hlen_f, _, _, _, _, _, _, _ => by
      grind
  | _ :: _, _ :: _, [_], hlen_f, _, _, _, _, _, _, _ => by
      grind

/-- A sign-based version of the Wagner (1) root-production helper: if the
    common right-hand roots are not roots of `f + g`, then we can produce the
    strict interlacing roots of `f + g` without assuming `f` and `g` are
    coprime. This is the more human-style hypothesis actually used in the
    interval argument. -/
private lemma wagner1_roots_exist_of_no_common_right (f g : ℝ[X])
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (consumed_f consumed_g : Multiset ℝ) :
    ∀ (ss_f ss_g rs : List ℝ),
    ss_f.length + 1 = rs.length →
    ss_g.length + 1 = rs.length →
    ListInterlaces ss_f rs →
    ListInterlaces ss_g rs →
    (↑ss_f : Multiset ℝ) + consumed_f = f.roots →
    (↑ss_g : Multiset ℝ) + consumed_g = g.roots →
    (∀ r ∈ consumed_f, r ≤ rs.head!) →
    (∀ r ∈ consumed_g, r ≤ rs.head!) →
    (∀ r ∈ rs, ¬ (f + g).IsRoot r) →
    ∃ us : List ℝ, us.length = ss_f.length ∧ ListInterlaces us rs ∧
      (∀ u ∈ us, (f + g).IsRoot u) ∧ us.Pairwise (· < ·)
  | [], [], [_], _, _, _, _, _, _, _, _, _ => by
      grind
  | sf :: rest_f, sg :: rest_g, a :: b :: rest_rs,
    hlen_f, hlen_g, hint_f, hint_g, hss_f_eq, hss_g_eq,
    hcons_f, hcons_g, hno_rs => by
      obtain ⟨hasf, hsfb, hint_f_tail⟩ := hint_f
      obtain ⟨hasg, hsgb, hint_g_tail⟩ := hint_g
      have hab : a ≤ b := le_trans hasf hsfb
      have hf_roots_erase : f.roots.erase sf = ↑rest_f + consumed_f := by
        have h := hss_f_eq.symm
        rw [← Multiset.cons_coe] at h
        rw [Multiset.cons_add] at h
        simp_all
      have hg_roots_erase : g.roots.erase sg = ↑rest_g + consumed_g := by
        have h := hss_g_eq.symm
        rw [← Multiset.cons_coe] at h
        rw [Multiset.cons_add] at h
        simp_all
      have hcons_f_le : ∀ r ∈ consumed_f, r ≤ a := hcons_f
      have hcons_g_le : ∀ r ∈ consumed_g, r ≤ a := hcons_g
      have hsf_root : f.IsRoot sf := by
        have : sf ∈ f.roots := by
          rw [← hss_f_eq]
          simp [Multiset.mem_add]
        simp_all
      have hsg_root : g.IsRoot sg := by
        have : sg ∈ g.roots := by
          rw [← hss_g_eq]
          simp [Multiset.mem_add]
        simp_all
      have hlen_f' : rest_f.length + 1 = (b :: rest_rs).length := by grind
      have hlen_g' : rest_g.length + 1 = (b :: rest_rs).length := by grind
      have hss_f_eq' : (↑rest_f : Multiset ℝ) + (sf ::ₘ consumed_f) = f.roots :=
        calc
          (↑rest_f : Multiset ℝ) + (sf ::ₘ consumed_f)
              = sf ::ₘ consumed_f + ↑rest_f := add_comm _ _
          _ = sf ::ₘ (consumed_f + ↑rest_f) := Multiset.cons_add ..
          _ = sf ::ₘ (↑rest_f + consumed_f) := by grind
          _ = sf ::ₘ ↑rest_f + consumed_f := (Multiset.cons_add ..).symm
          _ = (↑(sf :: rest_f) : Multiset ℝ) + consumed_f := by simp
          _ = f.roots := hss_f_eq
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + (sg ::ₘ consumed_g) = g.roots :=
        calc
          (↑rest_g : Multiset ℝ) + (sg ::ₘ consumed_g)
              = sg ::ₘ consumed_g + ↑rest_g := add_comm _ _
          _ = sg ::ₘ (consumed_g + ↑rest_g) := Multiset.cons_add ..
          _ = sg ::ₘ (↑rest_g + consumed_g) := by grind
          _ = sg ::ₘ ↑rest_g + consumed_g := (Multiset.cons_add ..).symm
          _ = (↑(sg :: rest_g) : Multiset ℝ) + consumed_g := by simp
          _ = g.roots := hss_g_eq
      have hcons_f' : ∀ r ∈ (sf ::ₘ consumed_f), r ≤ b := by grind
      have hcons_g' : ∀ r ∈ (sg ::ₘ consumed_g), r ≤ b := by grind
      rcases eq_or_lt_of_le hab with hab_eq | hab_lt
      · have hsf_eq : sf = a := le_antisymm (hab_eq.symm ▸ hsfb) hasf
        have hsg_eq : sg = a := le_antisymm (hab_eq.symm ▸ hsgb) hasg
        simp_all
      · have hf_dichotomy : ∀ r ∈ f.roots.erase sf, r ≤ a ∨ b ≤ r := by
          rw [hf_roots_erase]
          intro r hr
          rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
          · right
            exact listInterlaces_all_ge rest_f rest_rs b hint_f_tail r (Multiset.mem_coe.mp hr_rest)
          · grind
        have hg_dichotomy : ∀ r ∈ g.roots.erase sg, r ≤ a ∨ b ≤ r := by
          rw [hg_roots_erase]
          intro r hr
          rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
          · right
            exact listInterlaces_all_ge rest_g rest_rs b hint_g_tail r (Multiset.mem_coe.mp hr_rest)
          · grind
        have hcount_eq :
            (g.roots.erase sg).countP (b ≤ ·) = (f.roots.erase sf).countP (b ≤ ·) := by
          rw [hf_roots_erase, hg_roots_erase, Multiset.countP_add, Multiset.countP_add]
          have hcf_rest := Multiset.countP_eq_card.mpr (fun r hr =>
            listInterlaces_all_ge rest_f rest_rs b hint_f_tail r (Multiset.mem_coe.mp hr))
          have hcg_rest := Multiset.countP_eq_card.mpr (fun r hr =>
            listInterlaces_all_ge rest_g rest_rs b hint_g_tail r (Multiset.mem_coe.mp hr))
          have hcf_cons : consumed_f.countP (b ≤ ·) = 0 :=
            Multiset.countP_eq_zero.mpr (fun r hr =>
              not_le.mpr (lt_of_le_of_lt (hcons_f_le r hr) hab_lt))
          have hcg_cons : consumed_g.countP (b ≤ ·) = 0 :=
            Multiset.countP_eq_zero.mpr (fun r hr =>
              not_le.mpr (lt_of_le_of_lt (hcons_g_le r hr) hab_lt))
          simp_all
        rcases le_or_gt sf sg with hsfsg | hsfsg
        · have hsign :=
            opposite_sign_at_interlacing_roots hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos
            hasf hsfb hasg hsgb hsf_root hsg_root hf_dichotomy hg_dichotomy hcount_eq
          obtain ⟨u, huf, hub, hufg⟩ := sum_has_root_between hsfsg hsf_root hsg_root hsign
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist_of_no_common_right f g hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos
              (sf ::ₘ consumed_f) (sg ::ₘ consumed_g)
              rest_f rest_g (b :: rest_rs) hlen_f' hlen_g' hint_f_tail hint_g_tail
              hss_f_eq' hss_g_eq' hcons_f' hcons_g'
              (List.forall_mem_of_forall_mem_cons hno_rs)
          have hu_lt_b : u < b := by grind
          have hus_pw' : (u :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw =>
              lt_of_lt_of_le hu_lt_b (listInterlaces_all_ge us rest_rs b hus_int w hw), hus_pw⟩
          exact ⟨u :: us, by simp [hus_len],
            ⟨le_trans hasf huf, le_trans hub hsgb, hus_int⟩,
            fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hufg) (hus_root v),
            hus_pw'⟩
        · have hsgf := le_of_lt hsfsg
          have hsign :=
            opposite_sign_at_interlacing_roots hg_ne hg_splits hf_ne hf_splits hg_pos hf_pos
            hasg hsgb hasf hsfb hsg_root hsf_root hg_dichotomy hf_dichotomy
            (hcount_eq.symm)
          obtain ⟨u, hug, huf, hufg⟩ :=
            sum_has_root_between hsgf hsg_root hsf_root
              (by lia)
          have hufg' : (f + g).IsRoot u := by rwa [add_comm] at hufg
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist_of_no_common_right f g hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos
              (sf ::ₘ consumed_f) (sg ::ₘ consumed_g)
              rest_f rest_g (b :: rest_rs) hlen_f' hlen_g' hint_f_tail hint_g_tail
              hss_f_eq' hss_g_eq' hcons_f' hcons_g'
              (List.forall_mem_of_forall_mem_cons hno_rs)
          have hu_lt_b : u < b := by grind
          have hus_pw' : (u :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw =>
              lt_of_lt_of_le hu_lt_b (listInterlaces_all_ge us rest_rs b hus_int w hw), hus_pw⟩
          exact ⟨u :: us, by simp [hus_len],
            ⟨le_trans hasg hug, le_trans huf hsfb, hus_int⟩,
            fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hufg') (hus_root v),
            hus_pw'⟩
  | [], [], [], hlen_f, _, _, _, _, _, _, _, _ => by
      lia
  | [], [], _ :: _ :: _, hlen_f, _, _, _, _, _, _, _, _ => by
      grind
  | [], _ :: _, _, hlen_f, hlen_g, _, _, _, _, _, _, _ => by
      grind
  | _ :: _, [], _, hlen_f, hlen_g, _, _, _, _, _, _, _ => by
      grind
  | _ :: _, _ :: _, [], hlen_f, _, _, _, _, _, _, _, _ => by
      grind
  | _ :: _, _ :: _, [_], hlen_f, _, _, _, _, _, _, _, _ => by
      grind

/-- If `bigger` has a root `p` below all roots of `smaller`, and `smaller + bigger`
    and `smaller + bigger` has degree one more than `smaller`, then
    `smaller + bigger` has a root ≤ p. Used for the mixed-degree cases in Wagner (1). -/
lemma exists_root_le_of_mixed {smaller bigger : ℝ[X]}
    (hsmaller_ne : smaller ≠ 0)
    (hsmaller_pos : HasPosLeadingCoeff smaller)
    (hsum_pos : HasPosLeadingCoeff (smaller + bigger))
    {p : ℝ} (hbigp : bigger.IsRoot p)
    (hsmaller_gt : ∀ t ∈ smaller.roots, p < t)
    (hdeg : smaller.natDegree + 1 = (smaller + bigger).natDegree) :
    ∃ u₀ : ℝ, u₀ ≤ p ∧ (smaller + bigger).IsRoot u₀ := by
  have hsum_ne : smaller + bigger ≠ 0 := hsum_pos.ne_zero
  have hbig0 : bigger.eval p = 0 := hbigp
  have hsum_eval : (smaller + bigger).eval p = smaller.eval p := by simp_all
  rcases Nat.even_or_odd smaller.natDegree with hpar | hpar
  · have hsmaller_pos_eval : 0 < smaller.eval p :=
      eval_pos_of_all_roots_gt_of_even hsmaller_ne hsmaller_pos hpar hsmaller_gt
    have hsum_deg_pos : 0 < (smaller + bigger).degree := by
      rw [degree_eq_natDegree hsum_ne]
      have : 0 < (smaller + bigger).natDegree := by lia
      simp_all
    have hsum_odd : Odd (smaller + bigger).natDegree := by grind
    obtain ⟨u, hu_le, hu_root⟩ :=
      exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot
        (hsum_eval ▸ hsmaller_pos_eval)
        (tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hsum_pos hsum_deg_pos hsum_odd)
    grind
  · have hsmaller_neg_eval : smaller.eval p < 0 :=
      eval_neg_of_all_roots_gt_of_odd hsmaller_ne hsmaller_pos hpar hsmaller_gt
    have hsum_deg_pos : 0 < (smaller + bigger).degree := by
      rw [degree_eq_natDegree hsum_ne]
      have : 0 < (smaller + bigger).natDegree := by lia
      simp_all
    have hsum_even : Even (smaller + bigger).natDegree := by grind
    obtain ⟨u, hu_le, hu_root⟩ :=
      exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop
        (hsum_eval ▸ hsmaller_neg_eval)
        (tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hsum_pos hsum_deg_pos hsum_even)
    grind

/-- Wagner (1): If f and g both precede h with positive leading coefficients,
    and f + g is real-rooted, then (f + g) precedes h. -/
theorem prec_add_of_prec_right {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg_rr_ne : (f + g) ≠ 0) (hfg_rr_splits : (f + g).Splits)
    (hcop : IsCoprime f g) :
    Prec (f + g) h := by
  obtain ⟨hf, hh, ss_f, rs_f, hss_f_sorted, hrs_f_sorted, hss_f_eq, hrs_f_eq, hcase_f⟩ := hfh
  obtain ⟨hg, _, ss_g, rs_g, hss_g_sorted, hrs_g_sorted, hss_g_eq, hrs_g_eq, hcase_g⟩ := hgh
  rcases hcase_f with ⟨hlen_f, hint_f⟩ | ⟨hlen_f_alt, halt_f⟩
  · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · -- Both differ-by-1: unify the rs lists
      have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      -- Find roots of f+g via the recursive helper
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop 0 0
          ss_f ss_g rs_f hlen_f hlen_g hint_f hint_g
          (by simp [hss_f_eq]) (by simp [hss_g_eq])
          (by simp) (by simp)
      -- us is strictly sorted (Pairwise (· < ·)) by IsCoprime, hence Nodup.
      have hus_nodup : us.Nodup :=
        hus_pw.imp ne_of_lt
      have hus_sub : (↑us : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
        intro u hu
        simp_all
      -- f+g has degree = ss_f.length (from real-rooted and length of us)
      have hfg_natDeg : (f + g).natDegree = us.length := by
        rw [hus_len]
        have : ss_f.length = f.natDegree := by
          rw [← card_roots_of_splits hf.2, ← Multiset.coe_card, hss_f_eq]
        have hfg_deg : (f + g).natDegree = f.natDegree := by
          have hg_natDeg : ss_g.length = g.natDegree := by
            rw [← card_roots_of_splits hg.2, ← Multiset.coe_card, hss_g_eq]
          have hdeg_eq : f.natDegree = g.natDegree := by lia
          exact natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg_eq hf_pos hg_pos
        lia
      -- us exhausts all roots of f+g (since |us| = deg(f+g))
      have hus_eq : (↑us : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hus_sub
        rw [Multiset.coe_card]
        have h1 := card_roots_of_splits hfg_rr_splits
        lia -- using h1 and hfg_natDeg
      -- Build the Prec witness
      exact ⟨⟨hfg_rr_ne, hfg_rr_splits⟩, hh, us, rs_f,
        pairwise_le_of_listInterlaces us rs_f hus_int, hrs_f_sorted, hus_eq, hrs_f_eq,
        Or.inl ⟨by lia, hus_int⟩⟩
    · -- Case A: f differ-by-1, g same-degree
      have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with | nil => simp at hlen_f | cons r rs => lia
      obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
        cases ss_g with | nil => simp at hlen_g_alt | cons s rest => lia
      obtain ⟨hs₁_le, hint_g_tail⟩ := halt_g
      have hs₁_root : g.IsRoot s₁_g :=
        (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
      -- Degree computations
      have hf_deg : ss_f.length = f.natDegree := by
        have := card_roots_of_splits hf.2; rw [← hss_f_eq, Multiset.coe_card] at this; lia
      have hg_deg : g.natDegree = f.natDegree + 1 := by
        have : (s₁_g :: rest_g).length = g.natDegree := by
          have := card_roots_of_splits hg.2; rw [← hss_g_eq, Multiset.coe_card] at this; lia
        lia
      have hdeg_lt : f.natDegree < g.natDegree := by lia
      have hfg_deg : (f + g).natDegree = g.natDegree :=
        natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hg_pos
      have hfg_lc : (f + g).leadingCoeff = g.leadingCoeff := by
        simp only [leadingCoeff, hfg_deg, coeff_add,
          coeff_eq_zero_of_natDegree_lt hdeg_lt, zero_add]
      have hfg_pos : HasPosLeadingCoeff (f + g) :=
        hasPosLeadingCoeff_add_of_natDegree_lt_right hdeg_lt hg_pos
      -- All roots of f are > s₁_g (interlacing + IsCoprime)
      have hsmaller_gt : ∀ t ∈ f.roots, s₁_g < t := by
        intro t ht; rw [← hss_f_eq] at ht
        have ht_ge : r₁ ≤ t :=
          listInterlaces_all_ge ss_f rest_rs r₁ hint_f t (Multiset.mem_coe.mp ht)
        rcases lt_or_eq_of_le (le_trans hs₁_le ht_ge) with h | h
        · lia
        · exfalso; subst h
          have hf0 : Polynomial.eval s₁_g f = 0 :=
            (mem_roots hf.1).mp (by lia)
          have hg0 : Polynomial.eval s₁_g g = 0 := hs₁_root
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval s₁_g) hab
          simp [eval_add, eval_mul, eval_one, hf0, hg0] at this
      obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
        exists_root_le_of_mixed hf.1 hf_pos hfg_pos hs₁_root hsmaller_gt (by
          lia)
      -- Main roots via recursive helper
      have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by grind
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
        rw [← hss_g_eq, Multiset.coe_add]
        simp
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop 0 ↑[s₁_g]
          ss_f rest_g (r₁ :: rest_rs) hlen_f hlen_g_rest hint_f hint_g_tail
          (by simp [hss_f_eq]) hss_g_eq' (by simp)
          (by
             simp_all)
      -- u₀ < r₁ (IsCoprime prevents u₀ = s₁_g = r₁)
      have hu₀_lt_r₁ : u₀ < r₁ := by
        rcases lt_or_eq_of_le (le_trans hu₀_le hs₁_le) with h | h
        · lia
        · exfalso
          have hs_eq : s₁_g = r₁ := le_antisymm hs₁_le (h ▸ hu₀_le)
          have hgr₁ : Polynomial.eval r₁ g = 0 := by simp_all
          have hfr₁ : Polynomial.eval r₁ f = 0 := by simp_all
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval r₁) hab
          simp [eval_add, eval_mul, eval_one, hfr₁, hgr₁] at this
      -- Combine into Prec witness
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu₀_lt_r₁
          (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup := (hpw.imp ne_of_lt : (u₀ :: us).Nodup)
      have hsub : (↑(u₀ :: us) : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
        intro u hu
        exact (mem_roots hfg_rr_ne).mpr
          ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root) (hus_root u))
      have hroots_eq : (↑(u₀ :: us) : Multiset ℝ) = (f + g).roots :=
        Multiset.eq_of_le_of_card_le hsub (by
          rw [Multiset.coe_card]; simp only [List.length_cons]
          have h1 := card_roots_of_splits hfg_rr_splits; lia)
      exact ⟨⟨hfg_rr_ne, hfg_rr_splits⟩, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by grind,
                 ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
  · -- Case B: f same-degree
    rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · -- Case B.1: f same-degree, g differ-by-1 (symmetric to Case A)
      have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with | nil => simp at hlen_g | cons r rs => lia
      obtain ⟨s₁_f, rest_f, rfl⟩ : ∃ a l, ss_f = a :: l := by
        cases ss_f with | nil => simp at hlen_f_alt | cons s rest => lia
      obtain ⟨hs₁_le, hint_f_tail⟩ := halt_f
      have hs₁_root : f.IsRoot s₁_f :=
        (mem_roots hf.1).mp (by rw [← hss_f_eq]; simp)
      have hg_deg : ss_g.length = g.natDegree := by
        have := card_roots_of_splits hg.2; rw [← hss_g_eq, Multiset.coe_card] at this; lia
      have hf_deg : f.natDegree = g.natDegree + 1 := by
        have : (s₁_f :: rest_f).length = f.natDegree := by
          have := card_roots_of_splits hf.2; rw [← hss_f_eq, Multiset.coe_card] at this; lia
        lia
      have hdeg_lt : g.natDegree < f.natDegree := by lia
      have hfg_deg : (f + g).natDegree = f.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hf_pos
      have hfg_pos : HasPosLeadingCoeff (f + g) :=
        hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg_lt hf_pos
      have hsmaller_gt : ∀ t ∈ g.roots, s₁_f < t := by
        intro t ht; rw [← hss_g_eq] at ht
        have ht_ge : r₁ ≤ t :=
          listInterlaces_all_ge ss_g rest_rs r₁ hint_g t (Multiset.mem_coe.mp ht)
        rcases lt_or_eq_of_le (le_trans hs₁_le ht_ge) with h | h
        · lia
        · exfalso; subst h
          have hg0 : Polynomial.eval s₁_f g = 0 :=
            (mem_roots hg.1).mp (by lia)
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval s₁_f) hab
          simp [eval_add, eval_mul, eval_one,
            (show Polynomial.eval s₁_f f = 0 from hs₁_root), hg0] at this
      obtain ⟨u₀, hu₀_le, hu₀_root_gf⟩ :=
        exists_root_le_of_mixed hg.1 hg_pos
          (by rw [show g + f = f + g from add_comm g f]; lia)
          hs₁_root hsmaller_gt (by
            rw [show g + f = f + g from add_comm g f, hfg_deg, hf_deg])
      have hu₀_root : (f + g).IsRoot u₀ := by rwa [add_comm] at hu₀_root_gf
      have hlen_f_rest : rest_f.length + 1 = (r₁ :: rest_rs).length := by grind
      have hss_f_eq' : (↑rest_f : Multiset ℝ) + ↑[s₁_f] = f.roots := by
        rw [← hss_f_eq, Multiset.coe_add]
        simp
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop ↑[s₁_f] 0
          rest_f ss_g (r₁ :: rest_rs) hlen_f_rest hlen_g hint_f_tail hint_g
          hss_f_eq' (by simp [hss_g_eq])
          (by
             simp_all) (by simp)
      have hu₀_lt_r₁ : u₀ < r₁ := by
        rcases lt_or_eq_of_le (le_trans hu₀_le hs₁_le) with h | h
        · lia
        · exfalso
          have hs_eq : s₁_f = r₁ := le_antisymm hs₁_le (h ▸ hu₀_le)
          have hfr₁ : Polynomial.eval r₁ f = 0 := by simp_all
          have hgr₁ : Polynomial.eval r₁ g = 0 := by simp_all
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval r₁) hab
          simp [eval_add, eval_mul, eval_one, hfr₁, hgr₁] at this
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu₀_lt_r₁
          (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup := (hpw.imp ne_of_lt : (u₀ :: us).Nodup)
      have hsub : (↑(u₀ :: us) : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
        intro u hu
        exact (mem_roots hfg_rr_ne).mpr
          ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root) (hus_root u))
      have hroots_eq : (↑(u₀ :: us) : Multiset ℝ) = (f + g).roots :=
        Multiset.eq_of_le_of_card_le hsub (by
          rw [Multiset.coe_card]; simp only [List.length_cons]
          have h1 := card_roots_of_splits hfg_rr_splits; lia)
      exact ⟨⟨hfg_rr_ne, hfg_rr_splits⟩, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by grind,
                 ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
    · -- Case B.2: both same-degree
      have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      rcases rs_f with _ | ⟨r₁, rest_rs⟩
      · -- Degenerate: rs_f = [], all constants
        refine ⟨⟨hfg_rr_ne, hfg_rr_splits⟩, hh, [], [], List.Pairwise.nil,
          List.Pairwise.nil, ?_, hrs_f_eq, Or.inr ⟨rfl, trivial⟩⟩
        simp only [List.length_nil] at hlen_f_alt hlen_g_alt
        have hfnd : f.natDegree = 0 := by
          have := card_roots_of_splits hf.2; rw [← hss_f_eq, Multiset.coe_card] at this; lia
        have hgnd : g.natDegree = 0 := by
          have := card_roots_of_splits hg.2; rw [← hss_g_eq, Multiset.coe_card] at this; lia
        have hfgnd : (f + g).natDegree = 0 := by grind [natDegree_add_le f g]
        have h := card_roots_of_splits hfg_rr_splits; simp_all
      · -- rs_f = r₁ :: rest_rs
        obtain ⟨s₁_f, rest_f, rfl⟩ : ∃ a l, ss_f = a :: l := by
          cases ss_f with | nil => simp at hlen_f_alt | cons s rest => lia
        obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
          cases ss_g with | nil => simp at hlen_g_alt | cons s rest => lia
        obtain ⟨hs₁f_le, hint_f_tail⟩ := halt_f
        obtain ⟨hs₁g_le, hint_g_tail⟩ := halt_g
        have hs₁f_root : f.IsRoot s₁_f :=
          (mem_roots hf.1).mp (by rw [← hss_f_eq]; simp)
        have hs₁g_root : g.IsRoot s₁_g :=
          (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
        have hf_deg : (s₁_f :: rest_f).length = f.natDegree := by
          have := card_roots_of_splits hf.2; rw [← hss_f_eq, Multiset.coe_card] at this; lia
        have hg_deg : (s₁_g :: rest_g).length = g.natDegree := by
          have := card_roots_of_splits hg.2; rw [← hss_g_eq, Multiset.coe_card] at this; lia
        have hdeg_eq : f.natDegree = g.natDegree := by lia
        have hfg_deg : (f + g).natDegree = f.natDegree :=
          natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg_eq hf_pos hg_pos
        have hf_roots_erase : f.roots.erase s₁_f = ↑rest_f := by
          rw [← hss_f_eq, ← Multiset.cons_coe, Multiset.erase_cons_head]
        have hg_roots_erase : g.roots.erase s₁_g = ↑rest_g := by
          rw [← hss_g_eq, ← Multiset.cons_coe, Multiset.erase_cons_head]
        have hcount_eq :
            (g.roots.erase s₁_g).countP (r₁ ≤ ·) =
              (f.roots.erase s₁_f).countP (r₁ ≤ ·) := by
          rw [hf_roots_erase, hg_roots_erase]
          have hcf := Multiset.countP_eq_card.mpr (fun r hr =>
            listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr))
          have hcg := Multiset.countP_eq_card.mpr (fun r hr =>
            listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr))
          simp_all
        have hlen_f_rest : rest_f.length + 1 = (r₁ :: rest_rs).length := by grind
        have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by grind
        have hss_f_eq' : (↑rest_f : Multiset ℝ) + ↑[s₁_f] = f.roots := by
          rw [← hss_f_eq, Multiset.coe_add]
          simp
        have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
          rw [← hss_g_eq, Multiset.coe_add]
          simp
        rcases le_or_gt s₁_f s₁_g with hsfsg | hsfsg
        · have hf_dich : ∀ r ∈ f.roots.erase s₁_f, r ≤ s₁_f ∨ r₁ ≤ r := by
            rw [hf_roots_erase]; intro r hr; right
            exact listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr)
          have hg_dich : ∀ r ∈ g.roots.erase s₁_g, r ≤ s₁_f ∨ r₁ ≤ r := by
            rw [hg_roots_erase]; intro r hr; right
            exact listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr)
          have hsign := opposite_sign_at_interlacing_roots hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos
            (le_refl _) hs₁f_le hsfsg hs₁g_le
            hs₁f_root hs₁g_root hf_dich hg_dich hcount_eq
          obtain ⟨c, hcf, hcg, hc_root⟩ :=
            sum_has_root_between hsfsg hs₁f_root hs₁g_root hsign
          have hc_lt_r₁ : c < r₁ := by
            rcases lt_or_eq_of_le (le_trans hcg hs₁g_le) with h | h
            · lia
            · exfalso
              have : s₁_g = r₁ := le_antisymm hs₁g_le (h ▸ hcg)
              have hgr₁ : Polynomial.eval r₁ g = 0 := by simp_all
              have hfr₁ : Polynomial.eval r₁ f = 0 := by simp_all
              obtain ⟨a, b, hab⟩ := hcop
              have := congr_arg (Polynomial.eval r₁) hab
              simp [eval_add, eval_mul, eval_one, hfr₁, hgr₁] at this
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop ↑[s₁_f] ↑[s₁_g]
              rest_f rest_g (r₁ :: rest_rs) hlen_f_rest hlen_g_rest
              hint_f_tail hint_g_tail hss_f_eq' hss_g_eq'
              (by
                 simp_all)
              (by
                 simp_all)
          have hpw : (c :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hc_lt_r₁
              (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
          have hnodup := (hpw.imp ne_of_lt : (c :: us).Nodup)
          have hsub : (↑(c :: us) : Multiset ℝ) ≤ (f + g).roots := by
            rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
            intro u hu
            exact (mem_roots hfg_rr_ne).mpr
              ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hc_root) (hus_root u))
          have hroots_eq : (↑(c :: us) : Multiset ℝ) = (f + g).roots :=
            Multiset.eq_of_le_of_card_le hsub (by
              rw [Multiset.coe_card]; simp only [List.length_cons]
              simp only [List.length_cons] at hf_deg
              have h1 := card_roots_of_splits hfg_rr_splits; lia)
          exact ⟨⟨hfg_rr_ne, hfg_rr_splits⟩, hh, c :: us, r₁ :: rest_rs,
            hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
            Or.inr ⟨by grind,
                     ⟨le_trans hcg hs₁g_le, hus_int⟩⟩⟩
        · -- s₁_f > s₁_g
          have hsgf := le_of_lt hsfsg
          have hg_dich : ∀ r ∈ g.roots.erase s₁_g, r ≤ s₁_g ∨ r₁ ≤ r := by
            rw [hg_roots_erase]; intro r hr; right
            exact listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr)
          have hf_dich : ∀ r ∈ f.roots.erase s₁_f, r ≤ s₁_g ∨ r₁ ≤ r := by
            rw [hf_roots_erase]; intro r hr; right
            exact listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr)
          have hsign := opposite_sign_at_interlacing_roots hg.1 hg.2 hf.1 hf.2 hg_pos hf_pos
            (le_refl _) hs₁g_le hsgf hs₁f_le
            hs₁g_root hs₁f_root hg_dich hf_dich hcount_eq.symm
          obtain ⟨c, hcg, hcf, hc_root_gf⟩ := sum_has_root_between hsgf hs₁g_root hs₁f_root
            (by lia)
          have hc_root : (f + g).IsRoot c := by rwa [add_comm]
          have hc_lt_r₁ : c < r₁ := by
            rcases lt_or_eq_of_le (le_trans hcf hs₁f_le) with h | h
            · lia
            · exfalso
              have : s₁_f = r₁ := le_antisymm hs₁f_le (h ▸ hcf)
              have hfr₁ : Polynomial.eval r₁ f = 0 := by simp_all
              have hgr₁ : Polynomial.eval r₁ g = 0 := by simp_all
              obtain ⟨a, b, hab⟩ := hcop
              have := congr_arg (Polynomial.eval r₁) hab
              simp [eval_add, eval_mul, eval_one, hfr₁, hgr₁] at this
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop ↑[s₁_f] ↑[s₁_g]
              rest_f rest_g (r₁ :: rest_rs) hlen_f_rest hlen_g_rest
              hint_f_tail hint_g_tail hss_f_eq' hss_g_eq'
              (by
                simp_all)
              (by
                simp_all)
          have hpw : (c :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hc_lt_r₁
              (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
          have hnodup := (hpw.imp ne_of_lt : (c :: us).Nodup)
          have hsub : (↑(c :: us) : Multiset ℝ) ≤ (f + g).roots := by
            rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
            intro u hu
            exact (mem_roots hfg_rr_ne).mpr
              ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hc_root) (hus_root u))
          have hroots_eq : (↑(c :: us) : Multiset ℝ) = (f + g).roots :=
            Multiset.eq_of_le_of_card_le hsub (by
              rw [Multiset.coe_card]; simp only [List.length_cons]
              simp only [List.length_cons] at hf_deg
              have h1 := card_roots_of_splits hfg_rr_splits; lia)
          exact ⟨⟨hfg_rr_ne, hfg_rr_splits⟩, hh, c :: us, r₁ :: rest_rs,
            hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
            Or.inr ⟨by grind,
            ⟨le_trans hcf hs₁f_le, hus_int⟩⟩⟩

/-- A high-level sign-based version of Wagner (1): the only obstruction to the
    interval proof is a root of `f + g` landing exactly on a root of the common
    right-hand polynomial. If that does not happen, then common factors between
    `f` and `g` do not matter. -/
theorem prec_add_of_prec_right_of_no_common_right {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r) :
    Prec (f + g) h := by
  obtain ⟨hf, hh, ss_f, rs_f, hss_f_sorted, hrs_f_sorted, hss_f_eq, hrs_f_eq, hcase_f⟩ := hfh
  obtain ⟨hg, _, ss_g, rs_g, hss_g_sorted, hrs_g_sorted, hss_g_eq, hrs_g_eq, hcase_g⟩ := hgh
  have hno_rs_f : ∀ r ∈ rs_f, ¬ (f + g).IsRoot r := by
    intro r hr
    apply hno r
    exact (mem_roots hh.1).mp (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mp hr)
  rcases hcase_f with ⟨hlen_f, hint_f⟩ | ⟨hlen_f_alt, halt_f⟩
  · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist_of_no_common_right f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos 0 0
          ss_f ss_g rs_f hlen_f hlen_g hint_f hint_g
          (by simp [hss_f_eq]) (by simp [hss_g_eq])
          (by simp) (by simp) hno_rs_f
      have hus_nodup : us.Nodup := hus_pw.imp ne_of_lt
      have hfg_ne : f + g ≠ 0 := by
        have hg_natDeg : ss_g.length = g.natDegree := by
          rw [← card_roots_of_splits hg.2, ← Multiset.coe_card, hss_g_eq]
        have hdeg_eq : f.natDegree = g.natDegree := by
          have hf_natDeg : ss_f.length = f.natDegree := by
            rw [← card_roots_of_splits hf.2, ← Multiset.coe_card, hss_f_eq]
          lia
        exact add_ne_zero_of_same_natDegree_of_posLeadingCoeff hdeg_eq hf_pos hg_pos
      have hus_sub : (↑us : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
        intro u hu
        simp_all
      have hfg_natDeg : (f + g).natDegree = us.length := by
        rw [hus_len]
        have : ss_f.length = f.natDegree := by
          rw [← card_roots_of_splits hf.2, ← Multiset.coe_card, hss_f_eq]
        have hfg_deg : (f + g).natDegree = f.natDegree := by
          have hg_natDeg : ss_g.length = g.natDegree := by
            rw [← card_roots_of_splits hg.2, ← Multiset.coe_card, hss_g_eq]
          have hdeg_eq : f.natDegree = g.natDegree := by lia
          exact natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg_eq hf_pos hg_pos
        lia
      have hus_eq : (↑us : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hus_sub
        rw [Multiset.coe_card]
        calc
          (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
          _ = us.length := hfg_natDeg
      have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
        refine ⟨hfg_ne, splits_of_card_roots ?_⟩
        rw [← hus_eq, Multiset.coe_card, hfg_natDeg]
      exact ⟨hfg_rr, hh, us, rs_f,
        pairwise_le_of_listInterlaces us rs_f hus_int, hrs_f_sorted, hus_eq, hrs_f_eq,
        Or.inl ⟨by lia, hus_int⟩⟩
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with
        | nil => simp at hlen_f
        | cons r rs => lia
      obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
        cases ss_g with
        | nil => simp at hlen_g_alt
        | cons s rest => lia
      obtain ⟨hs₁_le, hint_g_tail⟩ := halt_g
      have hs₁_root : g.IsRoot s₁_g :=
        (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
      have hf_deg : ss_f.length = f.natDegree := by
        have := card_roots_of_splits hf.2
        rw [← hss_f_eq, Multiset.coe_card] at this
        lia
      have hg_deg : g.natDegree = f.natDegree + 1 := by
        have : (s₁_g :: rest_g).length = g.natDegree := by
          have := card_roots_of_splits hg.2
          rw [← hss_g_eq, Multiset.coe_card] at this
          lia
        lia
      have hdeg_lt : f.natDegree < g.natDegree := by lia
      have hfg_deg : (f + g).natDegree = g.natDegree :=
        natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hg_pos
      have hfg_pos : HasPosLeadingCoeff (f + g) :=
        hasPosLeadingCoeff_add_of_natDegree_lt_right hdeg_lt hg_pos
      have hsmaller_gt : ∀ t ∈ f.roots, s₁_g < t := by
        intro t ht
        rw [← hss_f_eq] at ht
        have ht_ge : r₁ ≤ t :=
          listInterlaces_all_ge ss_f rest_rs r₁ hint_f t (Multiset.mem_coe.mp ht)
        rcases lt_or_eq_of_le (le_trans hs₁_le ht_ge) with h | h
        · lia
        · exfalso
          subst h
          have hf0 : Polynomial.eval s₁_g f = 0 :=
            (mem_roots hf.1).mp (by lia)
          have hsum0 : (f + g).IsRoot s₁_g := by simp_all
          grind
      obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
        exists_root_le_of_mixed hf.1 hf_pos hfg_pos hs₁_root hsmaller_gt (by
          lia)
      have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by grind
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
        rw [← hss_g_eq, Multiset.coe_add]
        simp
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist_of_no_common_right f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos 0 ↑[s₁_g]
          ss_f rest_g (r₁ :: rest_rs) hlen_f hlen_g_rest hint_f hint_g_tail
          (by simp [hss_f_eq]) hss_g_eq' (by simp)
          (by
             simp_all)
          hno_rs_f
      have hu₀_lt_r₁ : u₀ < r₁ := by grind
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw =>
          lt_of_lt_of_le hu₀_lt_r₁
            (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup := (hpw.imp ne_of_lt : (u₀ :: us).Nodup)
      have hfg_ne : f + g ≠ 0 := hfg_pos.ne_zero
      have hsub : (↑(u₀ :: us) : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
        intro u hu
        exact (mem_roots hfg_ne).mpr
          ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root) (hus_root u))
      have hroots_eq : (↑(u₀ :: us) : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hsub
        rw [Multiset.coe_card]
        have hcard_le' : (f + g).roots.card ≤ us.length + 1 := by
          calc
            (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
            _ = g.natDegree := hfg_deg
            _ = f.natDegree + 1 := hg_deg
            _ = us.length + 1 := by lia
        grind
      have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
        refine ⟨hfg_ne, splits_of_card_roots ?_⟩
        rw [← hroots_eq, Multiset.coe_card]
        grind
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by grind,
                 ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
  · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with
        | nil => simp at hlen_g
        | cons r rs => lia
      obtain ⟨s₁_f, rest_f, rfl⟩ : ∃ a l, ss_f = a :: l := by
        cases ss_f with
        | nil => simp at hlen_f_alt
        | cons s rest => lia
      obtain ⟨hs₁_le, hint_f_tail⟩ := halt_f
      have hs₁_root : f.IsRoot s₁_f :=
        (mem_roots hf.1).mp (by rw [← hss_f_eq]; simp)
      have hg_deg : ss_g.length = g.natDegree := by
        have := card_roots_of_splits hg.2
        rw [← hss_g_eq, Multiset.coe_card] at this
        lia
      have hf_deg : f.natDegree = g.natDegree + 1 := by
        have : (s₁_f :: rest_f).length = f.natDegree := by
          have := card_roots_of_splits hf.2
          rw [← hss_f_eq, Multiset.coe_card] at this
          lia
        lia
      have hdeg_lt : g.natDegree < f.natDegree := by lia
      have hfg_deg : (f + g).natDegree = f.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hf_pos
      have hfg_pos : HasPosLeadingCoeff (f + g) :=
        hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg_lt hf_pos
      have hsmaller_gt : ∀ t ∈ g.roots, s₁_f < t := by
        intro t ht
        rw [← hss_g_eq] at ht
        have ht_ge : r₁ ≤ t :=
          listInterlaces_all_ge ss_g rest_rs r₁ hint_g t (Multiset.mem_coe.mp ht)
        rcases lt_or_eq_of_le (le_trans hs₁_le ht_ge) with h | h
        · lia
        · exfalso
          subst h
          have hg0 : Polynomial.eval s₁_f g = 0 :=
            (mem_roots hg.1).mp (by lia)
          have hsum0 : (f + g).IsRoot s₁_f := by simp_all
          grind
      obtain ⟨u₀, hu₀_le, hu₀_root_gf⟩ :=
        exists_root_le_of_mixed hg.1 hg_pos
          (by rw [show g + f = f + g from add_comm g f]; lia)
          hs₁_root hsmaller_gt (by
            rw [show g + f = f + g from add_comm g f, hfg_deg, hf_deg])
      have hu₀_root : (f + g).IsRoot u₀ := by rwa [add_comm] at hu₀_root_gf
      have hlen_f_rest : rest_f.length + 1 = (r₁ :: rest_rs).length := by grind
      have hss_f_eq' : (↑rest_f : Multiset ℝ) + ↑[s₁_f] = f.roots := by
        rw [← hss_f_eq, Multiset.coe_add]
        simp
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist_of_no_common_right f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos ↑[s₁_f] 0
          rest_f ss_g (r₁ :: rest_rs) hlen_f_rest hlen_g hint_f_tail hint_g
          hss_f_eq' (by simp [hss_g_eq])
          (by
             simp_all) (by simp)
          hno_rs_f
      have hu₀_lt_r₁ : u₀ < r₁ := by grind
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw =>
          lt_of_lt_of_le hu₀_lt_r₁
            (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup := (hpw.imp ne_of_lt : (u₀ :: us).Nodup)
      have hfg_ne : f + g ≠ 0 := hfg_pos.ne_zero
      have hsub : (↑(u₀ :: us) : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
        intro u hu
        exact (mem_roots hfg_ne).mpr
          ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root) (hus_root u))
      have hroots_eq : (↑(u₀ :: us) : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hsub
        rw [Multiset.coe_card]
        have hcard_le' : (f + g).roots.card ≤ us.length + 1 := by
          calc
            (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
            _ = f.natDegree := hfg_deg
            _ = g.natDegree + 1 := hf_deg
            _ = us.length + 1 := by lia
        grind
      have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
        refine ⟨hfg_ne, splits_of_card_roots ?_⟩
        rw [← hroots_eq, Multiset.coe_card]
        grind
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by grind,
                 ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      rcases rs_f with _ | ⟨r₁, rest_rs⟩
      · simp only [List.length_nil] at hlen_f_alt hlen_g_alt
        have hfnd : f.natDegree = 0 := by
          have := card_roots_of_splits hf.2
          rw [← hss_f_eq, Multiset.coe_card] at this
          lia
        have hgnd : g.natDegree = 0 := by
          have := card_roots_of_splits hg.2
          rw [← hss_g_eq, Multiset.coe_card] at this
          lia
        have hfgnd : (f + g).natDegree = 0 := by grind [natDegree_add_le f g]
        have hfg_ne : f + g ≠ 0 :=
          add_ne_zero_of_same_natDegree_of_posLeadingCoeff (by simp [hfnd, hgnd]) hf_pos hg_pos
        have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
          have hcard_le : (f + g).roots.card ≤ 0 := by
            calc
              (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
              _ = 0 := hfgnd
          have hroots0 : (f + g).roots.card = 0 := by lia
          refine ⟨hfg_ne, splits_of_card_roots ?_⟩
          lia
        refine ⟨hfg_rr, hh, [], [], List.Pairwise.nil, List.Pairwise.nil, ?_,
          hrs_f_eq, Or.inr ⟨rfl, trivial⟩⟩
        have hroots0 : (f + g).roots.card = 0 := by rw [card_roots_of_splits hfg_rr.2, hfgnd]
        simp_all
      · obtain ⟨s₁_f, rest_f, rfl⟩ : ∃ a l, ss_f = a :: l := by
          cases ss_f with
          | nil => simp at hlen_f_alt
          | cons s rest => lia
        obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
          cases ss_g with
          | nil => simp at hlen_g_alt
          | cons s rest => lia
        obtain ⟨hs₁f_le, hint_f_tail⟩ := halt_f
        obtain ⟨hs₁g_le, hint_g_tail⟩ := halt_g
        have hs₁f_root : f.IsRoot s₁_f :=
          (mem_roots hf.1).mp (by rw [← hss_f_eq]; simp)
        have hs₁g_root : g.IsRoot s₁_g :=
          (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
        have hf_deg : (s₁_f :: rest_f).length = f.natDegree := by
          have := card_roots_of_splits hf.2
          rw [← hss_f_eq, Multiset.coe_card] at this
          lia
        have hg_deg : (s₁_g :: rest_g).length = g.natDegree := by
          have := card_roots_of_splits hg.2
          rw [← hss_g_eq, Multiset.coe_card] at this
          lia
        have hdeg_eq : f.natDegree = g.natDegree := by lia
        have hfg_deg : (f + g).natDegree = f.natDegree :=
          natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg_eq hf_pos hg_pos
        have hf_roots_erase : f.roots.erase s₁_f = ↑rest_f := by
          rw [← hss_f_eq, ← Multiset.cons_coe, Multiset.erase_cons_head]
        have hg_roots_erase : g.roots.erase s₁_g = ↑rest_g := by
          rw [← hss_g_eq, ← Multiset.cons_coe, Multiset.erase_cons_head]
        have hcount_eq :
            (g.roots.erase s₁_g).countP (r₁ ≤ ·) =
              (f.roots.erase s₁_f).countP (r₁ ≤ ·) := by
          rw [hf_roots_erase, hg_roots_erase]
          have hcf := Multiset.countP_eq_card.mpr (fun r hr =>
            listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr))
          have hcg := Multiset.countP_eq_card.mpr (fun r hr =>
            listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr))
          simp_all
        have hlen_f_rest : rest_f.length + 1 = (r₁ :: rest_rs).length := by grind
        have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by grind
        have hss_f_eq' : (↑rest_f : Multiset ℝ) + ↑[s₁_f] = f.roots := by
          rw [← hss_f_eq, Multiset.coe_add]
          simp
        have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
          rw [← hss_g_eq, Multiset.coe_add]
          simp
        rcases le_or_gt s₁_f s₁_g with hsfsg | hsfsg
        · have hf_dich : ∀ r ∈ f.roots.erase s₁_f, r ≤ s₁_f ∨ r₁ ≤ r := by
            rw [hf_roots_erase]
            intro r hr
            right
            exact listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr)
          have hg_dich : ∀ r ∈ g.roots.erase s₁_g, r ≤ s₁_f ∨ r₁ ≤ r := by
            rw [hg_roots_erase]
            intro r hr
            right
            exact listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr)
          have hsign := opposite_sign_at_interlacing_roots hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos
            (le_refl _) hs₁f_le hsfsg hs₁g_le
            hs₁f_root hs₁g_root hf_dich hg_dich hcount_eq
          obtain ⟨c, hcf, hcg, hc_root⟩ :=
            sum_has_root_between hsfsg hs₁f_root hs₁g_root hsign
          have hc_lt_r₁ : c < r₁ := by grind
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist_of_no_common_right f g hf.1 hf.2 hg.1 hg.2
              hf_pos hg_pos ↑[s₁_f] ↑[s₁_g]
              rest_f rest_g (r₁ :: rest_rs) hlen_f_rest hlen_g_rest
              hint_f_tail hint_g_tail hss_f_eq' hss_g_eq'
              (by
                 simp_all)
              (by
                 simp_all)
              hno_rs_f
          have hpw : (c :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw =>
              lt_of_lt_of_le hc_lt_r₁
                (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
          have hnodup := (hpw.imp ne_of_lt : (c :: us).Nodup)
          have hfg_ne : f + g ≠ 0 := fun h0 => by simp_all
          have hsub : (↑(c :: us) : Multiset ℝ) ≤ (f + g).roots := by
            rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
            intro u hu
            exact (mem_roots hfg_ne).mpr
              ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hc_root) (hus_root u))
          have hroots_eq : (↑(c :: us) : Multiset ℝ) = (f + g).roots := by
            apply Multiset.eq_of_le_of_card_le hsub
            rw [Multiset.coe_card]
            have hcard_le' : (f + g).roots.card ≤ us.length + 1 := by
              calc
                (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
                _ = f.natDegree := hfg_deg
                _ = us.length + 1 := by lia
            grind
          have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
            refine ⟨hfg_ne, splits_of_card_roots ?_⟩
            rw [← hroots_eq, Multiset.coe_card]
            grind
          exact ⟨hfg_rr, hh, c :: us, r₁ :: rest_rs,
            hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
            Or.inr ⟨by grind,
                     ⟨le_trans hcg hs₁g_le, hus_int⟩⟩⟩
        · have hsgf := le_of_lt hsfsg
          have hg_dich : ∀ r ∈ g.roots.erase s₁_g, r ≤ s₁_g ∨ r₁ ≤ r := by
            rw [hg_roots_erase]
            intro r hr
            right
            exact listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr)
          have hf_dich : ∀ r ∈ f.roots.erase s₁_f, r ≤ s₁_g ∨ r₁ ≤ r := by
            rw [hf_roots_erase]
            intro r hr
            right
            exact listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr)
          have hsign := opposite_sign_at_interlacing_roots hg.1 hg.2 hf.1 hf.2 hg_pos hf_pos
            (le_refl _) hs₁g_le hsgf hs₁f_le
            hs₁g_root hs₁f_root hg_dich hf_dich hcount_eq.symm
          obtain ⟨c, hcg, hcf, hc_root_gf⟩ :=
            sum_has_root_between hsgf hs₁g_root hs₁f_root
              (by lia)
          have hc_root : (f + g).IsRoot c := by rwa [add_comm] at hc_root_gf
          have hc_lt_r₁ : c < r₁ := by grind
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist_of_no_common_right f g hf.1 hf.2 hg.1 hg.2
              hf_pos hg_pos ↑[s₁_f] ↑[s₁_g]
              rest_f rest_g (r₁ :: rest_rs) hlen_f_rest hlen_g_rest
              hint_f_tail hint_g_tail hss_f_eq' hss_g_eq'
              (by
                 simp_all)
              (by
                 simp_all)
              hno_rs_f
          have hpw : (c :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw =>
              lt_of_lt_of_le hc_lt_r₁
                (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
          have hnodup := (hpw.imp ne_of_lt : (c :: us).Nodup)
          have hfg_ne : f + g ≠ 0 := fun h0 => by simp_all
          have hsub : (↑(c :: us) : Multiset ℝ) ≤ (f + g).roots := by
            rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
            intro u hu
            exact (mem_roots hfg_ne).mpr
              ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hc_root) (hus_root u))
          have hroots_eq : (↑(c :: us) : Multiset ℝ) = (f + g).roots := by
            apply Multiset.eq_of_le_of_card_le hsub
            rw [Multiset.coe_card]
            have hcard_le' : (f + g).roots.card ≤ us.length + 1 := by
              calc
                (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
                _ = f.natDegree := hfg_deg
                _ = us.length + 1 := by lia
            grind
          have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
            refine ⟨hfg_ne, splits_of_card_roots ?_⟩
            rw [← hroots_eq, Multiset.coe_card]
            grind
          exact ⟨hfg_rr, hh, c :: us, r₁ :: rest_rs,
            hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
            Or.inr ⟨by grind,
                     ⟨le_trans hcf hs₁f_le, hus_int⟩⟩⟩

/-- A common-factor version of Wagner (1): if `d` is real-rooted and the reduced
    summands satisfy the usual coprime addition theorem, then the original
    summands also satisfy it after multiplying back by `d`. This keeps the
    high-level proof closer to the human argument "factor out the shared part,
    add the quotients, then multiply back". -/
theorem prec_add_of_prec_right_of_common_factor {d f g h : ℝ[X]}
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    {f' g' h' : ℝ[X]}
    (hf_def : f = d * f') (hg_def : g = d * g') (hh_def : h = d * h')
    (hfh : Prec f' h') (hgh : Prec g' h')
    (hf'_pos : HasPosLeadingCoeff f') (hg'_pos : HasPosLeadingCoeff g')
    (hfg'_rr_ne : (f' + g') ≠ 0) (hfg'_rr_splits : (f' + g').Splits)
    (hcop : IsCoprime f' g') :
    Prec (f + g) h := by
  subst hf_def hg_def hh_def
  have hsum : Prec (f' + g') h' :=
    prec_add_of_prec_right hfh hgh hf'_pos hg'_pos hfg'_rr_ne hfg'_rr_splits hcop
  have hmul : Prec (d * (f' + g')) (d * h') := prec_mul_common_factor hd_ne hd_splits hsum
  simpa [left_distrib, right_distrib, mul_add, add_comm, add_left_comm, add_assoc] using hmul

/-- A common-factor version of the no-common-right Wagner theorem. This is the
factor-out-the-shared-part form of the boundary-collision argument. -/
theorem prec_add_of_prec_right_of_common_factor_of_no_common_right {d f g h : ℝ[X]}
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    {f' g' h' : ℝ[X]}
    (hf_def : f = d * f') (hg_def : g = d * g') (hh_def : h = d * h')
    (hfh : Prec f' h') (hgh : Prec g' h')
    (hf'_pos : HasPosLeadingCoeff f') (hg'_pos : HasPosLeadingCoeff g')
    (hno : ∀ r : ℝ, h'.IsRoot r → ¬ (f' + g').IsRoot r) :
    Prec (f + g) h := by
  subst hf_def hg_def hh_def
  have hsum : Prec (f' + g') h' :=
    prec_add_of_prec_right_of_no_common_right hfh hgh hf'_pos hg'_pos hno
  have hmul : Prec (d * (f' + g')) (d * h') := prec_mul_common_factor hd_ne hd_splits hsum
  simpa [left_distrib, right_distrib, mul_add, add_comm, add_left_comm, add_assoc] using hmul

/-- Wagner (1) without a coprimeness hypothesis: positive leading coefficients
and a common right-hand interlacing bound already force `f + g` to precede `h`.
The proof repeatedly cancels any shared root of `h` and `f + g`, then applies
the sign-based no-common-right theorem to the reduced situation. -/
theorem prec_add_of_prec_right_of_posLeadingCoeff {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    Prec (f + g) h := by
  have hP :
      ∀ n, ∀ (f g h : ℝ[X]), h.natDegree = n →
        Prec f h → Prec g h →
        HasPosLeadingCoeff f → HasPosLeadingCoeff g →
        Prec (f + g) h := by
    intro n
    exact Nat.strong_induction_on n (fun n ih =>
      show ∀ (f g h : ℝ[X]), h.natDegree = n →
        Prec f h → Prec g h →
        HasPosLeadingCoeff f → HasPosLeadingCoeff g →
        Prec (f + g) h from by
        intro f g h hn hfh hgh hf_pos hg_pos
        by_cases hcommon : ∃ r : ℝ, h.IsRoot r ∧ (f + g).IsRoot r
        · rcases hcommon with ⟨r, hrh, hrfg⟩
          have hfrg : f.IsRoot r ∧ g.IsRoot r :=
            isRoot_of_isRoot_right_of_isRoot_add hfh hgh hf_pos hg_pos hrh hrfg
          obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hfrg.1
          obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hfrg.2
          obtain ⟨qh, hqh⟩ := dvd_iff_isRoot.mpr hrh
          have hfh' : Prec qf qh := by
            apply prec_of_prec_mul_X_sub_C_both r
            lia
          have hgh' : Prec qg qh := by
            apply prec_of_prec_mul_X_sub_C_both r
            lia
          have hqf_pos : HasPosLeadingCoeff qf := by
            unfold HasPosLeadingCoeff at hf_pos ⊢
            simp_all
          have hqg_pos : HasPosLeadingCoeff qg := by
            unfold HasPosLeadingCoeff at hg_pos ⊢
            simp_all
          have hh_ne : h ≠ 0 := hfh.2.1.1
          have hqh_ne : qh ≠ 0 := by grind
          have hqh_lt : qh.natDegree < n := by
            have hqh_succ : qh.natDegree + 1 = h.natDegree := by
              rw [hqh, natDegree_mul (X_sub_C_ne_zero r) hqh_ne, natDegree_X_sub_C]
              lia
            lia
          have hsum' : Prec (qf + qg) qh := by grind
          have hmul : Prec ((X - C r) * (qf + qg)) ((X - C r) * qh) :=
            prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hsum'
          grind
        · have hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r := by grind
          exact prec_add_of_prec_right_of_no_common_right hfh hgh hf_pos hg_pos hno)
  grind

/-- A mixed-degree version of Wagner (1): if `f` precedes `h` with degree one less,
    `g` precedes `h` with the same degree, and `f` and `g` are coprime, then
    `f + g` precedes `h`. This packages the branch needed for the derangement
    recurrence, avoiding a separate `((f + g) ≠ 0 ∧ (f + g).Splits)` hypothesis. -/
theorem prec_add_of_prec_right_mixed_of_natDegree {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfh_deg : f.natDegree + 1 = h.natDegree)
    (hgh_deg : g.natDegree = h.natDegree)
    (hcop : IsCoprime f g) :
    Prec (f + g) h := by
  obtain ⟨hf, hh, ss_f, rs_f, hss_f_sorted, hrs_f_sorted, hss_f_eq, hrs_f_eq, hcase_f⟩ := hfh
  obtain ⟨hg, _, ss_g, rs_g, hss_g_sorted, hrs_g_sorted, hss_g_eq, hrs_g_eq, hcase_g⟩ := hgh
  rcases hcase_f with ⟨hlen_f, hint_f⟩ | ⟨hlen_f_alt, halt_f⟩
  · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · have hg_deg' : g.natDegree + 1 = h.natDegree := by
        have hss_len : ss_g.length = g.natDegree := by
          rw [← Multiset.coe_card, hss_g_eq, card_roots_of_splits hg.2]
        have hrs_len : rs_g.length = h.natDegree := by
          rw [← Multiset.coe_card, hrs_g_eq, card_roots_of_splits hh.2]
        lia
      lia
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with | nil => simp at hlen_f | cons r rs => lia
      obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
        cases ss_g with | nil => simp at hlen_g_alt | cons s rest => lia
      obtain ⟨hs₁_le, hint_g_tail⟩ := halt_g
      have hs₁_root : g.IsRoot s₁_g :=
        (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
      have hf_deg : ss_f.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_f_eq, card_roots_of_splits hf.2]
      have hg_deg : g.natDegree = f.natDegree + 1 := by lia
      have hdeg_lt : f.natDegree < g.natDegree := by lia
      have hfg_deg : (f + g).natDegree = g.natDegree :=
        natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hg_pos
      have hfg_pos : HasPosLeadingCoeff (f + g) :=
        hasPosLeadingCoeff_add_of_natDegree_lt_right hdeg_lt hg_pos
      have hsmaller_gt : ∀ t ∈ f.roots, s₁_g < t := by
        intro t ht
        rw [← hss_f_eq] at ht
        have ht_ge : r₁ ≤ t :=
          listInterlaces_all_ge ss_f rest_rs r₁ hint_f t (Multiset.mem_coe.mp ht)
        rcases lt_or_eq_of_le (le_trans hs₁_le ht_ge) with h | h
        · lia
        · exfalso
          subst h
          have hf0 : Polynomial.eval s₁_g f = 0 :=
            (mem_roots hf.1).mp (by lia)
          have hg0 : Polynomial.eval s₁_g g = 0 := hs₁_root
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval s₁_g) hab
          simp [eval_add, eval_mul, eval_one, hf0, hg0] at this
      obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
        exists_root_le_of_mixed hf.1 hf_pos hfg_pos hs₁_root hsmaller_gt (by
          lia)
      have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by grind
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
        rw [← hss_g_eq, Multiset.coe_add]
        simp
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos hcop 0 ↑[s₁_g]
          ss_f rest_g (r₁ :: rest_rs) hlen_f hlen_g_rest hint_f hint_g_tail
          (by simp [hss_f_eq]) hss_g_eq' (by simp)
          (by
            simp_all)
      have hu₀_lt_r₁ : u₀ < r₁ := by
        rcases lt_or_eq_of_le (le_trans hu₀_le hs₁_le) with h | h
        · lia
        · exfalso
          have hs_eq : s₁_g = r₁ := le_antisymm hs₁_le (h ▸ hu₀_le)
          have hgr₁ : Polynomial.eval r₁ g = 0 := by simp_all
          have hfr₁ : Polynomial.eval r₁ f = 0 := by simp_all
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval r₁) hab
          simp [eval_add, eval_mul, eval_one, hfr₁, hgr₁] at this
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu₀_lt_r₁
          (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup : (u₀ :: us).Nodup := hpw.imp ne_of_lt
      have hfg_ne : f + g ≠ 0 := hfg_pos.ne_zero
      have hsub : (↑(u₀ :: us) : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
        intro u hu
        exact (mem_roots hfg_ne).mpr
          ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root) (hus_root u))
      have hroots_eq : (↑(u₀ :: us) : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hsub
        have hcard_le' : (f + g).roots.card ≤ us.length + 1 := by
          calc
            (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
            _ = g.natDegree := hfg_deg
            _ = f.natDegree + 1 := hg_deg
            _ = us.length + 1 := by lia
        simp_all
      have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
        refine ⟨hfg_ne, splits_of_card_roots ?_⟩
        rw [← hroots_eq, Multiset.coe_card]
        grind
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by grind,
          ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
  · have hf_deg' : f.natDegree = h.natDegree := by
      have hss_len : ss_f.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_f_eq, card_roots_of_splits hf.2]
      have hrs_len : rs_f.length = h.natDegree := by
        rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hh.2]
      lia
    lia

/-- A sign-based mixed-degree Wagner theorem: if `f` precedes `h` with degree
one less, `g` precedes `h` with the same degree, and the sum `f + g` has no
root in common with `h`, then `f + g` also precedes `h`. This removes the
artificial `IsCoprime f g` restriction from the mixed branch actually used in
recurrences like the derangement-excedance sequence. -/
theorem prec_add_of_prec_right_mixed_of_natDegree_of_no_common_right {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfh_deg : f.natDegree + 1 = h.natDegree)
    (hgh_deg : g.natDegree = h.natDegree)
    (hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r) :
    Prec (f + g) h := by
  obtain ⟨hf, hh, ss_f, rs_f, hss_f_sorted, hrs_f_sorted, hss_f_eq, hrs_f_eq, hcase_f⟩ := hfh
  obtain ⟨hg, _, ss_g, rs_g, hss_g_sorted, hrs_g_sorted, hss_g_eq, hrs_g_eq, hcase_g⟩ := hgh
  have hno_rs_f : ∀ r ∈ rs_f, ¬ (f + g).IsRoot r := by
    intro r hr
    apply hno r
    exact (mem_roots hh.1).mp (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mp hr)
  rcases hcase_f with ⟨hlen_f, hint_f⟩ | ⟨hlen_f_alt, halt_f⟩
  · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · have hg_deg' : g.natDegree + 1 = h.natDegree := by
        have hss_len : ss_g.length = g.natDegree := by
          rw [← Multiset.coe_card, hss_g_eq, card_roots_of_splits hg.2]
        have hrs_len : rs_g.length = h.natDegree := by
          rw [← Multiset.coe_card, hrs_g_eq, card_roots_of_splits hh.2]
        lia
      lia
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with | nil => simp at hlen_f | cons r rs => lia
      obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
        cases ss_g with | nil => simp at hlen_g_alt | cons s rest => lia
      obtain ⟨hs₁_le, hint_g_tail⟩ := halt_g
      have hs₁_root : g.IsRoot s₁_g :=
        (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
      have hf_deg : ss_f.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_f_eq, card_roots_of_splits hf.2]
      have hg_deg : g.natDegree = f.natDegree + 1 := by lia
      have hdeg_lt : f.natDegree < g.natDegree := by lia
      have hfg_deg : (f + g).natDegree = g.natDegree :=
        natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hg_pos
      have hfg_pos : HasPosLeadingCoeff (f + g) :=
        hasPosLeadingCoeff_add_of_natDegree_lt_right hdeg_lt hg_pos
      have hsmaller_gt : ∀ t ∈ f.roots, s₁_g < t := by
        intro t ht
        rw [← hss_f_eq] at ht
        have ht_ge : r₁ ≤ t :=
          listInterlaces_all_ge ss_f rest_rs r₁ hint_f t (Multiset.mem_coe.mp ht)
        rcases lt_or_eq_of_le (le_trans hs₁_le ht_ge) with h | h
        · lia
        · exfalso
          subst h
          have hf0 : Polynomial.eval s₁_g f = 0 :=
            (mem_roots hf.1).mp (by lia)
          have hsum0 : (f + g).IsRoot s₁_g := by simp_all
          grind
      obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
        exists_root_le_of_mixed hf.1 hf_pos hfg_pos hs₁_root hsmaller_gt (by
          lia)
      have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by grind
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
        rw [← hss_g_eq, Multiset.coe_add]
        simp
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist_of_no_common_right f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos 0 ↑[s₁_g]
          ss_f rest_g (r₁ :: rest_rs) hlen_f hlen_g_rest hint_f hint_g_tail
          (by simp [hss_f_eq]) hss_g_eq' (by simp)
          (by
            simp_all)
          hno_rs_f
      have hu₀_lt_r₁ : u₀ < r₁ := by grind
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu₀_lt_r₁
          (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup : (u₀ :: us).Nodup := hpw.imp ne_of_lt
      have hfg_ne : f + g ≠ 0 := hfg_pos.ne_zero
      have hsub : (↑(u₀ :: us) : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
        intro u hu
        exact (mem_roots hfg_ne).mpr
          ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root) (hus_root u))
      have hroots_eq : (↑(u₀ :: us) : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hsub
        have hcard_le' : (f + g).roots.card ≤ us.length + 1 := by
          calc
            (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
            _ = g.natDegree := hfg_deg
            _ = f.natDegree + 1 := hg_deg
            _ = us.length + 1 := by lia
        simp_all
      have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
        refine ⟨hfg_ne, splits_of_card_roots ?_⟩
        rw [← hroots_eq, Multiset.coe_card]
        grind
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by grind,
          ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
  · have hf_deg' : f.natDegree = h.natDegree := by
      have hss_len : ss_f.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_f_eq, card_roots_of_splits hf.2]
      have hrs_len : rs_f.length = h.natDegree := by
        rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hh.2]
      lia
    lia

/-- A common-factor version of the mixed-degree Wagner addition theorem. -/
theorem prec_add_of_prec_right_mixed_of_natDegree_of_common_factor {d f g h : ℝ[X]}
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    {f' g' h' : ℝ[X]}
    (hf_def : f = d * f') (hg_def : g = d * g') (hh_def : h = d * h')
    (hfh : Prec f' h') (hgh : Prec g' h')
    (hf'_pos : HasPosLeadingCoeff f') (hg'_pos : HasPosLeadingCoeff g')
    (hfh_deg : f'.natDegree + 1 = h'.natDegree)
    (hgh_deg : g'.natDegree = h'.natDegree)
    (hcop : IsCoprime f' g') :
    Prec (f + g) h := by
  subst hf_def hg_def hh_def
  have hsum : Prec (f' + g') h' :=
    prec_add_of_prec_right_mixed_of_natDegree hfh hgh hf'_pos hg'_pos hfh_deg hgh_deg hcop
  have hmul : Prec (d * (f' + g')) (d * h') := prec_mul_common_factor hd_ne hd_splits hsum
  simpa [left_distrib, right_distrib, mul_add, add_comm, add_left_comm, add_assoc] using hmul

/-- A common-factor version of the mixed-degree no-common-right Wagner theorem. -/
theorem prec_add_of_prec_right_mixed_of_natDegree_of_common_factor_of_no_common_right
    {d f g h : ℝ[X]}
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    {f' g' h' : ℝ[X]}
    (hf_def : f = d * f') (hg_def : g = d * g') (hh_def : h = d * h')
    (hfh : Prec f' h') (hgh : Prec g' h')
    (hf'_pos : HasPosLeadingCoeff f') (hg'_pos : HasPosLeadingCoeff g')
    (hfh_deg : f'.natDegree + 1 = h'.natDegree)
    (hgh_deg : g'.natDegree = h'.natDegree)
    (hno : ∀ r : ℝ, h'.IsRoot r → ¬ (f' + g').IsRoot r) :
    Prec (f + g) h := by
  subst hf_def hg_def hh_def
  have hsum : Prec (f' + g') h' :=
    prec_add_of_prec_right_mixed_of_natDegree_of_no_common_right
      hfh hgh hf'_pos hg'_pos hfh_deg hgh_deg hno
  have hmul : Prec (d * (f' + g')) (d * h') := prec_mul_common_factor hd_ne hd_splits hsum
  simpa [left_distrib, right_distrib, mul_add, add_comm, add_left_comm, add_assoc] using hmul

end
end RealRooted
