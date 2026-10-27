module

public import RealRooted.WagnerRightSum.Sign
import RealRooted.WagnerX.AffineFactors
import RealRooted.WagnerX.ListInterlacing
import RealRooted.Linear

/-!
# Wagner (1): Common-right addition theorems

If f ≪ h and g ≪ h with positive leading coefficients, then (f + g) ≪ h.
Generalizes to n summands by induction.
-/

public section

open Polynomial Filter

noncomputable section

namespace RealRooted

section

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
        rw [← hss_f_eq, ← Multiset.cons_coe,
          Multiset.erase_add_left_pos _ (by simp), Multiset.erase_cons_head]
      have hg_roots_erase : g.roots.erase sg = ↑rest_g + consumed_g := by
        rw [← hss_g_eq, ← Multiset.cons_coe,
          Multiset.erase_add_left_pos _ (by simp), Multiset.erase_cons_head]
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
        obtain ⟨u, hau, hub, hu_root⟩ :
            ∃ u, a ≤ u ∧ u ≤ b ∧ (f + g).IsRoot u := by
          rcases le_total sf sg with hsfsg | hsgf
          · obtain ⟨u, huf, hug, hu⟩ := sum_has_root_between hsfsg hsf_root hsg_root
              (opposite_sign_at_interlacing_roots hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos
                hasf hsfb hasg hsgb hsf_root hsg_root hf_dichotomy hg_dichotomy hcount_eq)
            exact ⟨u, hasf.trans huf, hug.trans hsgb, hu⟩
          · obtain ⟨u, hug, huf, hu⟩ := sum_has_root_between hsgf hsg_root hsf_root
              (opposite_sign_at_interlacing_roots hg_ne hg_splits hf_ne hf_splits hg_pos hf_pos
                hasg hsgb hasf hsfb hsg_root hsf_root hg_dichotomy hf_dichotomy hcount_eq.symm)
            exact ⟨u, hasg.trans hug, huf.trans hsfb, by rwa [add_comm] at hu⟩
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
          wagner1_roots_exist_of_no_common_right f g hf_ne hf_splits hg_ne hg_splits hf_pos hg_pos
            (sf ::ₘ consumed_f) (sg ::ₘ consumed_g)
            rest_f rest_g (b :: rest_rs) hlen_f' hlen_g' hint_f_tail hint_g_tail
            hss_f_eq' hss_g_eq' hcons_f' hcons_g'
            (List.forall_mem_of_forall_mem_cons hno_rs)
        have hu_lt_b : u < b := by grind
        exact ⟨u :: us, by simp [hus_len], ⟨hau, hub, hus_int⟩,
          fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hu_root) (hus_root v),
          List.pairwise_cons.mpr ⟨fun w hw =>
            lt_of_lt_of_le hu_lt_b (listInterlaces_all_ge us rest_rs b hus_int w hw), hus_pw⟩⟩
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
private lemma exists_root_le_of_mixed {smaller bigger : ℝ[X]}
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
  have hsum_deg_pos : 0 < (smaller + bigger).degree := by
    rw [degree_eq_natDegree hsum_ne]
    have : 0 < (smaller + bigger).natDegree := by lia
    simp_all
  rcases Nat.even_or_odd smaller.natDegree with hpar | hpar
  · have hsmaller_pos_eval : 0 < smaller.eval p :=
      eval_pos_of_all_roots_gt_of_even hsmaller_ne hsmaller_pos hpar hsmaller_gt
    have hsum_odd : Odd (smaller + bigger).natDegree := by grind
    exact exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot
      (hsum_eval ▸ hsmaller_pos_eval)
      (tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hsum_pos hsum_deg_pos hsum_odd)
  · have hsmaller_neg_eval : smaller.eval p < 0 :=
      eval_neg_of_all_roots_gt_of_odd hsmaller_ne hsmaller_pos hpar hsmaller_gt
    have hsum_even : Even (smaller + bigger).natDegree := by grind
    exact exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop
      (hsum_eval ▸ hsmaller_neg_eval)
      (tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hsum_pos hsum_deg_pos hsum_even)

/-- A high-level sign-based version of Wagner (1): the only obstruction to the
    interval proof is a root of `f + g` landing exactly on a root of the common
    right-hand polynomial. If that does not happen, then common factors between
    `f` and `g` do not matter. -/
theorem StrictInterl.add_of_right_of_no_common_right {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r) :
    StrictInterl (f + g) h := by
  wlog hdeg : f.natDegree ≤ g.natDegree generalizing f g
  · rw [add_comm]
    apply this hgh hfh hg_pos hf_pos
    · simpa [add_comm] using hno
    · lia
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
      have hf_deg : ss_f.length = f.natDegree := by
        rw [← Polynomial.splits_iff_card_roots.mp hf.2, ← Multiset.coe_card, hss_f_eq]
      have hg_deg : ss_g.length = g.natDegree := by
        rw [← Polynomial.splits_iff_card_roots.mp hg.2, ← Multiset.coe_card, hss_g_eq]
      have hdeg_eq : f.natDegree = g.natDegree := by lia
      have hfg_ne := add_ne_zero_of_same_natDegree_of_posLeadingCoeff hdeg_eq hf_pos hg_pos
      have hfg_deg := natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg_eq hf_pos hg_pos
      have hus_sub : (↑us : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hus_pw.imp ne_of_lt))]
        intro u hu
        simp_all
      have hfg_natDeg : (f + g).natDegree = us.length := by lia
      have hus_eq : (↑us : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hus_sub
        rw [Multiset.coe_card]
        calc
          (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
          _ = us.length := hfg_natDeg
      have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
        refine ⟨hfg_ne, Polynomial.splits_iff_card_roots.mpr ?_⟩
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
        have := Polynomial.splits_iff_card_roots.mp hf.2
        rw [← hss_f_eq, Multiset.coe_card] at this
        lia
      have hg_deg : g.natDegree = f.natDegree + 1 := by
        have : (s₁_g :: rest_g).length = g.natDegree := by
          have := Polynomial.splits_iff_card_roots.mp hg.2
          rw [← hss_g_eq, Multiset.coe_card] at this
          lia
        lia
      have hdeg_lt : f.natDegree < g.natDegree := by lia
      have hfg_deg : (f + g).natDegree = g.natDegree :=
        Polynomial.natDegree_add_eq_right_of_natDegree_lt hdeg_lt
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
      have hfg_ne : f + g ≠ 0 := hfg_pos.ne_zero
      have hsub : (↑(u₀ :: us) : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hpw.imp ne_of_lt))]
        intro u hu
        exact (mem_roots hfg_ne).mpr
          ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root) (hus_root u))
      have hroots_eq : (↑(u₀ :: us) : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hsub
        rw [Multiset.coe_card]
        calc
          (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
          _ = g.natDegree := hfg_deg
          _ = f.natDegree + 1 := hg_deg
          _ = us.length + 1 := by lia
          _ = (u₀ :: us).length := by simp
      have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
        refine ⟨hfg_ne, Polynomial.splits_iff_card_roots.mpr ?_⟩
        rw [← hroots_eq, Multiset.coe_card]
        grind
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by grind,
                 ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
  · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · have hf_deg : ss_f.length = f.natDegree := by
        rw [← Polynomial.splits_iff_card_roots.mp hf.2, ← Multiset.coe_card, hss_f_eq]
      have hg_deg : ss_g.length = g.natDegree := by
        rw [← Polynomial.splits_iff_card_roots.mp hg.2, ← Multiset.coe_card, hss_g_eq]
      have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      lia
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      rcases rs_f with _ | ⟨r₁, rest_rs⟩
      · simp only [List.length_nil] at hlen_f_alt hlen_g_alt
        have hfnd : f.natDegree = 0 := by
          have := Polynomial.splits_iff_card_roots.mp hf.2
          rw [← hss_f_eq, Multiset.coe_card] at this
          lia
        have hgnd : g.natDegree = 0 := by
          have := Polynomial.splits_iff_card_roots.mp hg.2
          rw [← hss_g_eq, Multiset.coe_card] at this
          lia
        have hfgnd : (f + g).natDegree = 0 := by grind [natDegree_add_le f g]
        have hfg_ne : f + g ≠ 0 :=
          add_ne_zero_of_same_natDegree_of_posLeadingCoeff (by simp [hfnd, hgnd]) hf_pos hg_pos
        have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) :=
          ⟨hfg_ne, Polynomial.Splits.of_natDegree_eq_zero hfgnd⟩
        refine ⟨hfg_rr, hh, [], [], List.Pairwise.nil, List.Pairwise.nil, ?_,
          hrs_f_eq, Or.inr ⟨rfl, trivial⟩⟩
        exact (Multiset.card_eq_zero.mp (by
          rw [Polynomial.splits_iff_card_roots.mp hfg_rr.2, hfgnd])).symm
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
          have := Polynomial.splits_iff_card_roots.mp hf.2
          rw [← hss_f_eq, Multiset.coe_card] at this
          lia
        have hg_deg : (s₁_g :: rest_g).length = g.natDegree := by
          have := Polynomial.splits_iff_card_roots.mp hg.2
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
        have hf_dich (x : ℝ) : ∀ r ∈ f.roots.erase s₁_f, r ≤ x ∨ r₁ ≤ r := by
          rw [hf_roots_erase]
          exact fun r hr => Or.inr
            (listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr))
        have hg_dich (x : ℝ) : ∀ r ∈ g.roots.erase s₁_g, r ≤ x ∨ r₁ ≤ r := by
          rw [hg_roots_erase]
          exact fun r hr => Or.inr
            (listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr))
        obtain ⟨c, hc_lt_r₁, hc_root⟩ : ∃ c, c < r₁ ∧ (f + g).IsRoot c := by
          rcases le_total s₁_f s₁_g with hsfsg | hsgf
          · obtain ⟨c, _, hcg, hc⟩ := sum_has_root_between hsfsg hs₁f_root hs₁g_root
              (opposite_sign_at_interlacing_roots hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos
                le_rfl hs₁f_le hsfsg hs₁g_le hs₁f_root hs₁g_root
                (hf_dich s₁_f) (hg_dich s₁_f) hcount_eq)
            exact ⟨c, by grind, hc⟩
          · obtain ⟨c, _, hcf, hc⟩ := sum_has_root_between hsgf hs₁g_root hs₁f_root
              (opposite_sign_at_interlacing_roots hg.1 hg.2 hf.1 hf.2 hg_pos hf_pos
                le_rfl hs₁g_le hsgf hs₁f_le hs₁g_root hs₁f_root
                (hg_dich s₁_g) (hf_dich s₁_g) hcount_eq.symm)
            have hc' : (f + g).IsRoot c := by rwa [add_comm] at hc
            exact ⟨c, by grind, hc'⟩
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
          wagner1_roots_exist_of_no_common_right f g hf.1 hf.2 hg.1 hg.2
            hf_pos hg_pos ↑[s₁_f] ↑[s₁_g] rest_f rest_g (r₁ :: rest_rs)
            hlen_f_rest hlen_g_rest hint_f_tail hint_g_tail hss_f_eq' hss_g_eq'
            (by simp_all) (by simp_all) hno_rs_f
        have hpw : (c :: us).Pairwise (· < ·) :=
          List.pairwise_cons.mpr ⟨fun w hw => hc_lt_r₁.trans_le
            (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
        have hfg_ne : f + g ≠ 0 := fun h0 => by simp_all
        have hsub : (↑(c :: us) : Multiset ℝ) ≤ (f + g).roots := by
          rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hpw.imp ne_of_lt))]
          intro u hu
          exact (mem_roots hfg_ne).mpr
            ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hc_root) (hus_root u))
        have hroots_eq : (↑(c :: us) : Multiset ℝ) = (f + g).roots := by
          apply Multiset.eq_of_le_of_card_le hsub
          rw [Multiset.coe_card]
          calc
            (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
            _ = f.natDegree := hfg_deg
            _ = us.length + 1 := by lia
            _ = (c :: us).length := by simp
        have hfg_rr : ((f + g) ≠ 0 ∧ (f + g).Splits) := by
          refine ⟨hfg_ne, Polynomial.splits_iff_card_roots.mpr ?_⟩
          rw [← hroots_eq, Multiset.coe_card]
          grind
        exact ⟨hfg_rr, hh, c :: us, r₁ :: rest_rs, hpw.imp le_of_lt,
          hrs_f_sorted, hroots_eq, hrs_f_eq,
          Or.inr ⟨by grind, ⟨hc_lt_r₁.le, hus_int⟩⟩⟩

/-- Wagner (1) without a coprimeness hypothesis: positive leading coefficients
and a common right-hand interlacing bound already force `f + g` to precede `h`.
The proof repeatedly cancels any shared root of `h` and `f + g`, then applies
the sign-based no-common-right theorem to the reduced situation. -/
theorem StrictInterl.add_of_right_of_posLeadingCoeff {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    StrictInterl (f + g) h := by
  have hP :
      ∀ n, ∀ (f g h : ℝ[X]), h.natDegree = n →
        StrictInterl f h → StrictInterl g h →
        HasPosLeadingCoeff f → HasPosLeadingCoeff g →
        StrictInterl (f + g) h :=
    fun n => Nat.strong_induction_on n (fun n ih =>
      show ∀ (f g h : ℝ[X]), h.natDegree = n →
        StrictInterl f h → StrictInterl g h →
        HasPosLeadingCoeff f → HasPosLeadingCoeff g →
        StrictInterl (f + g) h from by
        intro f g h hn hfh hgh hf_pos hg_pos
        by_cases hcommon : ∃ r : ℝ, h.IsRoot r ∧ (f + g).IsRoot r
        · rcases hcommon with ⟨r, hrh, hrfg⟩
          have hfrg : f.IsRoot r ∧ g.IsRoot r :=
            isRoot_of_isRoot_right_of_isRoot_add hfh hgh hf_pos hg_pos hrh hrfg
          obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hfrg.1
          obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hfrg.2
          obtain ⟨qh, hqh⟩ := dvd_iff_isRoot.mpr hrh
          have hfh' : StrictInterl qf qh := by
            apply StrictInterl.of_mul_X_sub_C_both (r := r)
            lia
          have hgh' : StrictInterl qg qh := by
            apply StrictInterl.of_mul_X_sub_C_both (r := r)
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
            rw [← hn, hqh, natDegree_mul (X_sub_C_ne_zero r) hqh_ne, natDegree_X_sub_C]
            lia
          have hsum' : StrictInterl (qf + qg) qh := by grind
          have hmul : StrictInterl ((X - C r) * (qf + qg)) ((X - C r) * qh) :=
            hsum'.mul_common_factor
              (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2
          grind
        · have hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r := by grind
          exact StrictInterl.add_of_right_of_no_common_right hfh hgh hf_pos hg_pos hno)
  exact hP h.natDegree f g h rfl hfh hgh hf_pos hg_pos

/-! ## Deprecated Wagner sum names -/

end
end RealRooted
