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

/-- A long enough strictly ordered list of roots exhausts a polynomial's roots. -/
private lemma roots_eq_and_splits_of_pairwise_roots {p : ℝ[X]} {us : List ℝ}
    (hp_ne : p ≠ 0) (hpw : us.Pairwise (· < ·))
    (hroots : ∀ u ∈ us, p.IsRoot u) (hdegree : p.natDegree ≤ us.length) :
    (↑us : Multiset ℝ) = p.roots ∧ p.Splits := by
  have hsub : (↑us : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hpw.imp ne_of_lt))]
    exact fun u hu => (mem_roots hp_ne).mpr (hroots u (Multiset.mem_coe.mp hu))
  have heq := Multiset.eq_of_le_of_card_le hsub (by
    rw [Multiset.coe_card]
    exact (card_roots' p).trans hdegree)
  refine ⟨heq, Polynomial.splits_iff_card_roots.mpr ?_⟩
  rw [← heq, Multiset.coe_card]
  apply le_antisymm
  · simpa [← heq] using card_roots' p
  · exact hdegree

/-- Wagner's right-sum argument when both left polynomials have degree one below the right. -/
private lemma strictInterl_add_of_right_succ_succ {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r)
    (hfdeg : f.natDegree + 1 = h.natDegree)
    (hgdeg : g.natDegree + 1 = h.natDegree) : StrictInterl (f + g) h := by
  obtain ⟨hh, hf, _, rs_f, ss_f, hrs_f_sorted, hss_f_sorted, hrs_f_eq,
    hss_f_eq, hint_f⟩ := hfh.toInterlaces hfdeg
  obtain ⟨_, hg, _, rs_g, ss_g, hrs_g_sorted, hss_g_sorted, hrs_g_eq,
    hss_g_eq, hint_g⟩ := hgh.toInterlaces hgdeg
  have hrs_eq : rs_f = rs_g := by
    apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
    exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
  subst rs_g
  have hno_rs : ∀ r ∈ rs_f, ¬ (f + g).IsRoot r := by
    intro r hr
    exact hno r ((mem_roots hh.1).mp (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mp hr))
  have hss_f_len := hf.2.length_eq_natDegree_of_coe_eq_roots hss_f_eq
  have hss_g_len := hg.2.length_eq_natDegree_of_coe_eq_roots hss_g_eq
  have hrs_len := hh.2.length_eq_natDegree_of_coe_eq_roots hrs_f_eq
  obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
    wagner1_roots_exist_of_no_common_right f g hf.1 hf.2 hg.1 hg.2 hf_pos hg_pos 0 0
      ss_f ss_g rs_f (by lia) (by lia) hint_f hint_g (by simp [hss_f_eq])
      (by simp [hss_g_eq]) (by simp) (by simp) hno_rs
  have hfg_ne := add_ne_zero_of_same_natDegree_of_posLeadingCoeff (by lia) hf_pos hg_pos
  have hfg_degree : (f + g).natDegree ≤ us.length := by
    rw [hus_len, hss_f_len]
    exact (natDegree_add_le f g).trans (max_le le_rfl (by lia))
  obtain ⟨hus_eq, hfg_splits⟩ :=
    roots_eq_and_splits_of_pairwise_roots hfg_ne hus_pw hus_root hfg_degree
  exact ⟨⟨hfg_ne, hfg_splits⟩, hh, us, rs_f,
    pairwise_le_of_listInterlaces us rs_f hus_int, hrs_f_sorted, hus_eq, hrs_f_eq,
    Or.inl ⟨by lia, hus_int⟩⟩

/-- Wagner's right-sum argument when only the second left polynomial has full degree. -/
private lemma strictInterl_add_of_right_succ_same {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r)
    (hfdeg : f.natDegree + 1 = h.natDegree)
    (hgdeg : g.natDegree = h.natDegree) : StrictInterl (f + g) h := by
  obtain ⟨hh, hf, _, rs, ss_f, hrs_sorted, _, hrs_eq, hss_f_eq, hint_f⟩ :=
    hfh.toInterlaces hfdeg
  obtain ⟨ss_g, rs_g, _, hrs_g_sorted, hss_g_eq, hrs_g_eq, halt_g⟩ :=
    hgh.exists_listAlternates_of_natDegree_eq hgdeg
  have hrs_eq' : rs = rs_g := by
    apply List.Perm.eq_of_pairwise' hrs_sorted hrs_g_sorted
    exact Multiset.coe_eq_coe.mp (hrs_eq.trans hrs_g_eq.symm)
  subst rs_g
  have hrs_len := hh.2.length_eq_natDegree_of_coe_eq_roots hrs_eq
  have hss_f_len := hf.2.length_eq_natDegree_of_coe_eq_roots hss_f_eq
  have hss_g_len := hgh.1.2.length_eq_natDegree_of_coe_eq_roots hss_g_eq
  obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs = a :: l := by
    cases rs with
    | nil => simp at hrs_len; lia
    | cons r rs => exact ⟨r, rs, rfl⟩
  obtain ⟨s₁, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
    cases ss_g with
    | nil => simp at hss_g_len; lia
    | cons s rest => exact ⟨s, rest, rfl⟩
  simp only [List.length_cons] at hrs_len hss_g_len
  obtain ⟨hs₁_le, hint_g_tail⟩ := halt_g
  have hs₁_root : g.IsRoot s₁ := (mem_roots hgh.1.1).mp (by rw [← hss_g_eq]; simp)
  have hdeg_lt : f.natDegree < g.natDegree := by lia
  have hfg_deg := Polynomial.natDegree_add_eq_right_of_natDegree_lt hdeg_lt
  have hfg_pos := hasPosLeadingCoeff_add_of_natDegree_lt_right hdeg_lt hg_pos
  have hsmaller_gt : ∀ t ∈ f.roots, s₁ < t := by
    intro t ht
    rw [← hss_f_eq] at ht
    have ht_ge := listInterlaces_all_ge ss_f rest_rs r₁ hint_f t (Multiset.mem_coe.mp ht)
    rcases lt_or_eq_of_le (hs₁_le.trans ht_ge) with hlt | heq
    · exact hlt
    · exfalso
      subst t
      have hf0 : Polynomial.eval s₁ f = 0 := (mem_roots hf.1).mp (by lia)
      have hsum0 : (f + g).IsRoot s₁ := by simp_all
      have hs₁r₁ : s₁ = r₁ := le_antisymm hs₁_le ht_ge
      have hs₁mem : s₁ ∈ r₁ :: rest_rs := List.mem_cons.mpr (Or.inl hs₁r₁)
      exact (hno s₁ ((mem_roots hh.1).mp (by
        rw [← hrs_eq]
        exact Multiset.mem_coe.mpr hs₁mem))) hsum0
  obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
    exists_root_le_of_mixed hf.1 hf_pos hfg_pos hs₁_root hsmaller_gt (by lia)
  have hno_rs : ∀ r ∈ r₁ :: rest_rs, ¬ (f + g).IsRoot r := by
    intro r hr
    exact hno r ((mem_roots hh.1).mp (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr))
  obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
    wagner1_roots_exist_of_no_common_right f g hf.1 hf.2 hgh.1.1 hgh.1.2 hf_pos hg_pos
      0 ↑[s₁] ss_f rest_g (r₁ :: rest_rs) (by simp only [List.length_cons]; lia)
      (by simp only [List.length_cons]; lia) hint_f hint_g_tail
      (by simp [hss_f_eq]) (by rw [← hss_g_eq, Multiset.coe_add]; simp) (by simp)
      (by simp_all) hno_rs
  have hu₀_lt : u₀ < r₁ := by
    rcases lt_or_eq_of_le (hu₀_le.trans hs₁_le) with hlt | heq
    · exact hlt
    · exact False.elim (hno_rs u₀ (by simp [← heq]) hu₀_root)
  have hpw : (u₀ :: us).Pairwise (· < ·) := List.pairwise_cons.mpr
    ⟨fun w hw => hu₀_lt.trans_le (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
  obtain ⟨hroots_eq, hfg_splits⟩ := roots_eq_and_splits_of_pairwise_roots
    hfg_pos.ne_zero hpw (fun u hu => (List.mem_cons.mp hu).elim (· ▸ hu₀_root) (hus_root u))
    (by simp only [List.length_cons]; lia)
  exact ⟨⟨hfg_pos.ne_zero, hfg_splits⟩, hh, u₀ :: us, r₁ :: rest_rs,
    hpw.imp le_of_lt, hrs_sorted, hroots_eq, hrs_eq, Or.inr ⟨by
      simp only [List.length_cons]
      lia,
      ⟨hu₀_le.trans hs₁_le, hus_int⟩⟩⟩

/-- The equal-degree Wagner sum is immediate when the common right side is constant. -/
private lemma strictInterl_add_of_right_same_same_zero {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (_hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfdeg : f.natDegree = h.natDegree) (hgdeg : g.natDegree = h.natDegree)
    (hhdeg : h.natDegree = 0) : StrictInterl (f + g) h := by
  have hfg_ne := add_ne_zero_of_same_natDegree_of_posLeadingCoeff (by lia) hf_pos hg_pos
  have hfg_deg : (f + g).natDegree = 0 := by grind [natDegree_add_le f g]
  have hfg_splits := Polynomial.Splits.of_natDegree_eq_zero hfg_deg
  have hfg_roots : (↑([] : List ℝ) : Multiset ℝ) = (f + g).roots := by
    exact (Multiset.card_eq_zero.mp (by
      rw [Polynomial.splits_iff_card_roots.mp hfg_splits, hfg_deg])).symm
  have hh_roots : (↑([] : List ℝ) : Multiset ℝ) = h.roots := by
    exact (Multiset.card_eq_zero.mp (by
      rw [Polynomial.splits_iff_card_roots.mp hfh.2.1.2, hhdeg])).symm
  exact ⟨⟨hfg_ne, hfg_splits⟩, hfh.2.1, [], [], List.Pairwise.nil, List.Pairwise.nil,
    hfg_roots, hh_roots, Or.inr ⟨rfl, trivial⟩⟩

/-- Alternating equal-degree root lists force a sum root before their common first slot. -/
private lemma exists_sum_root_lt_of_same_degree_alternates {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r)
    {r₁ s₁f s₁g : ℝ} {rest_rs rest_f rest_g : List ℝ}
    (hrs_eq : (↑(r₁ :: rest_rs) : Multiset ℝ) = h.roots)
    (hss_f_eq : (↑(s₁f :: rest_f) : Multiset ℝ) = f.roots)
    (hss_g_eq : (↑(s₁g :: rest_g) : Multiset ℝ) = g.roots)
    (hlen : rest_f.length = rest_g.length)
    (hs₁f_le : s₁f ≤ r₁) (hint_f : ListInterlaces rest_f (r₁ :: rest_rs))
    (hs₁g_le : s₁g ≤ r₁) (hint_g : ListInterlaces rest_g (r₁ :: rest_rs)) :
    ∃ c, c < r₁ ∧ (f + g).IsRoot c := by
  have hs₁f_root : f.IsRoot s₁f := (mem_roots hfh.1.1).mp (by rw [← hss_f_eq]; simp)
  have hs₁g_root : g.IsRoot s₁g := (mem_roots hgh.1.1).mp (by rw [← hss_g_eq]; simp)
  have hf_erase : f.roots.erase s₁f = ↑rest_f := by
    rw [← hss_f_eq, ← Multiset.cons_coe, Multiset.erase_cons_head]
  have hg_erase : g.roots.erase s₁g = ↑rest_g := by
    rw [← hss_g_eq, ← Multiset.cons_coe, Multiset.erase_cons_head]
  have hcount : (g.roots.erase s₁g).countP (r₁ ≤ ·) =
      (f.roots.erase s₁f).countP (r₁ ≤ ·) := by
    have hcf := Multiset.countP_eq_card.mpr (fun r hr =>
      listInterlaces_all_ge rest_f rest_rs r₁ hint_f r (Multiset.mem_coe.mp hr))
    have hcg := Multiset.countP_eq_card.mpr (fun r hr =>
      listInterlaces_all_ge rest_g rest_rs r₁ hint_g r (Multiset.mem_coe.mp hr))
    calc
      _ = (↑rest_g : Multiset ℝ).countP (r₁ ≤ ·) := by rw [hg_erase]
      _ = (↑rest_g : Multiset ℝ).card := hcg
      _ = rest_g.length := by simp
      _ = rest_f.length := hlen.symm
      _ = (↑rest_f : Multiset ℝ).card := by simp
      _ = (↑rest_f : Multiset ℝ).countP (r₁ ≤ ·) := hcf.symm
      _ = _ := by rw [hf_erase]
  have hf_dich (x : ℝ) : ∀ r ∈ f.roots.erase s₁f, r ≤ x ∨ r₁ ≤ r := by
    rw [hf_erase]
    exact fun r hr => Or.inr (listInterlaces_all_ge rest_f rest_rs r₁ hint_f r
      (Multiset.mem_coe.mp hr))
  have hg_dich (x : ℝ) : ∀ r ∈ g.roots.erase s₁g, r ≤ x ∨ r₁ ≤ r := by
    rw [hg_erase]
    exact fun r hr => Or.inr (listInterlaces_all_ge rest_g rest_rs r₁ hint_g r
      (Multiset.mem_coe.mp hr))
  rcases le_total s₁f s₁g with hfg | hgf
  · obtain ⟨c, _, hcg, hc⟩ := sum_has_root_between hfg hs₁f_root hs₁g_root
      (opposite_sign_at_interlacing_roots hfh.1.1 hfh.1.2 hgh.1.1 hgh.1.2
        hf_pos hg_pos le_rfl hs₁f_le hfg hs₁g_le hs₁f_root hs₁g_root
        (hf_dich s₁f) (hg_dich s₁f) hcount)
    refine ⟨c, ?_, hc⟩
    rcases lt_or_eq_of_le (hcg.trans hs₁g_le) with hlt | heq
    · exact hlt
    · subst c
      exact False.elim ((hno r₁ ((mem_roots hfh.2.1.1).mp (by
        rw [← hrs_eq]
        simp))) hc)
  · obtain ⟨c, _, hcf, hc⟩ := sum_has_root_between hgf hs₁g_root hs₁f_root
      (opposite_sign_at_interlacing_roots hgh.1.1 hgh.1.2 hfh.1.1 hfh.1.2
        hg_pos hf_pos le_rfl hs₁g_le hgf hs₁f_le hs₁g_root hs₁f_root
        (hg_dich s₁g) (hf_dich s₁g) hcount.symm)
    have hc' : (f + g).IsRoot c := by rwa [add_comm] at hc
    refine ⟨c, ?_, hc'⟩
    rcases lt_or_eq_of_le (hcf.trans hs₁f_le) with hlt | heq
    · exact hlt
    · subst c
      exact False.elim ((hno r₁ ((mem_roots hfh.2.1.1).mp (by
        rw [← hrs_eq]
        simp))) hc')

/-- Wagner's right-sum argument for three positive equal degrees. -/
private lemma strictInterl_add_of_right_same_same_pos {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r)
    (hfdeg : f.natDegree = h.natDegree) (hgdeg : g.natDegree = h.natDegree)
    (hhdeg : 0 < h.natDegree) : StrictInterl (f + g) h := by
  obtain ⟨ss_f, rs, hss_f_sorted, hrs_sorted, hss_f_eq, hrs_eq, halt_f⟩ :=
    hfh.exists_listAlternates_of_natDegree_eq hfdeg
  obtain ⟨ss_g, rs_g, hss_g_sorted, hrs_g_sorted, hss_g_eq, hrs_g_eq, halt_g⟩ :=
    hgh.exists_listAlternates_of_natDegree_eq hgdeg
  have hrs_eq' : rs = rs_g := by
    apply List.Perm.eq_of_pairwise' hrs_sorted hrs_g_sorted
    exact Multiset.coe_eq_coe.mp (hrs_eq.trans hrs_g_eq.symm)
  subst rs_g
  have hrs_len := hfh.2.1.2.length_eq_natDegree_of_coe_eq_roots hrs_eq
  have hsf_len := hfh.1.2.length_eq_natDegree_of_coe_eq_roots hss_f_eq
  have hsg_len := hgh.1.2.length_eq_natDegree_of_coe_eq_roots hss_g_eq
  obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs = a :: l := by
    cases rs with
    | nil => simp at hrs_len; lia
    | cons r rs => exact ⟨r, rs, rfl⟩
  obtain ⟨s₁f, rest_f, rfl⟩ : ∃ a l, ss_f = a :: l := by
    cases ss_f with
    | nil => simp at hsf_len; lia
    | cons s ss => exact ⟨s, ss, rfl⟩
  obtain ⟨s₁g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
    cases ss_g with
    | nil => simp at hsg_len; lia
    | cons s ss => exact ⟨s, ss, rfl⟩
  simp only [List.length_cons] at hrs_len hsf_len hsg_len
  obtain ⟨hs₁f_le, hint_f⟩ := halt_f
  obtain ⟨hs₁g_le, hint_g⟩ := halt_g
  obtain ⟨c, hc_lt, hc_root⟩ := exists_sum_root_lt_of_same_degree_alternates
    hfh hgh hf_pos hg_pos hno hrs_eq hss_f_eq hss_g_eq (by lia)
    hs₁f_le hint_f hs₁g_le hint_g
  have hno_rs : ∀ r ∈ r₁ :: rest_rs, ¬ (f + g).IsRoot r := fun r hr =>
    hno r ((mem_roots hfh.2.1.1).mp (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr))
  obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
    wagner1_roots_exist_of_no_common_right f g hfh.1.1 hfh.1.2 hgh.1.1 hgh.1.2
      hf_pos hg_pos ↑[s₁f] ↑[s₁g] rest_f rest_g (r₁ :: rest_rs)
      (by simp only [List.length_cons]; lia) (by simp only [List.length_cons]; lia)
      hint_f hint_g (by rw [← hss_f_eq, Multiset.coe_add]; simp)
      (by rw [← hss_g_eq, Multiset.coe_add]; simp) (by simp_all) (by simp_all) hno_rs
  have hpw : (c :: us).Pairwise (· < ·) := List.pairwise_cons.mpr
    ⟨fun w hw => hc_lt.trans_le (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
  have hfg_deg := natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
    (hfdeg.trans hgdeg.symm) hf_pos hg_pos
  have hfg_ne :=
    add_ne_zero_of_same_natDegree_of_posLeadingCoeff (hfdeg.trans hgdeg.symm) hf_pos hg_pos
  obtain ⟨hroots_eq, hfg_splits⟩ := roots_eq_and_splits_of_pairwise_roots
    hfg_ne hpw (fun u hu => (List.mem_cons.mp hu).elim (· ▸ hc_root) (hus_root u))
    (by simp only [List.length_cons]; lia)
  exact ⟨⟨hfg_ne, hfg_splits⟩, hfh.2.1,
    c :: us, r₁ :: rest_rs, hpw.imp le_of_lt, hrs_sorted, hroots_eq, hrs_eq,
    Or.inr ⟨by simp only [List.length_cons]; lia, ⟨hc_lt.le, hus_int⟩⟩⟩

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
    exact this hgh hfh hg_pos hf_pos (by simpa [add_comm] using hno) (by lia)
  rcases hfh.natDegree_eq_or_eq_succ with hf_same | hf_succ
  · rcases hgh.natDegree_eq_or_eq_succ with hg_same | hg_succ
    · by_cases hhdeg : h.natDegree = 0
      · exact strictInterl_add_of_right_same_same_zero hfh hgh hf_pos hg_pos
          hf_same.symm hg_same.symm hhdeg
      · exact strictInterl_add_of_right_same_same_pos hfh hgh hf_pos hg_pos hno
          hf_same.symm hg_same.symm (Nat.pos_of_ne_zero hhdeg)
    · exfalso
      lia
  · rcases hgh.natDegree_eq_or_eq_succ with hg_same | hg_succ
    · exact strictInterl_add_of_right_succ_same hfh hgh hf_pos hg_pos hno
        hf_succ.symm hg_same.symm
    · exact strictInterl_add_of_right_succ_succ hfh hgh hf_pos hg_pos hno
        hf_succ.symm hg_succ.symm

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
