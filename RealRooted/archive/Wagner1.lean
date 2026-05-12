/-
# Wagner's lemma, form (1)

If `Prec f h` and `Prec g h` with positive leading coefficients
and `IsCoprime f g`, then `Prec (f+g) h`.

This handles all four cases: both differ-by-1, mixed (f differ-by-1 /
g same-degree and vice versa), and both same-degree.
-/
import RealRooted.Basic
import RealRooted.Interlacing
import RealRooted.SignLemmas

open Polynomial

noncomputable section

namespace RealRooted

/-- Core of Wagner (1): given interlacing lists ss_f, ss_g into rs (differ-by-1),
    there exist roots us of f+g with ListInterlaces us rs.
    The `consumed_f/consumed_g` multisets track roots already processed in prior
    intervals; they satisfy `↑ss_f + consumed = f.roots` and are all `≤ rs.head`. -/
private lemma wagner1_roots_exist (f g : ℝ[X])
    (hf : IsRealRooted f) (hg : IsRealRooted g)
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
      refine ⟨[], rfl, trivial, ?_, List.Pairwise.nil⟩
      intro u hu; exact nomatch hu
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
      rw [h, Multiset.erase_cons_head]
    have hg_roots_erase : g.roots.erase sg = ↑rest_g + consumed_g := by
      have h := hss_g_eq.symm
      rw [← Multiset.cons_coe] at h
      rw [Multiset.cons_add] at h
      rw [h, Multiset.erase_cons_head]
    -- Consumed roots are ≤ a (from hypothesis, since rs.head! = a)
    have hcons_f_le : ∀ r ∈ consumed_f, r ≤ a := hcons_f
    have hcons_g_le : ∀ r ∈ consumed_g, r ≤ a := hcons_g
    -- sf is a root of f, sg is a root of g
    have hsf_root : f.IsRoot sf := by
      have : sf ∈ f.roots := by
        rw [← hss_f_eq]; simp [Multiset.mem_add, Multiset.mem_cons]
      exact (mem_roots hf.1).mp this
    have hsg_root : g.IsRoot sg := by
      have : sg ∈ g.roots := by
        rw [← hss_g_eq]; simp [Multiset.mem_add, Multiset.mem_cons]
      exact (mem_roots hg.1).mp this
    -- Shared recursive call arguments
    have hlen_f' : rest_f.length + 1 = (b :: rest_rs).length := by
      simp at hlen_f ⊢; omega
    have hlen_g' : rest_g.length + 1 = (b :: rest_rs).length := by
      simp at hlen_g ⊢; omega
    have hss_f_eq' : (↑rest_f : Multiset ℝ) + (sf ::ₘ consumed_f) = f.roots :=
      calc (↑rest_f : Multiset ℝ) + (sf ::ₘ consumed_f)
          = sf ::ₘ consumed_f + ↑rest_f := add_comm _ _
        _ = sf ::ₘ (consumed_f + ↑rest_f) := Multiset.cons_add ..
        _ = sf ::ₘ (↑rest_f + consumed_f) := by rw [add_comm consumed_f]
        _ = sf ::ₘ ↑rest_f + consumed_f := (Multiset.cons_add ..).symm
        _ = (↑(sf :: rest_f) : Multiset ℝ) + consumed_f := by simp
        _ = f.roots := hss_f_eq
    have hss_g_eq' : (↑rest_g : Multiset ℝ) + (sg ::ₘ consumed_g) = g.roots :=
      calc (↑rest_g : Multiset ℝ) + (sg ::ₘ consumed_g)
          = sg ::ₘ consumed_g + ↑rest_g := add_comm _ _
        _ = sg ::ₘ (consumed_g + ↑rest_g) := Multiset.cons_add ..
        _ = sg ::ₘ (↑rest_g + consumed_g) := by rw [add_comm consumed_g]
        _ = sg ::ₘ ↑rest_g + consumed_g := (Multiset.cons_add ..).symm
        _ = (↑(sg :: rest_g) : Multiset ℝ) + consumed_g := by simp
        _ = g.roots := hss_g_eq
    have hcons_f' : ∀ r ∈ (sf ::ₘ consumed_f), r ≤ b := by
      intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
      · exact hsfb
      · exact le_trans (hcons_f_le r hr) hab
    have hcons_g' : ∀ r ∈ (sg ::ₘ consumed_g), r ≤ b := by
      intro r hr; rcases Multiset.mem_cons.mp hr with rfl | hr
      · exact hsgb
      · exact le_trans (hcons_g_le r hr) hab
    -- Case split: a = b (trivial root) vs a < b (sign lemma)
    rcases eq_or_lt_of_le hab with hab_eq | hab_lt
    · -- a = b: sf = sg = a, but then f(a) = 0 = g(a), contradicting IsCoprime f g
      have hsf_eq : sf = a := le_antisymm (hab_eq.symm ▸ hsfb) hasf
      have hsg_eq : sg = a := le_antisymm (hab_eq.symm ▸ hsgb) hasg
      exfalso
      have hfa : f.eval a = 0 := by rw [← hsf_eq]; exact hsf_root
      have hga : g.eval a = 0 := by rw [← hsg_eq]; exact hsg_root
      obtain ⟨p, q, hpq⟩ := hcop
      have h1 := congr_arg (Polynomial.eval a) hpq
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, hfa, hga] at h1
    · -- a < b: consumed roots are all < b, so countP (b ≤ ·) = 0
      have hf_dichotomy : ∀ r ∈ f.roots.erase sf, r ≤ a ∨ b ≤ r := by
        rw [hf_roots_erase]; intro r hr
        rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
        · right; exact listInterlaces_all_ge rest_f rest_rs b hint_f_tail r
              (Multiset.mem_coe.mp hr_rest)
        · left; exact hcons_f_le r hr_cons
      have hg_dichotomy : ∀ r ∈ g.roots.erase sg, r ≤ a ∨ b ≤ r := by
        rw [hg_roots_erase]; intro r hr
        rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
        · right; exact listInterlaces_all_ge rest_g rest_rs b hint_g_tail r
              (Multiset.mem_coe.mp hr_rest)
        · left; exact hcons_g_le r hr_cons
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
        have hlens : rest_f.length = rest_g.length := by
          simp only [List.length_cons] at hlen_f hlen_g; omega
        rw [hcg_rest, hcf_rest, hcg_cons, hcf_cons]
        simp only [Multiset.coe_card]; omega
      -- Sign lemma + IVT
      rcases le_or_gt sf sg with hsfsg | hsfsg
      · have hsign := opposite_sign_at_interlacing_roots hf hg hf_pos hg_pos hab
          hasf hsfb hasg hsgb hsfsg hsf_root hsg_root hf_dichotomy hg_dichotomy hcount_eq
        obtain ⟨u, huf, hub, hufg⟩ := sum_has_root_between hsfsg hsf_root hsg_root hsign
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
          wagner1_roots_exist f g hf hg hf_pos hg_pos hcop
            (sf ::ₘ consumed_f) (sg ::ₘ consumed_g)
            rest_f rest_g (b :: rest_rs) hlen_f' hlen_g' hint_f_tail hint_g_tail
            hss_f_eq' hss_g_eq' hcons_f' hcons_g'
        -- Under IsCoprime, u < b: if u = b then sg = b, forcing g(b) = f(b) = 0
        have hu_lt_b : u < b := by
          rcases lt_or_eq_of_le (le_trans hub hsgb) with h | h
          · exact h
          · exfalso
            -- h : u = b
            have hsg_b : sg = b := le_antisymm hsgb (h ▸ hub)
            have hgb : g.eval b = 0 := by rw [← hsg_b]; exact hsg_root
            have hfb : f.eval b = 0 := by
              have hmain := h ▸ hufg
              rw [Polynomial.IsRoot.def, Polynomial.eval_add, hgb, add_zero] at hmain
              exact hmain
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
        have hsign := opposite_sign_at_interlacing_roots hg hf hg_pos hf_pos hab
          hasg hsgb hasf hsfb hsgf hsg_root hsf_root hg_dichotomy hf_dichotomy
          (hcount_eq.symm)
        obtain ⟨u, hug, huf, hufg⟩ := sum_has_root_between hsgf hsg_root hsf_root
          (by linarith [mul_comm (eval sf g) (eval sg f)])
        have hufg' : (f + g).IsRoot u := by rwa [add_comm]
        obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
          wagner1_roots_exist f g hf hg hf_pos hg_pos hcop
            (sf ::ₘ consumed_f) (sg ::ₘ consumed_g)
            rest_f rest_g (b :: rest_rs) hlen_f' hlen_g' hint_f_tail hint_g_tail
            hss_f_eq' hss_g_eq' hcons_f' hcons_g'
        -- Under IsCoprime, u < b: if u = b then sf = b, forcing f(b) = g(b) = 0
        have hu_lt_b : u < b := by
          rcases lt_or_eq_of_le (le_trans huf hsfb) with h | h
          · exact h
          · exfalso
            -- h : u = b
            have hsf_b : sf = b := le_antisymm hsfb (h ▸ huf)
            have hfb : f.eval b = 0 := by rw [← hsf_b]; exact hsf_root
            have hgb : g.eval b = 0 := by
              have hmain := h ▸ hufg'
              rw [Polynomial.IsRoot.def, Polynomial.eval_add, hfb, zero_add] at hmain
              exact hmain
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
      simp only [List.length_nil] at hlen_f; omega
  | [], [], _ :: _ :: _, hlen_f, _, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f; omega
  | [], _ :: _, _, hlen_f, hlen_g, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f hlen_g; omega
  | _ :: _, [], _, hlen_f, hlen_g, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f hlen_g; omega
  | _ :: _, _ :: _, [], hlen_f, _, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f; omega
  | _ :: _, _ :: _, [_], hlen_f, _, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f; omega

/-- If `bigger` has a root `p` below all roots of `smaller`, and `smaller + bigger`
    has one more root than `smaller`, then `smaller + bigger` has a root ≤ p.
    Used for the mixed-degree cases in Wagner (1). -/
lemma exists_root_le_of_mixed {smaller bigger : ℝ[X]}
    (hsmaller : IsRealRooted smaller)
    (hfg : IsRealRooted (smaller + bigger))
    (hsmaller_pos : HasPosLeadingCoeff smaller)
    (hfg_pos : HasPosLeadingCoeff (smaller + bigger))
    (hcop : IsCoprime smaller bigger)
    {p : ℝ} (hbigp : bigger.IsRoot p)
    (hsmaller_gt : ∀ t ∈ smaller.roots, p < t)
    (hcard : smaller.roots.card + 1 = (smaller + bigger).roots.card) :
    ∃ u₀ : ℝ, u₀ ≤ p ∧ (smaller + bigger).IsRoot u₀ := by
  by_contra hall; push_neg at hall
  have h_all_gt : ∀ u ∈ (smaller + bigger).roots, p < u :=
    fun u hu => not_le.mp (fun hle => hall u hle ((mem_roots hfg.1).mp hu))
  have hbig0 : bigger.eval p = 0 := hbigp
  have heval_eq : (smaller + bigger).eval p = smaller.eval p := by
    rw [eval_add, hbig0, add_zero]
  set Ps := (smaller.roots.map (p - ·)).prod
  set Pfg := ((smaller + bigger).roots.map (p - ·)).prod
  have heval_s : smaller.eval p = smaller.leadingCoeff * Ps :=
    eval_eq_leadingCoeff_mul_prod_sub hsmaller p
  have heval_fg : (smaller + bigger).eval p = (smaller + bigger).leadingCoeff * Pfg :=
    eval_eq_leadingCoeff_mul_prod_sub hfg p
  have hlc_eq : (smaller + bigger).leadingCoeff * Pfg = smaller.leadingCoeff * Ps := by
    linarith
  -- Sign analysis: Ps has sign (-1)^n, Pfg has sign (-1)^(n+1)
  have h_sign_s : 0 ≤ (-1 : ℝ) ^ smaller.roots.card * Ps := by
    rw [← Multiset.countP_eq_card.mpr (fun r hr => le_of_lt (hsmaller_gt r hr))]
    exact sign_of_prod_countP smaller.roots (fun r => p - r) (fun r => p ≤ r)
      (fun _ _ hnp => by push_neg at hnp; linarith)
      (fun _ _ hp => by linarith)
  have h_sign_fg : 0 ≤ (-1 : ℝ) ^ (smaller + bigger).roots.card * Pfg := by
    rw [← Multiset.countP_eq_card.mpr (fun u hu => le_of_lt (h_all_gt u hu))]
    exact sign_of_prod_countP (smaller + bigger).roots (fun r => p - r) (fun r => p ≤ r)
      (fun _ _ hnp => by push_neg at hnp; linarith)
      (fun _ _ hp => by linarith)
  have hpow : (-1 : ℝ) ^ ((smaller + bigger).roots.card + smaller.roots.card) = -1 := by
    have : (smaller + bigger).roots.card + smaller.roots.card =
        2 * smaller.roots.card + 1 := by omega
    rw [this, pow_add, pow_mul]; norm_num
  have h_nonpos : Pfg * Ps ≤ 0 := by
    have h := mul_nonneg h_sign_fg h_sign_s
    have hrw : (-1 : ℝ) ^ (smaller + bigger).roots.card * Pfg *
        ((-1 : ℝ) ^ smaller.roots.card * Ps) =
        (-1 : ℝ) ^ ((smaller + bigger).roots.card + smaller.roots.card) *
        (Pfg * Ps) := by rw [pow_add]; ring
    rw [hrw, hpow] at h; linarith
  have h_nonneg : 0 ≤ Pfg * Ps := by
    by_contra hlt; push_neg at hlt
    have h1 : (smaller + bigger).leadingCoeff * (Pfg * Ps) < 0 :=
      mul_neg_of_pos_of_neg hfg_pos hlt
    have h2 : 0 ≤ (smaller + bigger).leadingCoeff * (Pfg * Ps) := by
      have hkey : (smaller + bigger).leadingCoeff * (Pfg * Ps) =
          smaller.leadingCoeff * Ps ^ 2 := by
        calc (smaller + bigger).leadingCoeff * (Pfg * Ps)
            = ((smaller + bigger).leadingCoeff * Pfg) * Ps := by ring
          _ = (smaller.leadingCoeff * Ps) * Ps := by rw [hlc_eq]
          _ = smaller.leadingCoeff * Ps ^ 2 := by ring
      rw [hkey]; exact mul_nonneg (le_of_lt hsmaller_pos) (sq_nonneg Ps)
    linarith
  -- Pfg * Ps = 0, so Ps = 0, giving a common root → contradicts IsCoprime
  have h_zero := le_antisymm h_nonpos h_nonneg
  have hPs_zero : Ps = 0 := by
    rcases mul_eq_zero.mp h_zero with hPfg | hPs
    · have : smaller.leadingCoeff * Ps = 0 := by rw [← hlc_eq, hPfg, mul_zero]
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hsmaller_pos)
    · exact hPs
  have hp0 : Polynomial.eval p smaller = 0 := by rw [heval_s, hPs_zero, mul_zero]
  obtain ⟨a, b, hab⟩ := hcop
  have := congr_arg (Polynomial.eval p) hab
  simp [eval_add, eval_mul, eval_one, hp0, hbig0] at this

/-- Wagner (1): If f and g both precede h with positive leading coefficients,
    and f + g is real-rooted, then (f + g) precedes h. -/
theorem prec_add_of_prec_right {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg_rr : IsRealRooted (f + g))
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
        wagner1_roots_exist f g hf hg hf_pos hg_pos hcop 0 0
          ss_f ss_g rs_f hlen_f hlen_g hint_f hint_g
          (by simp [hss_f_eq]) (by simp [hss_g_eq])
          (by simp) (by simp)
      -- us is strictly sorted (Pairwise (· < ·)) by IsCoprime, hence Nodup.
      have hus_nodup : us.Nodup :=
        hus_pw.imp ne_of_lt
      have hus_sub : (↑us : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
        intro u hu
        exact (mem_roots hfg_rr.1).mpr (hus_root u (Multiset.mem_coe.mp hu))
      -- f+g has degree = ss_f.length (from real-rooted and length of us)
      have hfg_natDeg : (f + g).natDegree = us.length := by
        rw [hus_len]
        have : ss_f.length = f.natDegree := by
          rw [← hf.2, ← Multiset.coe_card, hss_f_eq]
        have hfg_deg : (f + g).natDegree = f.natDegree := by
          have hg_natDeg : ss_g.length = g.natDegree := by
            rw [← hg.2, ← Multiset.coe_card, hss_g_eq]
          have hdeg_eq : f.natDegree = g.natDegree := by omega
          have hup : (f + g).natDegree ≤ f.natDegree := by
            have h := natDegree_add_le f g
            rw [max_eq_left hdeg_eq.symm.le] at h; exact h
          have hdown : f.natDegree ≤ (f + g).natDegree := by
            apply le_natDegree_of_ne_zero
            rw [coeff_add]
            have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
            have hgc : g.coeff f.natDegree = g.leadingCoeff := by
              unfold leadingCoeff; rw [← hdeg_eq]
            rw [hfc, hgc]
            exact ne_of_gt (by unfold HasPosLeadingCoeff at hf_pos hg_pos; linarith)
          exact le_antisymm hup hdown
        omega
      -- us exhausts all roots of f+g (since |us| = deg(f+g))
      have hus_eq : (↑us : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hus_sub
        rw [Multiset.coe_card]
        have h1 := hfg_rr.2  -- (f+g).roots.card = (f+g).natDegree
        omega  -- using h1 and hfg_natDeg
      -- Build the Prec witness
      exact ⟨hfg_rr, hh, us, rs_f,
        pairwise_le_of_listInterlaces us rs_f hus_int, hrs_f_sorted, hus_eq, hrs_f_eq,
        Or.inl ⟨by rw [hus_len]; have := hlen_f; simp at this ⊢; omega, hus_int⟩⟩
    · -- Case A: f differ-by-1, g same-degree
      have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with | nil => simp at hlen_f | cons r rs => exact ⟨r, rs, rfl⟩
      obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
        cases ss_g with | nil => simp at hlen_g_alt | cons s rest => exact ⟨s, rest, rfl⟩
      obtain ⟨hs₁_le, hint_g_tail⟩ := halt_g
      have hs₁_root : g.IsRoot s₁_g :=
        (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
      -- Degree computations
      have hf_deg : ss_f.length = f.natDegree := by
        have := hf.2; rw [← hss_f_eq, Multiset.coe_card] at this; exact this
      have hg_deg : g.natDegree = f.natDegree + 1 := by
        have : (s₁_g :: rest_g).length = g.natDegree := by
          have := hg.2; rw [← hss_g_eq, Multiset.coe_card] at this; exact this
        simp [List.length_cons] at this hlen_f hlen_g_alt; omega
      have hdeg_lt : f.natDegree < g.natDegree := by omega
      have hfg_deg : (f + g).natDegree = g.natDegree := by
        apply le_antisymm
        · have h := natDegree_add_le f g; rwa [max_eq_right hdeg_lt.le] at h
        · apply le_natDegree_of_ne_zero; rw [coeff_add,
            coeff_eq_zero_of_natDegree_lt hdeg_lt, zero_add]
          exact ne_of_gt hg_pos
      have hfg_lc : (f + g).leadingCoeff = g.leadingCoeff := by
        simp only [leadingCoeff, hfg_deg, coeff_add,
          coeff_eq_zero_of_natDegree_lt hdeg_lt, zero_add]
      have hfg_pos : HasPosLeadingCoeff (f + g) := by
        show 0 < (f + g).leadingCoeff; rw [hfg_lc]; exact hg_pos
      -- All roots of f are > s₁_g (interlacing + IsCoprime)
      have hsmaller_gt : ∀ t ∈ f.roots, s₁_g < t := by
        intro t ht; rw [← hss_f_eq] at ht
        have ht_ge : r₁ ≤ t :=
          listInterlaces_all_ge ss_f rest_rs r₁ hint_f t (Multiset.mem_coe.mp ht)
        rcases lt_or_eq_of_le (le_trans hs₁_le ht_ge) with h | h
        · exact h
        · exfalso; subst h
          have hf0 : Polynomial.eval s₁_g f = 0 :=
            (mem_roots hf.1).mp (by rwa [hss_f_eq] at ht)
          have hg0 : Polynomial.eval s₁_g g = 0 := hs₁_root
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval s₁_g) hab
          simp [eval_add, eval_mul, eval_one, hf0, hg0] at this
      have hcard : f.roots.card + 1 = (f + g).roots.card := by
        rw [hf.2, hfg_rr.2, hfg_deg, hg_deg]
      obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
        exists_root_le_of_mixed hf hfg_rr hf_pos hfg_pos hcop hs₁_root hsmaller_gt hcard
      -- Main roots via recursive helper
      have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by
        simp [List.length_cons] at hlen_g_alt ⊢; omega
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
        rw [← hss_g_eq, Multiset.coe_add]
        exact Multiset.coe_eq_coe.mpr List.perm_append_comm
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist f g hf hg hf_pos hg_pos hcop 0 ↑[s₁_g]
          ss_f rest_g (r₁ :: rest_rs) hlen_f hlen_g_rest hint_f hint_g_tail
          (by simp [hss_f_eq]) hss_g_eq' (by simp)
          (by intro r hr; simp at hr; subst hr; exact hs₁_le)
      -- u₀ < r₁ (IsCoprime prevents u₀ = s₁_g = r₁)
      have hu₀_lt_r₁ : u₀ < r₁ := by
        rcases lt_or_eq_of_le (le_trans hu₀_le hs₁_le) with h | h
        · exact h
        · exfalso
          have hs_eq : s₁_g = r₁ := le_antisymm hs₁_le (h ▸ hu₀_le)
          have hgr₁ : Polynomial.eval r₁ g = 0 := by rw [← hs_eq]; exact hs₁_root
          have hfr₁ : Polynomial.eval r₁ f = 0 := by
            have := (show (f + g).IsRoot r₁ from h ▸ hu₀_root)
            simp [IsRoot.def, eval_add, hgr₁] at this; exact this
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
        exact (mem_roots hfg_rr.1).mpr
          ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root) (hus_root u))
      have hroots_eq : (↑(u₀ :: us) : Multiset ℝ) = (f + g).roots :=
        Multiset.eq_of_le_of_card_le hsub (by
          rw [Multiset.coe_card]; simp only [List.length_cons]
          have h1 := hfg_rr.2; rw [hfg_deg, hg_deg] at h1; omega)
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by simp only [List.length_cons] at hlen_f ⊢; omega,
                 ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
  · -- Case B: f same-degree
    rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · -- Case B.1: f same-degree, g differ-by-1 (symmetric to Case A)
      have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with | nil => simp at hlen_g | cons r rs => exact ⟨r, rs, rfl⟩
      obtain ⟨s₁_f, rest_f, rfl⟩ : ∃ a l, ss_f = a :: l := by
        cases ss_f with | nil => simp at hlen_f_alt | cons s rest => exact ⟨s, rest, rfl⟩
      obtain ⟨hs₁_le, hint_f_tail⟩ := halt_f
      have hs₁_root : f.IsRoot s₁_f :=
        (mem_roots hf.1).mp (by rw [← hss_f_eq]; simp)
      have hg_deg : ss_g.length = g.natDegree := by
        have := hg.2; rw [← hss_g_eq, Multiset.coe_card] at this; exact this
      have hf_deg : f.natDegree = g.natDegree + 1 := by
        have : (s₁_f :: rest_f).length = f.natDegree := by
          have := hf.2; rw [← hss_f_eq, Multiset.coe_card] at this; exact this
        simp [List.length_cons] at this hlen_g hlen_f_alt; omega
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
      have hsmaller_gt : ∀ t ∈ g.roots, s₁_f < t := by
        intro t ht; rw [← hss_g_eq] at ht
        have ht_ge : r₁ ≤ t :=
          listInterlaces_all_ge ss_g rest_rs r₁ hint_g t (Multiset.mem_coe.mp ht)
        rcases lt_or_eq_of_le (le_trans hs₁_le ht_ge) with h | h
        · exact h
        · exfalso; subst h
          have hg0 : Polynomial.eval s₁_f g = 0 :=
            (mem_roots hg.1).mp (by rwa [hss_g_eq] at ht)
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval s₁_f) hab
          simp [eval_add, eval_mul, eval_one, (show Polynomial.eval s₁_f f = 0 from hs₁_root), hg0] at this
      have hcard : g.roots.card + 1 = (g + f).roots.card := by
        rw [hg.2, show g + f = f + g from add_comm g f, hfg_rr.2, hfg_deg, hf_deg]
      obtain ⟨u₀, hu₀_le, hu₀_root_gf⟩ :=
        exists_root_le_of_mixed hg (by rwa [add_comm] : IsRealRooted (g + f))
          hg_pos (by rw [show g + f = f + g from add_comm g f]; exact hfg_pos)
          hcop.symm hs₁_root hsmaller_gt hcard
      have hu₀_root : (f + g).IsRoot u₀ := by rwa [add_comm] at hu₀_root_gf
      have hlen_f_rest : rest_f.length + 1 = (r₁ :: rest_rs).length := by
        simp [List.length_cons] at hlen_f_alt ⊢; omega
      have hss_f_eq' : (↑rest_f : Multiset ℝ) + ↑[s₁_f] = f.roots := by
        rw [← hss_f_eq, Multiset.coe_add]
        exact Multiset.coe_eq_coe.mpr List.perm_append_comm
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist f g hf hg hf_pos hg_pos hcop ↑[s₁_f] 0
          rest_f ss_g (r₁ :: rest_rs) hlen_f_rest hlen_g hint_f_tail hint_g
          hss_f_eq' (by simp [hss_g_eq])
          (by intro r hr; simp at hr; subst hr; exact hs₁_le) (by simp)
      have hu₀_lt_r₁ : u₀ < r₁ := by
        rcases lt_or_eq_of_le (le_trans hu₀_le hs₁_le) with h | h
        · exact h
        · exfalso
          have hs_eq : s₁_f = r₁ := le_antisymm hs₁_le (h ▸ hu₀_le)
          have hfr₁ : Polynomial.eval r₁ f = 0 := by rw [← hs_eq]; exact hs₁_root
          have hgr₁ : Polynomial.eval r₁ g = 0 := by
            have := (show (f + g).IsRoot r₁ from h ▸ hu₀_root)
            simp [IsRoot.def, eval_add, hfr₁] at this; exact this
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
        exact (mem_roots hfg_rr.1).mpr
          ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hu₀_root) (hus_root u))
      have hroots_eq : (↑(u₀ :: us) : Multiset ℝ) = (f + g).roots :=
        Multiset.eq_of_le_of_card_le hsub (by
          rw [Multiset.coe_card]; simp only [List.length_cons]
          have h1 := hfg_rr.2; rw [hfg_deg, hf_deg] at h1; omega)
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by simp only [List.length_cons] at hlen_f_alt ⊢; omega,
                 ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
    · -- Case B.2: both same-degree
      have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      rcases rs_f with _ | ⟨r₁, rest_rs⟩
      · -- Degenerate: rs_f = [], all constants
        refine ⟨hfg_rr, hh, [], [], List.Pairwise.nil, List.Pairwise.nil, ?_,
          hrs_f_eq, Or.inr ⟨rfl, trivial⟩⟩
        simp only [List.length_nil] at hlen_f_alt hlen_g_alt
        have hfnd : f.natDegree = 0 := by
          have := hf.2; rw [← hss_f_eq, Multiset.coe_card] at this; omega
        have hgnd : g.natDegree = 0 := by
          have := hg.2; rw [← hss_g_eq, Multiset.coe_card] at this; omega
        have hfgnd : (f + g).natDegree = 0 := by
          have := natDegree_add_le f g; omega
        have h := hfg_rr.2; rw [hfgnd] at h
        exact (Multiset.card_eq_zero.mp h).symm
      · -- rs_f = r₁ :: rest_rs
        obtain ⟨s₁_f, rest_f, rfl⟩ : ∃ a l, ss_f = a :: l := by
          cases ss_f with | nil => simp at hlen_f_alt | cons s rest => exact ⟨s, rest, rfl⟩
        obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
          cases ss_g with | nil => simp at hlen_g_alt | cons s rest => exact ⟨s, rest, rfl⟩
        obtain ⟨hs₁f_le, hint_f_tail⟩ := halt_f
        obtain ⟨hs₁g_le, hint_g_tail⟩ := halt_g
        have hs₁f_root : f.IsRoot s₁_f :=
          (mem_roots hf.1).mp (by rw [← hss_f_eq]; simp)
        have hs₁g_root : g.IsRoot s₁_g :=
          (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
        have hf_deg : (s₁_f :: rest_f).length = f.natDegree := by
          have := hf.2; rw [← hss_f_eq, Multiset.coe_card] at this; exact this
        have hg_deg : (s₁_g :: rest_g).length = g.natDegree := by
          have := hg.2; rw [← hss_g_eq, Multiset.coe_card] at this; exact this
        have hdeg_eq : f.natDegree = g.natDegree := by
          simp [List.length_cons] at hf_deg hg_deg hlen_f_alt hlen_g_alt; omega
        have hfg_deg : (f + g).natDegree = f.natDegree := by
          apply le_antisymm
          · have h := natDegree_add_le f g; rw [max_eq_left hdeg_eq.symm.le] at h; exact h
          · apply le_natDegree_of_ne_zero; rw [coeff_add]
            have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
            have hgc : g.coeff f.natDegree = g.leadingCoeff := by
              unfold leadingCoeff; rw [← hdeg_eq]
            rw [hfc, hgc]
            exact ne_of_gt (by unfold HasPosLeadingCoeff at hf_pos hg_pos; linarith)
        have hf_roots_erase : f.roots.erase s₁_f = ↑rest_f := by
          rw [← hss_f_eq, ← Multiset.cons_coe, Multiset.erase_cons_head]
        have hg_roots_erase : g.roots.erase s₁_g = ↑rest_g := by
          rw [← hss_g_eq, ← Multiset.cons_coe, Multiset.erase_cons_head]
        have hcount_eq :
            (g.roots.erase s₁_g).countP (r₁ ≤ ·) = (f.roots.erase s₁_f).countP (r₁ ≤ ·) := by
          rw [hf_roots_erase, hg_roots_erase]
          have hcf := Multiset.countP_eq_card.mpr (fun r hr =>
            listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr))
          have hcg := Multiset.countP_eq_card.mpr (fun r hr =>
            listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr))
          rw [hcg, hcf]; simp only [Multiset.coe_card]
          simp [List.length_cons] at hlen_f_alt hlen_g_alt; omega
        have hlen_f_rest : rest_f.length + 1 = (r₁ :: rest_rs).length := by
          simp [List.length_cons] at hlen_f_alt ⊢; omega
        have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by
          simp [List.length_cons] at hlen_g_alt ⊢; omega
        have hss_f_eq' : (↑rest_f : Multiset ℝ) + ↑[s₁_f] = f.roots := by
          rw [← hss_f_eq, Multiset.coe_add]
          exact Multiset.coe_eq_coe.mpr List.perm_append_comm
        have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
          rw [← hss_g_eq, Multiset.coe_add]
          exact Multiset.coe_eq_coe.mpr List.perm_append_comm
        rcases le_or_gt s₁_f s₁_g with hsfsg | hsfsg
        · have hf_dich : ∀ r ∈ f.roots.erase s₁_f, r ≤ s₁_f ∨ r₁ ≤ r := by
            rw [hf_roots_erase]; intro r hr; right
            exact listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr)
          have hg_dich : ∀ r ∈ g.roots.erase s₁_g, r ≤ s₁_f ∨ r₁ ≤ r := by
            rw [hg_roots_erase]; intro r hr; right
            exact listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr)
          have hsign := opposite_sign_at_interlacing_roots hf hg hf_pos hg_pos
            hs₁f_le (le_refl _) hs₁f_le hsfsg hs₁g_le hsfsg
            hs₁f_root hs₁g_root hf_dich hg_dich hcount_eq
          obtain ⟨c, hcf, hcg, hc_root⟩ :=
            sum_has_root_between hsfsg hs₁f_root hs₁g_root hsign
          have hc_lt_r₁ : c < r₁ := by
            rcases lt_or_eq_of_le (le_trans hcg hs₁g_le) with h | h
            · exact h
            · exfalso
              have : s₁_g = r₁ := le_antisymm hs₁g_le (h ▸ hcg)
              have hgr₁ : Polynomial.eval r₁ g = 0 := by rw [← this]; exact hs₁g_root
              have hfr₁ : Polynomial.eval r₁ f = 0 := by
                have := (show (f + g).IsRoot r₁ from h ▸ hc_root)
                simp [IsRoot.def, eval_add, hgr₁] at this; exact this
              obtain ⟨a, b, hab⟩ := hcop
              have := congr_arg (Polynomial.eval r₁) hab
              simp [eval_add, eval_mul, eval_one, hfr₁, hgr₁] at this
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist f g hf hg hf_pos hg_pos hcop ↑[s₁_f] ↑[s₁_g]
              rest_f rest_g (r₁ :: rest_rs) hlen_f_rest hlen_g_rest
              hint_f_tail hint_g_tail hss_f_eq' hss_g_eq'
              (by intro r hr; simp at hr; subst hr; exact hs₁f_le)
              (by intro r hr; simp at hr; subst hr; exact hs₁g_le)
          have hpw : (c :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hc_lt_r₁
              (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
          have hnodup := (hpw.imp ne_of_lt : (c :: us).Nodup)
          have hsub : (↑(c :: us) : Multiset ℝ) ≤ (f + g).roots := by
            rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
            intro u hu
            exact (mem_roots hfg_rr.1).mpr
              ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hc_root) (hus_root u))
          have hroots_eq : (↑(c :: us) : Multiset ℝ) = (f + g).roots :=
            Multiset.eq_of_le_of_card_le hsub (by
              rw [Multiset.coe_card]; simp only [List.length_cons]
              simp only [List.length_cons] at hf_deg
              have h1 := hfg_rr.2; rw [hfg_deg] at h1; omega)
          exact ⟨hfg_rr, hh, c :: us, r₁ :: rest_rs,
            hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
            Or.inr ⟨by simp only [List.length_cons] at hlen_f_alt ⊢; omega,
                     ⟨le_trans hcg hs₁g_le, hus_int⟩⟩⟩
        · -- s₁_f > s₁_g
          have hsgf := le_of_lt hsfsg
          have hg_dich : ∀ r ∈ g.roots.erase s₁_g, r ≤ s₁_g ∨ r₁ ≤ r := by
            rw [hg_roots_erase]; intro r hr; right
            exact listInterlaces_all_ge rest_g rest_rs r₁ hint_g_tail r (Multiset.mem_coe.mp hr)
          have hf_dich : ∀ r ∈ f.roots.erase s₁_f, r ≤ s₁_g ∨ r₁ ≤ r := by
            rw [hf_roots_erase]; intro r hr; right
            exact listInterlaces_all_ge rest_f rest_rs r₁ hint_f_tail r (Multiset.mem_coe.mp hr)
          have hsign := opposite_sign_at_interlacing_roots hg hf hg_pos hf_pos
            hs₁g_le (le_refl _) hs₁g_le hsgf hs₁f_le hsgf
            hs₁g_root hs₁f_root hg_dich hf_dich hcount_eq.symm
          obtain ⟨c, hcg, hcf, hc_root_gf⟩ := sum_has_root_between hsgf hs₁g_root hs₁f_root
            (by linarith [mul_comm (Polynomial.eval s₁_f g) (Polynomial.eval s₁_g f)])
          have hc_root : (f + g).IsRoot c := by rwa [add_comm]
          have hc_lt_r₁ : c < r₁ := by
            rcases lt_or_eq_of_le (le_trans hcf hs₁f_le) with h | h
            · exact h
            · exfalso
              have : s₁_f = r₁ := le_antisymm hs₁f_le (h ▸ hcf)
              have hfr₁ : Polynomial.eval r₁ f = 0 := by rw [← this]; exact hs₁f_root
              have hgr₁ : Polynomial.eval r₁ g = 0 := by
                have := (show (f + g).IsRoot r₁ from h ▸ hc_root)
                simp [IsRoot.def, eval_add, hfr₁] at this; exact this
              obtain ⟨a, b, hab⟩ := hcop
              have := congr_arg (Polynomial.eval r₁) hab
              simp [eval_add, eval_mul, eval_one, hfr₁, hgr₁] at this
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist f g hf hg hf_pos hg_pos hcop ↑[s₁_f] ↑[s₁_g]
              rest_f rest_g (r₁ :: rest_rs) hlen_f_rest hlen_g_rest
              hint_f_tail hint_g_tail hss_f_eq' hss_g_eq'
              (by intro r hr; simp at hr; subst hr; exact hs₁f_le)
              (by intro r hr; simp at hr; subst hr; exact hs₁g_le)
          have hpw : (c :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hc_lt_r₁
              (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
          have hnodup := (hpw.imp ne_of_lt : (c :: us).Nodup)
          have hsub : (↑(c :: us) : Multiset ℝ) ≤ (f + g).roots := by
            rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnodup)]
            intro u hu
            exact (mem_roots hfg_rr.1).mpr
              ((List.mem_cons.mp (Multiset.mem_coe.mp hu)).elim (· ▸ hc_root) (hus_root u))
          have hroots_eq : (↑(c :: us) : Multiset ℝ) = (f + g).roots :=
            Multiset.eq_of_le_of_card_le hsub (by
              rw [Multiset.coe_card]; simp only [List.length_cons]
              simp only [List.length_cons] at hf_deg
              have h1 := hfg_rr.2; rw [hfg_deg] at h1; omega)
          exact ⟨hfg_rr, hh, c :: us, r₁ :: rest_rs,
            hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
            Or.inr ⟨by simp only [List.length_cons] at hlen_f_alt ⊢; omega,
                     ⟨le_trans hcf hs₁f_le, hus_int⟩⟩⟩

end RealRooted
