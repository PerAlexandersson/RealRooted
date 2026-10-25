module

public import RealRooted.WagnerX

/-!
# Wagner sign analysis

Product signs, evaluation signs at interlacing roots, intermediate-value
bridges, and parity-controlled signs outside the root interval.
-/

@[expose] public section

open Polynomial Filter

noncomputable section

namespace RealRooted

section

/-! ## Wagner (1) & (2): Common interlacing under addition

The proof uses sign analysis: if f ≪ h with positive leading coefficient,
then f has alternating signs at the roots of h. Two polynomials both
interlacing h have the SAME sign pattern, so their sum does too.
By IVT, the sum has roots between consecutive roots of h.

These generalize to n summands by induction. -/

/-! ### Sign at roots: the key intermediate fact

If `f ≪ h` with `f` having positive leading coefficient, its evaluations
at roots of `h` obey the non-strict alternating product signs used below.
The generic `StrictInterl` predicate allows common roots, so these evaluations may
vanish; nonvanishing is used only with an explicit no-common-root hypothesis.

Thus two polynomials both preceding `h` with positive leading coefficients
have compatible non-strict signs at each root of `h`. -/

/-! ### Key sign lemma

If `f` and `g` both interlace `h` (differ-by-1) with positive leading
coefficients, and `f` has root `s` and `g` has root `t` with `s ≤ t`,
then `g(s) · f(t) ≤ 0`.

Uses the factorization `f(t) = lc · ∏(t - sⱼ)`: the number of negative
factors at the two evaluation points differs by 1 (odd total), giving
opposite signs. Consequence: `(f+g)` changes sign → IVT gives a root. -/

/-- A product whose factors are ≥ 0 or ≤ 0 according to a predicate `p`
    satisfies `0 ≤ (-1)^(countP p) * prod`. -/
private lemma sign_of_prod_countP (s : Multiset ℝ) (f : ℝ → ℝ) (p : ℝ → Prop)
    [DecidablePred p]
    (hpos : ∀ x ∈ s, ¬p x → 0 ≤ f x)
    (hneg : ∀ x ∈ s, p x → f x ≤ 0) :
    0 ≤ (-1 : ℝ) ^ (s.countP p) * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ih' := ih (fun x hx => hpos x (Multiset.mem_cons_of_mem hx))
                    (fun x hx => hneg x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.map_cons, Multiset.prod_cons]
    by_cases hp : p a
    · rw [Multiset.countP_cons_of_pos _ hp]
      have hfa := hneg a (Multiset.mem_cons_self a s) hp
      have : (-1 : ℝ) ^ (s.countP p + 1) * (f a * (s.map f).prod) =
        (-f a) * ((-1 : ℝ) ^ s.countP p * (s.map f).prod) := by grind
      rw [this]; exact mul_nonneg (by grind) ih'
    · rw [Multiset.countP_cons_of_neg _ hp]
      have hfa := hpos a (Multiset.mem_cons_self a s) hp
      have : (-1 : ℝ) ^ s.countP p * (f a * (s.map f).prod) =
        f a * ((-1 : ℝ) ^ s.countP p * (s.map f).prod) := by grind
      rw [this]; exact mul_nonneg hfa ih'

/-- If two multisets have the same count of "negative-producing" elements,
    then the product of their mapped products is non-negative. -/
private lemma prod_mul_prod_nonneg_of_same_neg_count {s₁ s₂ : Multiset ℝ}
    {f g : ℝ → ℝ} {p : ℝ → Prop} [DecidablePred p]
    (hf_pos : ∀ x ∈ s₁, ¬p x → 0 ≤ f x)
    (hf_neg : ∀ x ∈ s₁, p x → f x ≤ 0)
    (hg_pos : ∀ x ∈ s₂, ¬p x → 0 ≤ g x)
    (hg_neg : ∀ x ∈ s₂, p x → g x ≤ 0)
    (hcount : s₁.countP p = s₂.countP p) :
    0 ≤ (s₁.map f).prod * (s₂.map g).prod := by
  have h1 := sign_of_prod_countP s₁ f p hf_pos hf_neg
  have h2 := sign_of_prod_countP s₂ g p hg_pos hg_neg
  rw [hcount] at h1
  have hsq : (-1 : ℝ) ^ s₂.countP p * (-1 : ℝ) ^ s₂.countP p = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  nlinarith [mul_nonneg h1 h2]

/-- If all factors in two lists are nonpositive and the lists have the same
length, then the products have the same sign parity, so their product is
nonnegative. -/
private lemma prod_mul_prod_nonneg_of_forall_nonpos_of_eq_length
    {l₁ l₂ : List ℝ} (hlen : l₁.length = l₂.length)
    (h₁ : ∀ x ∈ l₁, x ≤ 0) (h₂ : ∀ x ∈ l₂, x ≤ 0) :
    0 ≤ l₁.prod * l₂.prod := by
  simpa using prod_mul_prod_nonneg_of_same_neg_count
    (s₁ := (↑l₁ : Multiset ℝ)) (s₂ := (↑l₂ : Multiset ℝ))
    (f := id) (g := id) (p := fun _ : ℝ => True)
    (hf_pos := by lia)
    (hf_neg := by simp_all)
    (hg_pos := by lia)
    (hg_neg := by simp_all)
    (hcount := by simp [hlen])

/-- At every root of the common right-hand list, two interlacing left-hand lists
have the same sign pattern. -/
private lemma listInterlaces_prod_mul_prod_nonneg_at_mem :
    ∀ {ss_f ss_g rs : List ℝ},
      ss_f.length = ss_g.length →
      ListInterlaces ss_f rs →
      ListInterlaces ss_g rs →
      ∀ r, r ∈ rs →
        0 ≤ (ss_f.map (r - ·)).prod * (ss_g.map (r - ·)).prod
  | [], [], [a], hlen, hint_f, hint_g, r, hr => by
      simp
  | sf :: rest_f, sg :: rest_g, a :: b :: rest_rs, hlen, hint_f, hint_g, r, hr => by
      obtain ⟨ha_sf, hsf_b, hint_f_tail⟩ := hint_f
      obtain ⟨ha_sg, hsg_b, hint_g_tail⟩ := hint_g
      rcases List.mem_cons.mp hr with rfl | hr_tail
      · have hall_f : ∀ x ∈ (sf :: rest_f).map (r - ·), x ≤ 0 := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
          have hay : r ≤ y :=
            listInterlaces_all_ge (sf :: rest_f) (b :: rest_rs) r
              ⟨ha_sf, hsf_b, hint_f_tail⟩ y hy
          linarith
        have hall_g : ∀ x ∈ (sg :: rest_g).map (r - ·), x ≤ 0 := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
          have hay : r ≤ y :=
            listInterlaces_all_ge (sg :: rest_g) (b :: rest_rs) r
              ⟨ha_sg, hsg_b, hint_g_tail⟩ y hy
          linarith
        exact prod_mul_prod_nonneg_of_forall_nonpos_of_eq_length
          (by grind) hall_f hall_g
      · have hr_ge_b : b ≤ r := by
          rcases List.mem_cons.mp hr_tail with rfl | hr_tail'
          · simp
          · exact listInterlaces_rs_all_ge rest_f rest_rs b hint_f_tail r hr_tail'
        have hsf_nonneg : 0 ≤ r - sf := by linarith
        have hsg_nonneg : 0 ≤ r - sg := by linarith
        have htail :
            0 ≤ (rest_f.map (r - ·)).prod * (rest_g.map (r - ·)).prod :=
          listInterlaces_prod_mul_prod_nonneg_at_mem
            (ss_f := rest_f) (ss_g := rest_g) (rs := b :: rest_rs)
            (by grind) hint_f_tail hint_g_tail r (by lia)
        simpa [List.map, List.prod_cons, mul_assoc, mul_left_comm, mul_comm] using
          mul_nonneg (mul_nonneg hsf_nonneg hsg_nonneg) htail
  | [], [], [], hlen, hint_f, _, _, hr => by
      simp
  | [], [], _ :: _ :: _, hlen, hint_f, _, _, hr => by
      simp
  | [], _ :: _, _, hlen, _, _, _, _ => by
      simp at hlen
  | _ :: _, [], _, hlen, _, _, _, _ => by
      simp at hlen
  | _ :: _, _ :: _, [], _, hint_f, _, _, _ => by
      simp [ListInterlaces] at hint_f
  | _ :: _, _ :: _, [_], _, hint_f, _, _, _ => by
      simp [ListInterlaces] at hint_f

/-- Same-sign version for the same-degree `ListAlternates` case. -/
private lemma listAlternates_prod_mul_prod_nonneg_at_mem :
    ∀ {ss_f ss_g rs : List ℝ},
      ss_f.length = ss_g.length →
      ListAlternates ss_f rs →
      ListAlternates ss_g rs →
      ∀ r, r ∈ rs →
        0 ≤ (ss_f.map (r - ·)).prod * (ss_g.map (r - ·)).prod
  | [], [], [], hlen, halt_f, halt_g, r, hr => by
      simp
  | sf :: rest_f, sg :: rest_g, r₁ :: rest_rs, hlen, halt_f, halt_g, r, hr => by
      obtain ⟨hsf_r₁, hint_f⟩ := halt_f
      obtain ⟨hsg_r₁, hint_g⟩ := halt_g
      have hr_ge_r₁ : r₁ ≤ r := by
        rcases List.mem_cons.mp hr with rfl | hr'
        · simp
        · exact listInterlaces_rs_all_ge rest_f rest_rs r₁ hint_f r hr'
      have hsf_nonneg : 0 ≤ r - sf := by linarith
      have hsg_nonneg : 0 ≤ r - sg := by linarith
      have htail :
          0 ≤ (rest_f.map (r - ·)).prod * (rest_g.map (r - ·)).prod :=
        listInterlaces_prod_mul_prod_nonneg_at_mem
          (ss_f := rest_f) (ss_g := rest_g) (rs := r₁ :: rest_rs)
          (by grind) hint_f hint_g r hr
      simpa [List.map, List.prod_cons, mul_assoc, mul_left_comm, mul_comm] using
        mul_nonneg (mul_nonneg hsf_nonneg hsg_nonneg) htail
  | [], _ :: _, _, hlen, _, _, _, _ => by
      simp at hlen
  | _ :: _, [], _, hlen, _, _, _, _ => by
      simp at hlen
  | _ :: _, _ :: _, [], _, halt_f, _, _, _ => by
      simp [ListAlternates] at halt_f

/-- Mixed sign version: one left list interlaces the common right list and the
other alternates with it. -/
private lemma listInterlaces_listAlternates_prod_mul_prod_nonneg_at_mem :
    ∀ {ss_f ss_g rs : List ℝ},
      ss_f.length + 1 = ss_g.length →
      ListInterlaces ss_f rs →
      ListAlternates ss_g rs →
      ∀ r, r ∈ rs →
        0 ≤ (ss_f.map (r - ·)).prod * (ss_g.map (r - ·)).prod
  | ss_f, sg :: rest_g, r₁ :: rest_rs, hlen, hint_f, halt_g, r, hr => by
      obtain ⟨hsg_r₁, hint_g⟩ := halt_g
      have hr_ge_r₁ : r₁ ≤ r := by
        rcases List.mem_cons.mp hr with rfl | hr'
        · simp
        · exact listInterlaces_rs_all_ge ss_f rest_rs r₁ hint_f r hr'
      have hsg_nonneg : 0 ≤ r - sg := by linarith
      have hlen' : ss_f.length = rest_g.length := by grind
      have hbase :
          0 ≤ (ss_f.map (r - ·)).prod * (rest_g.map (r - ·)).prod :=
        listInterlaces_prod_mul_prod_nonneg_at_mem hlen' hint_f hint_g r hr
      simpa [List.map, List.prod_cons, mul_assoc, mul_left_comm, mul_comm] using
        mul_nonneg hbase hsg_nonneg
  | _, [], _, hlen, _, halt_g, _, _ => by
      simp at hlen
  | _, _ :: _, [], hlen, hint_f, halt_g, _, _ => by
      simp [ListAlternates] at halt_g

/-! The remaining product non-negativity (`hrest_nonneg` in the sign lemma)
requires showing that after erasing one root from each of `f.roots` and `g.roots`,
the products `∏(s - remaining_g_root) · ∏(t - remaining_f_root) ≥ 0`.

This holds because:
1. Each remaining g-root `r` satisfies `r ≤ a ≤ s` or `r ≥ b ≥ t` (from interlacing)
2. Similarly for remaining f-roots
3. Both products have the same number of negative factors (= n-2-i, the number
   of intervals to the right of the current one)
4. Product of two numbers with the same sign parity is non-negative

The count equality (3) follows from the interlacing giving one root per interval. -/

/-- Evaluation of a real-rooted polynomial via its factorization. -/
@[deprecated Polynomial.Splits.eval_eq_prod_roots +typeChanged (since := "2026-10-21")]
lemma eval_eq_leadingCoeff_mul_prod_sub {p : ℝ[X]}
  (hp_splits : p.Splits) (x : ℝ) :
    p.eval x = p.leadingCoeff * (p.roots.map (x - ·)).prod :=
  hp_splits.eval_eq_prod_roots x

lemma eval_pos_of_all_roots_lt {p : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hlt : ∀ t ∈ p.roots, t < r) :
    0 < p.eval r := by
  rw [Polynomial.Splits.eval_eq_prod_roots hp_splits r]
  exact mul_pos hp_pos (Multiset.prod_pos (by simp_all))

/-- If two polynomials both precede the same right-hand polynomial with positive
leading coefficients, then they have the same sign at every root of that common
right-hand polynomial. -/
lemma eval_mul_eval_nonneg_of_strictInterl_right {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {r : ℝ} (hr : h.IsRoot r) :
    0 ≤ f.eval r * g.eval r := by
  obtain ⟨hf, hh, ss_f, rs_f, hss_f_sorted, hrs_f_sorted, hss_f_eq, hrs_f_eq, hcase_f⟩ := hfh
  obtain ⟨hg, _, ss_g, rs_g, hss_g_sorted, hrs_g_sorted, hss_g_eq, hrs_g_eq, hcase_g⟩ := hgh
  have hrs_eq : rs_f = rs_g := by
    apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
    exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
  subst hrs_eq
  have hr_mem_rs : r ∈ rs_f := by
    apply Multiset.mem_coe.mp
    simp_all
  rw [Polynomial.Splits.eval_eq_prod_roots hf.2 r, Polynomial.Splits.eval_eq_prod_roots hg.2 r]
  rw [← hss_f_eq, ← hss_g_eq]
  have hprod_f :
      ((↑ss_f : Multiset ℝ).map (r - ·)).prod = (ss_f.map (r - ·)).prod := rfl
  have hprod_g :
      ((↑ss_g : Multiset ℝ).map (r - ·)).prod = (ss_g.map (r - ·)).prod := rfl
  have hprod :
      0 ≤ (ss_f.map (r - ·)).prod * (ss_g.map (r - ·)).prod := by
    rcases hcase_f with ⟨hlen_f, hint_f⟩ | ⟨hlen_f, halt_f⟩
    · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g, halt_g⟩
      · exact listInterlaces_prod_mul_prod_nonneg_at_mem (by lia) hint_f hint_g r hr_mem_rs
      · exact listInterlaces_listAlternates_prod_mul_prod_nonneg_at_mem
          (by lia) hint_f halt_g r hr_mem_rs
    · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g, halt_g⟩
      · simpa [mul_comm] using
          (listInterlaces_listAlternates_prod_mul_prod_nonneg_at_mem
            (by lia) hint_g halt_f r hr_mem_rs)
      · exact listAlternates_prod_mul_prod_nonneg_at_mem (by lia) halt_f halt_g r hr_mem_rs
  rw [hprod_f, hprod_g]
  calc
    0 ≤ (f.leadingCoeff * g.leadingCoeff) *
        ((ss_f.map (r - ·)).prod * (ss_g.map (r - ·)).prod) :=
      mul_nonneg (mul_nonneg hf_pos.le hg_pos.le) hprod
    _ = f.leadingCoeff * (ss_f.map (r - ·)).prod *
        (g.leadingCoeff * (ss_g.map (r - ·)).prod) := by ring

/-- At each root of the common right-hand polynomial, `f + g` has the same sign
as `f`. -/
lemma eval_add_mul_eval_left_nonneg_of_strictInterl_right {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {r : ℝ} (hr : h.IsRoot r) :
    0 ≤ (f + g).eval r * f.eval r := by
  rw [Polynomial.eval_add]
  have hsign := eval_mul_eval_nonneg_of_strictInterl_right hfh hgh hf_pos hg_pos hr
  linarith [sq_nonneg (f.eval r), hsign]

/-- If the sum `f + g` vanishes at a root of the common right-hand polynomial,
then both summands already vanish there. This is the key boundary-collision
reduction for the sign-based Wagner proof. -/
lemma isRoot_of_isRoot_right_of_isRoot_add {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {r : ℝ} (hr : h.IsRoot r) (hadd : (f + g).IsRoot r) :
    f.IsRoot r ∧ g.IsRoot r := by
  have := eval_mul_eval_nonneg_of_strictInterl_right hfh hgh hf_pos hg_pos hr
  constructor <;> simp_all [Polynomial.IsRoot.def] <;> nlinarith

/-- Generic IVT bridge: opposite-or-zero endpoint signs give a real root in the
closed interval. -/
lemma exists_isRoot_between_of_eval_mul_nonpos {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b) (hsign : p.eval a * p.eval b ≤ 0) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ p.IsRoot c := by
  rcases le_total (p.eval a) (p.eval b) with hev | hev
  · obtain ⟨c, hc, hc_val⟩ := intermediate_value_Icc hab p.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) by constructor <;> nlinarith)
    exact ⟨c, hc.1, hc.2, hc_val⟩
  · obtain ⟨c, hc, hc_val⟩ := intermediate_value_Icc' hab p.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (p.eval b) (p.eval a) by constructor <;> nlinarith)
    exact ⟨c, hc.1, hc.2, hc_val⟩

/-- **Sign lemma**: Given real-rooted `f`, `g` with positive leading coefficients,
    roots `s` of `f` and `t` of `g` with `s ≤ t`, both in `[a, b]`, and the
    dichotomy conditions (all other roots of `f` resp. `g` are `≤ a` or `≥ b`,
    with equal counts of roots `≥ b`), then `g(s) · f(t) ≤ 0`.

    **Note**: The dichotomy conditions hold when `s` and `t` are the *paired* j-th
    roots in the interlacing (one root of f and g per h-interval [rⱼ, rⱼ₊₁]).
    They are supplied as hypotheses so callers can verify the pairing. -/
lemma opposite_sign_at_interlacing_roots {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b s t : ℝ}
    (has : a ≤ s) (hsb : s ≤ b) (hat : a ≤ t) (htb : t ≤ b)
    (hfs : f.IsRoot s) (hgt : g.IsRoot t)
    (hf_dichotomy : ∀ r ∈ f.roots.erase s, r ≤ a ∨ b ≤ r)
    (hg_dichotomy : ∀ r ∈ g.roots.erase t, r ≤ a ∨ b ≤ r)
    (hcount_eq : (g.roots.erase t).countP (b ≤ ·) = (f.roots.erase s).countP (b ≤ ·)) :
    g.eval s * f.eval t ≤ 0 := by
  rw [Polynomial.Splits.eval_eq_prod_roots hg_splits s,
      Polynomial.Splits.eval_eq_prod_roots hf_splits t]
  have hlcg := hg_pos; have hlcf := hf_pos
  unfold HasPosLeadingCoeff at hlcg hlcf
  suffices h : (g.roots.map (s - ·)).prod * (f.roots.map (t - ·)).prod ≤ 0 by
    nlinarith [mul_pos hlcg hlcf]
  have ht_mem : t ∈ g.roots := (mem_roots hg_ne).mpr hgt
  have hs_mem : s ∈ f.roots := (mem_roots hf_ne).mpr hfs
  rw [← Multiset.prod_map_erase (f := (s - ·)) ht_mem,
      ← Multiset.prod_map_erase (f := (t - ·)) hs_mem]
  set Pg := (Multiset.map (s - ·) (g.roots.erase t)).prod
  set Pf := (Multiset.map (t - ·) (f.roots.erase s)).prod
  have hst_neg : (s - t) * (t - s) ≤ 0 := by linarith [sq_nonneg (t - s)]
  have hrest_nonneg : 0 ≤ Pg * Pf := by
    apply prod_mul_prod_nonneg_of_same_neg_count (p := (b ≤ ·)) <;> grind
  have : (s - t) * Pg * ((t - s) * Pf) = (s - t) * (t - s) * (Pg * Pf) := by grind
  rw [this]
  exact mul_nonpos_of_nonpos_of_nonneg hst_neg hrest_nonneg

/-- Between any two roots of `f+g`-interlacing-relevant polynomials,
    the sum `f+g` has a root. -/
lemma sum_has_root_between {f g : ℝ[X]}
    {s t : ℝ} (hst : s ≤ t) (hfs : f.IsRoot s) (hgt : g.IsRoot t)
    (hsign : g.eval s * f.eval t ≤ 0) :
    ∃ c, s ≤ c ∧ c ≤ t ∧ (f + g).IsRoot c := by
  apply exists_isRoot_between_of_eval_mul_nonpos hst
  rw [Polynomial.eval_add, Polynomial.eval_add, show f.eval s = 0 from hfs,
    show g.eval t = 0 from hgt, zero_add, add_zero]
  exact hsign

lemma tendsto_eval_atBot_atTop_of_posLeadingCoeff_even {p : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hdeg : 0 < p.degree) (hpar : Even p.natDegree) :
    Tendsto (fun x => p.eval x) atBot atTop := by
  have hcomp_pos : 0 ≤ (p.comp (-X)).leadingCoeff := by
    rw [comp_neg_X_leadingCoeff_eq]
    rw [show (-1 : ℝ) ^ p.natDegree = 1 by simp_all]
    simpa using hp_pos.le
  convert ((p.comp (-X)).tendsto_atTop_of_leadingCoeff_nonneg (by simp_all) hcomp_pos).comp
    tendsto_neg_atBot_atTop using 1
  ext x
  simp [Polynomial.eval_comp]

lemma tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd {p : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hdeg : 0 < p.degree) (hpar : Odd p.natDegree) :
    Tendsto (fun x => p.eval x) atBot atBot := by
  have hcomp_nonpos : (p.comp (-X)).leadingCoeff ≤ 0 := by
    rw [comp_neg_X_leadingCoeff_eq]
    rw [show (-1 : ℝ) ^ p.natDegree = -1 by simp_all]
    simpa using hp_pos.le
  convert ((p.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos (by simp_all) hcomp_nonpos).comp
    tendsto_neg_atBot_atTop using 1
  ext x
  simp [Polynomial.eval_comp]

lemma exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot {p : ℝ[X]} {r : ℝ}
    (hr : 0 < p.eval r) (ht : Tendsto (fun x => p.eval x) atBot atBot) :
    ∃ u ≤ r, p.IsRoot u := by
  obtain ⟨x, hx_lt_r, hx_neg⟩ := ((eventually_lt_atBot r).and
    (ht.eventually (Iio_mem_atBot 0))).exists
  obtain ⟨u, hu, hu_root⟩ :=
    intermediate_value_Icc (le_of_lt hx_lt_r) p.continuous.continuousOn
      ⟨le_of_lt hx_neg, le_of_lt hr⟩
  exact ⟨u, hu.2, hu_root⟩

lemma exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop {p : ℝ[X]} {r : ℝ}
    (hr : p.eval r < 0) (ht : Tendsto (fun x => p.eval x) atBot atTop) :
    ∃ u ≤ r, p.IsRoot u := by
  obtain ⟨x, hx_lt_r, hx_pos⟩ := ((eventually_lt_atBot r).and
    (ht.eventually (Ioi_mem_atTop 0))).exists
  obtain ⟨u, hu, hu_root⟩ :=
    intermediate_value_Icc' (le_of_lt hx_lt_r) p.continuous.continuousOn
      ⟨le_of_lt hr, le_of_lt hx_pos⟩
  exact ⟨u, hu.2, hu_root⟩

lemma eval_pos_of_all_roots_gt_of_even {p : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hp_pos : HasPosLeadingCoeff p)
    (hpar : Even p.natDegree)
    (hgt : ∀ t ∈ p.roots, r < t) :
    0 < p.eval r := by
  by_cases hdeg0 : p.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg0] at hp_pos ⊢
    simpa [HasPosLeadingCoeff] using hp_pos
  · have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg0)
    have ht : Tendsto (fun x => p.eval x) atBot atTop :=
      tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hp_pos hdeg hpar
    by_contra hnonpos
    rcases eq_or_lt_of_le (le_of_not_gt hnonpos) with hzero | hneg
    · have hr_root : p.IsRoot r := by simp_all
      exact lt_irrefl r (hgt r ((mem_roots hp_ne).mpr hr_root))
    · obtain ⟨u, hu_le, hu_root⟩ := exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hneg ht
      exact not_lt_of_ge hu_le (hgt u ((mem_roots hp_ne).mpr hu_root))

lemma eval_neg_of_all_roots_gt_of_odd {p : ℝ[X]} {r : ℝ}
    (hp_ne : p ≠ 0) (hp_pos : HasPosLeadingCoeff p)
    (hpar : Odd p.natDegree)
    (hgt : ∀ t ∈ p.roots, r < t) :
    p.eval r < 0 := by
  have hdeg : 0 < p.degree := by
    have hnatdeg : 0 < p.natDegree := by grind
    exact natDegree_pos_iff_degree_pos.mp hnatdeg
  have ht : Tendsto (fun x => p.eval x) atBot atBot :=
    tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hp_pos hdeg hpar
  by_contra hnonneg
  rcases eq_or_lt_of_le (le_of_not_gt hnonneg) with hzero | hpos
  · have hr_root : p.IsRoot r := by simp_all
    exact lt_irrefl r (hgt r ((mem_roots hp_ne).mpr hr_root))
  · obtain ⟨u, hu_le, hu_root⟩ := exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hpos ht
    exact not_lt_of_ge hu_le (hgt u ((mem_roots hp_ne).mpr hu_root))

end
end RealRooted
