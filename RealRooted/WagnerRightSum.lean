/-
# Wagner (1): Common-right addition theorems

If f ≪ h and g ≪ h with positive leading coefficients, then (f + g) ≪ h.
Generalizes to n summands by induction.
-/
import RealRooted.WagnerX

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Polynomial Filter

noncomputable section

namespace RealRooted

set_option linter.flexible false in
section

/-! ## Wagner (1) & (2): Common interlacing under addition

The proof uses sign analysis: if f ≪ h with positive leading coefficient,
then f has alternating signs at the roots of h. Two polynomials both
interlacing h have the SAME sign pattern, so their sum does too.
By IVT, the sum has roots between consecutive roots of h.

These generalize to n summands by induction. -/

/-! ### Sign at roots: the key intermediate fact

If `f ≪ h` (differ-by-1) with `f` having positive leading coefficient,
then `f` has a definite sign at each root of `h`, alternating between
consecutive roots. Specifically, `f` does not vanish at any root of `h`
(since the roots of `f` strictly interlace those of `h`), and the sign
is determined by the leading coefficient and the position.

This means: two polynomials both interlacing `h` with positive leading
coefficients have the **same sign** at each root of `h`. -/

/-! ### Key sign lemma

If `f` and `g` both interlace `h` (differ-by-1) with positive leading
coefficients, and `f` has root `s` and `g` has root `t` with `s ≤ t`,
then `g(s) · f(t) ≤ 0`.

Uses the factorization `f(t) = lc · ∏(t - sⱼ)`: the number of negative
factors at the two evaluation points differs by 1 (odd total), giving
opposite signs. Consequence: `(f+g)` changes sign → IVT gives a root. -/

/-- A product of reals where each factor is ≥ 0 or ≤ 0 can be written as
    `(-1)^k · (nonneg)` for some k. -/
lemma exists_sign_of_prod (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x ∨ x ≤ 0) :
    ∃ k : ℕ, 0 ≤ (-1 : ℝ) ^ k * l.prod := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
    obtain ⟨k, hk⟩ := ih (fun x hx => h x (.tail _ hx))
    rcases h a (.head _) with ha | ha
    · refine ⟨k, ?_⟩
      rw [List.prod_cons]
      have : (-1 : ℝ) ^ k * (a * l.prod) = a * ((-1 : ℝ) ^ k * l.prod) := by ring
      rw [this]; exact mul_nonneg ha hk
    · refine ⟨k + 1, ?_⟩
      rw [List.prod_cons]
      have : (-1 : ℝ) ^ (k + 1) * (a * l.prod) = (-a) * ((-1 : ℝ) ^ k * l.prod) := by ring
      rw [this]; exact mul_nonneg (by linarith) hk

/-- Two products with the same "sign exponent" have a non-negative product. -/
lemma prod_mul_prod_nonneg_of_same_sign {l₁ l₂ : List ℝ}
    (h₁ : ∀ x ∈ l₁, 0 ≤ x ∨ x ≤ 0) (h₂ : ∀ x ∈ l₂, 0 ≤ x ∨ x ≤ 0)
    (k : ℕ) (hk₁ : 0 ≤ (-1 : ℝ) ^ k * l₁.prod) (hk₂ : 0 ≤ (-1 : ℝ) ^ k * l₂.prod) :
    0 ≤ l₁.prod * l₂.prod := by
  have : l₁.prod * l₂.prod = ((-1 : ℝ) ^ k * l₁.prod) * ((-1 : ℝ) ^ k * l₂.prod) *
    ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k)⁻¹ := by
    have h1 : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [this]
  apply mul_nonneg (mul_nonneg hk₁ hk₂)
  rw [← mul_pow]; simp [show (-1 : ℝ) * (-1) = 1 from by ring]

/-- A product whose factors are ≥ 0 or ≤ 0 according to a predicate `p`
    satisfies `0 ≤ (-1)^(countP p) * prod`. -/
private lemma sign_of_prod_countP (s : Multiset ℝ) (f : ℝ → ℝ) (p : ℝ → Prop) [DecidablePred p]
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
        (-f a) * ((-1 : ℝ) ^ s.countP p * (s.map f).prod) := by ring
      rw [this]; exact mul_nonneg (by linarith) ih'
    · rw [Multiset.countP_cons_of_neg _ hp]
      have hfa := hpos a (Multiset.mem_cons_self a s) hp
      have : (-1 : ℝ) ^ s.countP p * (f a * (s.map f).prod) =
        f a * ((-1 : ℝ) ^ s.countP p * (s.map f).prod) := by ring
      rw [this]; exact mul_nonneg hfa ih'

/-- If two multisets have the same count of "negative-producing" elements,
    then the product of their mapped products is non-negative. -/
lemma prod_mul_prod_nonneg_of_same_neg_count {s₁ s₂ : Multiset ℝ}
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
  have hmul := mul_nonneg h1 h2
  have hsq : (-1 : ℝ) ^ s₂.countP p * (-1 : ℝ) ^ s₂.countP p = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  nlinarith

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
    (hf_pos := by intro x hx hxfalse; exact (False.elim (hxfalse trivial)))
    (hf_neg := by intro x hx _; exact h₁ x (Multiset.mem_coe.mp hx))
    (hg_pos := by intro x hx hxfalse; exact (False.elim (hxfalse trivial)))
    (hg_neg := by intro x hx _; exact h₂ x (Multiset.mem_coe.mp hx))
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
      simp at hr
      subst hr
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
        have hlen' : rest_f.length = rest_g.length := by
          simp at hlen
          omega
        exact prod_mul_prod_nonneg_of_forall_nonpos_of_eq_length
          (by simpa [hlen']) hall_f hall_g
      · have hr_ge_b : b ≤ r := by
          rcases List.mem_cons.mp hr_tail with rfl | hr_tail'
          · exact le_rfl
          · exact listInterlaces_rs_all_ge rest_f rest_rs b hint_f_tail r hr_tail'
        have hsf_nonneg : 0 ≤ r - sf := by linarith
        have hsg_nonneg : 0 ≤ r - sg := by linarith
        have htail :
            0 ≤ (rest_f.map (r - ·)).prod * (rest_g.map (r - ·)).prod :=
          listInterlaces_prod_mul_prod_nonneg_at_mem
            (ss_f := rest_f) (ss_g := rest_g) (rs := b :: rest_rs)
            (by simp at hlen ⊢; omega) hint_f_tail hint_g_tail r (by simp [hr_tail])
        simpa [List.map, List.prod_cons, mul_assoc, mul_left_comm, mul_comm] using
          mul_nonneg (mul_nonneg hsf_nonneg hsg_nonneg) htail
  | [], [], [], hlen, hint_f, _, _, hr => by
      simp at hr
  | [], [], _ :: _ :: _, hlen, hint_f, _, _, hr => by
      simp [ListInterlaces] at hint_f
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
      simp at hr
  | sf :: rest_f, sg :: rest_g, r₁ :: rest_rs, hlen, halt_f, halt_g, r, hr => by
      obtain ⟨hsf_r₁, hint_f⟩ := halt_f
      obtain ⟨hsg_r₁, hint_g⟩ := halt_g
      have hr_ge_r₁ : r₁ ≤ r := by
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact le_rfl
        · exact listInterlaces_rs_all_ge rest_f rest_rs r₁ hint_f r hr'
      have hsf_nonneg : 0 ≤ r - sf := by linarith
      have hsg_nonneg : 0 ≤ r - sg := by linarith
      have htail :
          0 ≤ (rest_f.map (r - ·)).prod * (rest_g.map (r - ·)).prod :=
        listInterlaces_prod_mul_prod_nonneg_at_mem
          (ss_f := rest_f) (ss_g := rest_g) (rs := r₁ :: rest_rs)
          (by simp at hlen ⊢; omega) hint_f hint_g r hr
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
        · exact le_rfl
        · exact listInterlaces_rs_all_ge ss_f rest_rs r₁ hint_f r hr'
      have hsg_nonneg : 0 ≤ r - sg := by linarith
      have hlen' : ss_f.length = rest_g.length := by
        simp only [List.length_cons] at hlen
        omega
      have hbase :
          0 ≤ (ss_f.map (r - ·)).prod * (rest_g.map (r - ·)).prod :=
        listInterlaces_prod_mul_prod_nonneg_at_mem hlen' hint_f hint_g r hr
      simpa [List.map, List.prod_cons, mul_assoc, mul_left_comm, mul_comm] using
        mul_nonneg hbase hsg_nonneg
  | _, [], _, hlen, _, halt_g, _, _ => by
      simp at hlen
  | _, _ :: _, [], hlen, hint_f, halt_g, _, _ => by
      simp [ListAlternates] at halt_g

/-- In a differ-by-1 interlacing layout, evaluating at the first two right-hand
roots gives opposite-or-zero signs. -/
private lemma listInterlaces_prod_mul_prod_nonpos_at_heads :
    ∀ {ss : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ},
      ListInterlaces ss (r₁ :: r₂ :: rest) →
        (ss.map (r₁ - ·)).prod * (ss.map (r₂ - ·)).prod ≤ 0
  | s :: rest_s, r₁, r₂, rest, hint => by
      obtain ⟨hr₁s, hsr₂, htail⟩ := hint
      have hs_nonpos : (r₁ - s) * (r₂ - s) ≤ 0 := by
        nlinarith
      have htail_nonneg :
          0 ≤ (rest_s.map (r₁ - ·)).prod * (rest_s.map (r₂ - ·)).prod := by
        have hall_r₁ : ∀ x ∈ rest_s.map (r₁ - ·), x ≤ 0 := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
          have hr₂y : r₂ ≤ y := listInterlaces_all_ge rest_s rest r₂ htail y hy
          linarith
        have hall_r₂ : ∀ x ∈ rest_s.map (r₂ - ·), x ≤ 0 := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
          have hr₂y : r₂ ≤ y := listInterlaces_all_ge rest_s rest r₂ htail y hy
          linarith
        exact prod_mul_prod_nonneg_of_forall_nonpos_of_eq_length
          (by simp) hall_r₁ hall_r₂
      have hfactor :
          (List.map (fun x => r₁ - x) (s :: rest_s)).prod *
              (List.map (fun x => r₂ - x) (s :: rest_s)).prod =
            ((r₁ - s) * (r₂ - s)) *
              ((rest_s.map (r₁ - ·)).prod * (rest_s.map (r₂ - ·)).prod) := by
        simp [mul_assoc, mul_left_comm, mul_comm]
      rw [hfactor]
      exact mul_nonpos_of_nonpos_of_nonneg hs_nonpos htail_nonneg
  | [], _, _, _, hint => by
      simp [ListInterlaces] at hint

/-- In a same-degree alternating layout, evaluating at the first two right-hand
roots also gives opposite-or-zero signs. -/
private lemma listAlternates_prod_mul_prod_nonpos_at_heads :
    ∀ {ss : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ},
      ListAlternates ss (r₁ :: r₂ :: rest) →
        (ss.map (r₁ - ·)).prod * (ss.map (r₂ - ·)).prod ≤ 0
  | s :: rest_s, r₁, r₂, rest, halt => by
      obtain ⟨hsr₁, hint⟩ := halt
      have hs_nonneg : 0 ≤ (r₁ - s) * (r₂ - s) := by
        have hsr₂ : s ≤ r₂ := le_trans hsr₁ (by
          exact listInterlaces_rs_all_ge rest_s (r₂ :: rest) r₁ hint r₂ (by simp))
        nlinarith
      have htail_nonpos :
          (rest_s.map (r₁ - ·)).prod * (rest_s.map (r₂ - ·)).prod ≤ 0 :=
        listInterlaces_prod_mul_prod_nonpos_at_heads hint
      have hfactor :
          (List.map (fun x => r₁ - x) (s :: rest_s)).prod *
              (List.map (fun x => r₂ - x) (s :: rest_s)).prod =
            ((r₁ - s) * (r₂ - s)) *
              ((rest_s.map (r₁ - ·)).prod * (rest_s.map (r₂ - ·)).prod) := by
        simp [mul_assoc, mul_left_comm, mul_comm]
      rw [hfactor]
      exact mul_nonpos_of_nonneg_of_nonpos hs_nonneg htail_nonpos
  | [], _, _, _, halt => by
      simp [ListAlternates] at halt

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
lemma eval_eq_leadingCoeff_mul_prod_sub {p : ℝ[X]} (hp : IsRealRooted p) (x : ℝ) :
    p.eval x = p.leadingCoeff * (p.roots.map (x - ·)).prod := by
  have hfact := C_leadingCoeff_mul_prod_multiset_X_sub_C hp.2
  conv_lhs => rw [← hfact]
  simp only [eval_C_mul, eval_multiset_prod, Multiset.map_map, Function.comp,
    eval_sub, eval_X, eval_C]

/-- If two polynomials both precede the same right-hand polynomial with positive
leading coefficients, then they have the same sign at every root of that common
right-hand polynomial. -/
lemma eval_mul_eval_nonneg_of_prec_right {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
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
    rw [hrs_f_eq]
    exact (mem_roots hh.1).mpr hr
  rw [eval_eq_leadingCoeff_mul_prod_sub hf r, eval_eq_leadingCoeff_mul_prod_sub hg r]
  rw [← hss_f_eq, ← hss_g_eq]
  have hprod_f :
      ((↑ss_f : Multiset ℝ).map (r - ·)).prod = (ss_f.map (r - ·)).prod := rfl
  have hprod_g :
      ((↑ss_g : Multiset ℝ).map (r - ·)).prod = (ss_g.map (r - ·)).prod := rfl
  have hprod :
      0 ≤ (ss_f.map (r - ·)).prod * (ss_g.map (r - ·)).prod := by
    rcases hcase_f with ⟨hlen_f, hint_f⟩ | ⟨hlen_f, halt_f⟩
    · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g, halt_g⟩
      · have hlen : ss_f.length = ss_g.length := by omega
        exact listInterlaces_prod_mul_prod_nonneg_at_mem hlen hint_f hint_g r hr_mem_rs
      · have hlen : ss_f.length + 1 = ss_g.length := by omega
        exact listInterlaces_listAlternates_prod_mul_prod_nonneg_at_mem
          hlen hint_f halt_g r hr_mem_rs
    · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g, halt_g⟩
      · have hlen : ss_g.length + 1 = ss_f.length := by omega
        simpa [mul_comm] using
          (listInterlaces_listAlternates_prod_mul_prod_nonneg_at_mem
            hlen hint_g halt_f r hr_mem_rs)
      · have hlen : ss_f.length = ss_g.length := by omega
        exact listAlternates_prod_mul_prod_nonneg_at_mem hlen halt_f halt_g r hr_mem_rs
  have hlead : 0 ≤ f.leadingCoeff * g.leadingCoeff := mul_nonneg hf_pos.le hg_pos.le
  rw [hprod_f, hprod_g]
  have hfactor :
      f.leadingCoeff * (ss_f.map (r - ·)).prod * (g.leadingCoeff * (ss_g.map (r - ·)).prod)
        = (f.leadingCoeff * g.leadingCoeff) *
            ((ss_f.map (r - ·)).prod * (ss_g.map (r - ·)).prod) := by
    ring
  rw [hfactor]
  exact mul_nonneg hlead hprod

/-- At each root of the common right-hand polynomial, `f + g` has the same sign
as `f`. -/
lemma eval_add_mul_eval_left_nonneg_of_prec_right {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {r : ℝ} (hr : h.IsRoot r) :
    0 ≤ (f + g).eval r * f.eval r := by
  rw [Polynomial.eval_add]
  have hsign := eval_mul_eval_nonneg_of_prec_right hfh hgh hf_pos hg_pos hr
  nlinarith [sq_nonneg (f.eval r), hsign]

/-- At each root of the common right-hand polynomial, `f + g` has the same sign
as `g`. -/
lemma eval_add_mul_eval_right_nonneg_of_prec_right {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {r : ℝ} (hr : h.IsRoot r) :
    0 ≤ (f + g).eval r * g.eval r := by
  rw [Polynomial.eval_add]
  have hsign := eval_mul_eval_nonneg_of_prec_right hfh hgh hf_pos hg_pos hr
  nlinarith [sq_nonneg (g.eval r), hsign]

/-- If the sum `f + g` vanishes at a root of the common right-hand polynomial,
then both summands already vanish there. This is the key boundary-collision
reduction for the sign-based Wagner proof. -/
lemma isRoot_of_isRoot_right_of_isRoot_add {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {r : ℝ} (hr : h.IsRoot r) (hadd : (f + g).IsRoot r) :
    f.IsRoot r ∧ g.IsRoot r := by
  have hfg_nonneg := eval_mul_eval_nonneg_of_prec_right hfh hgh hf_pos hg_pos hr
  have hsum : f.eval r + g.eval r = 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.eval_add] using hadd
  have hf0 : f.eval r = 0 := by
    nlinarith
  have hg0 : g.eval r = 0 := by
    nlinarith
  exact ⟨by simpa [Polynomial.IsRoot.def] using hf0, by simpa [Polynomial.IsRoot.def] using hg0⟩

/-- A polynomial with roots arranged by a `ListInterlaces`/`ListAlternates`
layout has opposite-or-zero signs at consecutive right-hand roots. -/
private lemma eval_mul_eval_nonpos_of_roots_layout {f : ℝ[X]}
    (hf : IsRealRooted f) (hf_pos : HasPosLeadingCoeff f)
    {ss : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (hss_eq : (↑ss : Multiset ℝ) = f.roots)
    (hcase : ListInterlaces ss (r₁ :: r₂ :: rest) ∨
      ListAlternates ss (r₁ :: r₂ :: rest)) :
    f.eval r₁ * f.eval r₂ ≤ 0 := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hf r₁, eval_eq_leadingCoeff_mul_prod_sub hf r₂, ← hss_eq]
  have hprod :
      (ss.map (r₁ - ·)).prod * (ss.map (r₂ - ·)).prod ≤ 0 := by
    rcases hcase with hint | halt
    · exact listInterlaces_prod_mul_prod_nonpos_at_heads hint
    · exact listAlternates_prod_mul_prod_nonpos_at_heads halt
  have hprod_r₁ :
      ((↑ss : Multiset ℝ).map (r₁ - ·)).prod = (ss.map (r₁ - ·)).prod := rfl
  have hprod_r₂ :
      ((↑ss : Multiset ℝ).map (r₂ - ·)).prod = (ss.map (r₂ - ·)).prod := rfl
  have hfactor :
      f.leadingCoeff * (ss.map (r₁ - ·)).prod * (f.leadingCoeff * (ss.map (r₂ - ·)).prod) =
        (f.leadingCoeff * f.leadingCoeff) *
          ((ss.map (r₁ - ·)).prod * (ss.map (r₂ - ·)).prod) := by
    ring
  rw [hprod_r₁, hprod_r₂]
  rw [hfactor]
  have hlc_nonneg : 0 ≤ f.leadingCoeff * f.leadingCoeff := by
    nlinarith [hf_pos]
  exact mul_nonpos_of_nonneg_of_nonpos hlc_nonneg hprod

/-- Generic IVT bridge: opposite-or-zero endpoint signs give a real root in the
closed interval. -/
lemma exists_isRoot_between_of_eval_mul_nonpos {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b) (hsign : p.eval a * p.eval b ≤ 0) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ p.IsRoot c := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · have : p.IsRoot a := by
      rw [Polynomial.IsRoot.def]
      nlinarith [hsign]
    exact ⟨a, le_rfl, le_rfl, this⟩
  · rcases le_or_gt (p.eval a) 0 with ha | ha
    · rcases le_or_gt (p.eval b) 0 with hb | hb
      · have hzero : p.eval a = 0 ∨ p.eval b = 0 := by
          by_cases hza : p.eval a = 0
          · exact Or.inl hza
          · right
            have ha_neg : p.eval a < 0 := lt_of_le_of_ne ha hza
            nlinarith [hsign, ha_neg, hb]
        rcases hzero with hza | hzb
        · exact ⟨a, le_rfl, le_of_lt hab_lt, by simpa [Polynomial.IsRoot.def] using hza⟩
        · exact ⟨b, le_of_lt hab_lt, le_rfl, by simpa [Polynomial.IsRoot.def] using hzb⟩
      · have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
        have h0_mem : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) := ⟨ha, le_of_lt hb⟩
        obtain ⟨c, hc, hc_val⟩ := intermediate_value_Icc (le_of_lt hab_lt) hcont h0_mem
        exact ⟨c, hc.1, hc.2, hc_val⟩
    · rcases le_or_gt 0 (p.eval b) with hb | hb
      · have : p.eval b = 0 := by nlinarith
        exact ⟨b, le_of_lt hab_lt, le_rfl, by simpa [Polynomial.IsRoot.def] using this⟩
      · have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
        have h0_mem : (0 : ℝ) ∈ Set.Icc (p.eval b) (p.eval a) := ⟨le_of_lt hb, le_of_lt ha⟩
        obtain ⟨c, hc, hc_val⟩ := intermediate_value_Icc' (le_of_lt hab_lt) hcont h0_mem
        exact ⟨c, hc.1, hc.2, hc_val⟩

/-- **Sign lemma**: Given real-rooted `f`, `g` with positive leading coefficients,
    roots `s` of `f` and `t` of `g` with `s ≤ t`, both in `[a, b]`, and the
    dichotomy conditions (all other roots of `f` resp. `g` are `≤ a` or `≥ b`,
    with equal counts of roots `≥ b`), then `g(s) · f(t) ≤ 0`.

    **Note**: The dichotomy conditions hold when `s` and `t` are the *paired* j-th
    roots in the interlacing (one root of f and g per h-interval [rⱼ, rⱼ₊₁]).
    They are supplied as hypotheses so callers can verify the pairing. -/
lemma opposite_sign_at_interlacing_roots {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b s t : ℝ} (hab : a ≤ b)
    (has : a ≤ s) (hsb : s ≤ b) (hat : a ≤ t) (htb : t ≤ b)
    (hst : s ≤ t) (hfs : f.IsRoot s) (hgt : g.IsRoot t)
    (hf_dichotomy : ∀ r ∈ f.roots.erase s, r ≤ a ∨ b ≤ r)
    (hg_dichotomy : ∀ r ∈ g.roots.erase t, r ≤ a ∨ b ≤ r)
    (hcount_eq : (g.roots.erase t).countP (b ≤ ·) = (f.roots.erase s).countP (b ≤ ·)) :
    g.eval s * f.eval t ≤ 0 := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hg s,
      eval_eq_leadingCoeff_mul_prod_sub hf t]
  have hlcg := hg_pos; have hlcf := hf_pos
  unfold HasPosLeadingCoeff at hlcg hlcf
  suffices h : (g.roots.map (s - ·)).prod * (f.roots.map (t - ·)).prod ≤ 0 by
    nlinarith [mul_pos hlcg hlcf]
  have ht_mem : t ∈ g.roots := (mem_roots hg.1).mpr hgt
  have hs_mem : s ∈ f.roots := (mem_roots hf.1).mpr hfs
  rw [← Multiset.prod_map_erase (f := (s - ·)) ht_mem,
      ← Multiset.prod_map_erase (f := (t - ·)) hs_mem]
  set Pg := (Multiset.map (s - ·) (g.roots.erase t)).prod
  set Pf := (Multiset.map (t - ·) (f.roots.erase s)).prod
  have hst_neg : (s - t) * (t - s) ≤ 0 := by nlinarith [sq_nonneg (t - s)]
  -- For each element r in the erased multisets:
  -- If r ≤ a: (s - r) ≥ 0 and (t - r) ≥ 0
  -- If r ≥ b: (s - r) ≤ 0 and (t - r) ≤ 0
  -- Pg has k negative factors, Pf has k negative factors (from hcount_eq).
  -- sign(Pg) = (-1)^k, sign(Pf) = (-1)^k, so Pg * Pf has sign (-1)^{2k} ≥ 0.
  have hrest_nonneg : 0 ≤ Pg * Pf := by
    apply prod_mul_prod_nonneg_of_same_neg_count (p := (b ≤ ·))
    · intro r hr hnp; push_neg at hnp
      rcases hg_dichotomy r hr with h | h <;> linarith
    · intro r hr hp
      rcases hg_dichotomy r hr with h | h <;> linarith
    · intro r hr hnp; push_neg at hnp
      rcases hf_dichotomy r hr with h | h <;> linarith
    · intro r hr hp
      rcases hf_dichotomy r hr with h | h <;> linarith
    · exact hcount_eq
  -- Goal: (s - t) * Pg * ((t - s) * Pf) ≤ 0
  -- = (s - t) * (t - s) * (Pg * Pf) ≤ 0
  -- since (s-t)(t-s) ≤ 0 and Pg*Pf ≥ 0
  have : (s - t) * Pg * ((t - s) * Pf) = (s - t) * (t - s) * (Pg * Pf) := by ring
  rw [this]
  exact mul_nonpos_of_nonpos_of_nonneg hst_neg hrest_nonneg

/-- Between any two roots of `f+g`-interlacing-relevant polynomials,
    the sum `f+g` has a root. -/
lemma sum_has_root_between {f g : ℝ[X]}
    {s t : ℝ} (hst : s ≤ t) (hfs : f.IsRoot s) (hgt : g.IsRoot t)
    (hsign : g.eval s * f.eval t ≤ 0) :
    ∃ c, s ≤ c ∧ c ≤ t ∧ (f + g).IsRoot c := by
  rcases eq_or_lt_of_le hst with rfl | hlt
  · have : (f + g).IsRoot s := by
      rw [IsRoot.def, eval_add]; exact by rw [hfs, hgt]; ring
    exact ⟨s, le_refl _, le_refl _, this⟩
  · -- (f+g)(s) = g(s), (f+g)(t) = f(t)
    -- g(s) · f(t) ≤ 0, so they have opposite signs (or one is 0)
    have hfgs : (f + g).eval s = g.eval s := by rw [eval_add, hfs, zero_add]
    have hfgt : (f + g).eval t = f.eval t := by rw [eval_add, hgt, add_zero]
    rcases le_or_gt (g.eval s) 0 with hgs | hgs
    · rcases le_or_gt (f.eval t) 0 with hft | hft
      · -- Both ≤ 0. Since g(s) · f(t) ≤ 0, one must be ≥ 0 too, so one is 0.
        rcases eq_or_lt_of_le hgs with hgs0 | hgs'
        · exact ⟨s, le_refl _, le_of_lt hlt, by rw [IsRoot.def, hfgs, hgs0]⟩
        · have : f.eval t = 0 := by nlinarith
          exact ⟨t, le_of_lt hlt, le_refl _, by rw [IsRoot.def, hfgt, this]⟩
      · -- g(s) ≤ 0, f(t) > 0: (f+g)(s) ≤ 0 ≤ (f+g)(t), IVT
        have hcont : ContinuousOn (fun x => (f + g).eval x) (Set.Icc s t) :=
          (f + g).continuous.continuousOn
        -- (f+g)(s) = g(s) ≤ 0 ≤ f(t) = (f+g)(t), use IVT
        have h0_mem : (0 : ℝ) ∈ Set.Icc ((f+g).eval s) ((f+g).eval t) := by
          rw [hfgs, hfgt]; exact ⟨hgs, le_of_lt hft⟩
        obtain ⟨c, hc, hc_val⟩ := intermediate_value_Icc (le_of_lt hlt) hcont h0_mem
        exact ⟨c, hc.1, hc.2, hc_val⟩
    · -- g(s) > 0
      rcases le_or_gt 0 (f.eval t) with hft | hft
      · -- g(s) > 0, f(t) ≥ 0: since g(s)·f(t) ≤ 0, f(t) = 0
        have : f.eval t = 0 := by nlinarith
        exact ⟨t, le_of_lt hlt, le_refl _, by rw [IsRoot.def, hfgt, this]⟩
      · -- g(s) > 0, f(t) < 0: (f+g)(s) > 0 > (f+g)(t), IVT
        have hcont : ContinuousOn (fun x => (f + g).eval x) (Set.Icc s t) :=
          (f + g).continuous.continuousOn
        -- g(s) > 0 > f(t), so Icc goes f(t)..g(s)
        -- IVT gives Icc (eval a) (eval b), but (eval s) > 0 > (eval t)
        -- (f+g)(s) = g(s) > 0 > f(t) = (f+g)(t), use IVT'
        have h0_mem : (0 : ℝ) ∈ Set.Icc ((f+g).eval t) ((f+g).eval s) := by
          rw [hfgs, hfgt]; exact ⟨le_of_lt hft, le_of_lt hgs⟩
        obtain ⟨c, hc, hc_val⟩ := intermediate_value_Icc' (le_of_lt hlt) hcont h0_mem
        exact ⟨c, hc.1, hc.2, hc_val⟩

lemma tendsto_eval_atBot_atTop_of_posLeadingCoeff_even {p : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hdeg : 0 < p.degree) (hpar : Even p.natDegree) :
    Tendsto (fun x => p.eval x) atBot atTop := by
  have hcomp_pos : 0 ≤ (p.comp (-X)).leadingCoeff := by
    rw [comp_neg_X_leadingCoeff_eq]
    have hpow : (-1 : ℝ) ^ p.natDegree = 1 := by
      rcases hpar with ⟨k, hk⟩
      have hk' : p.natDegree = 2 * k := by omega
      rw [hk', pow_mul]
      norm_num
    unfold HasPosLeadingCoeff at hp_pos
    simpa [hpow] using hp_pos.le
  have htop :
      Tendsto (fun x => (p.comp (-X)).eval x) atTop atTop :=
    (p.comp (-X)).tendsto_atTop_of_leadingCoeff_nonneg
      (by simpa [degree_comp_neg_X] using hdeg) hcomp_pos
  convert htop.comp tendsto_neg_atBot_atTop using 1
  ext x
  simp [Polynomial.eval_comp]

lemma tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd {p : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hdeg : 0 < p.degree) (hpar : Odd p.natDegree) :
    Tendsto (fun x => p.eval x) atBot atBot := by
  have hcomp_nonpos : (p.comp (-X)).leadingCoeff ≤ 0 := by
    rw [comp_neg_X_leadingCoeff_eq]
    have hpow : (-1 : ℝ) ^ p.natDegree = -1 := by
      rcases hpar with ⟨k, hk⟩
      rw [hk, pow_add, pow_mul]
      norm_num
    unfold HasPosLeadingCoeff at hp_pos
    have hneg : -p.leadingCoeff ≤ 0 := by linarith
    simpa [hpow] using hneg
  have htop :
      Tendsto (fun x => (p.comp (-X)).eval x) atTop atBot :=
    (p.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos
      (by simpa [degree_comp_neg_X] using hdeg) hcomp_nonpos
  convert htop.comp tendsto_neg_atBot_atTop using 1
  ext x
  simp [Polynomial.eval_comp]

lemma exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot {p : ℝ[X]} {r : ℝ}
    (hr : 0 < p.eval r) (ht : Tendsto (fun x => p.eval x) atBot atBot) :
    ∃ u ≤ r, p.IsRoot u := by
  have hneg : ∀ᶠ x in atBot, p.eval x < 0 :=
    ht.eventually (Iio_mem_atBot 0)
  have hlt : ∀ᶠ x : ℝ in atBot, x < r := eventually_lt_atBot r
  obtain ⟨x, hx_lt_r, hx_neg⟩ := (hlt.and hneg).exists
  have h0 : (0 : ℝ) ∈ Set.Icc (p.eval x) (p.eval r) := ⟨le_of_lt hx_neg, le_of_lt hr⟩
  obtain ⟨u, hu, hu_root⟩ :=
    intermediate_value_Icc (le_of_lt hx_lt_r) p.continuous.continuousOn h0
  exact ⟨u, hu.2, hu_root⟩

lemma exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop {p : ℝ[X]} {r : ℝ}
    (hr : p.eval r < 0) (ht : Tendsto (fun x => p.eval x) atBot atTop) :
    ∃ u ≤ r, p.IsRoot u := by
  have hpos : ∀ᶠ x in atBot, 0 < p.eval x :=
    ht.eventually (Ioi_mem_atTop 0)
  have hlt : ∀ᶠ x : ℝ in atBot, x < r := eventually_lt_atBot r
  obtain ⟨x, hx_lt_r, hx_pos⟩ := (hlt.and hpos).exists
  have h0 : (0 : ℝ) ∈ Set.Icc (p.eval r) (p.eval x) := ⟨le_of_lt hr, le_of_lt hx_pos⟩
  obtain ⟨u, hu, hu_root⟩ :=
    intermediate_value_Icc' (le_of_lt hx_lt_r) p.continuous.continuousOn h0
  exact ⟨u, hu.2, hu_root⟩

private lemma eval_pos_of_all_roots_gt_of_even {p : ℝ[X]} {r : ℝ}
    (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 0 < p.degree) (hpar : Even p.natDegree)
    (hgt : ∀ t ∈ p.roots, r < t) :
    0 < p.eval r := by
  have ht : Tendsto (fun x => p.eval x) atBot atTop :=
    tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hp_pos hdeg hpar
  by_contra hnonpos
  rcases eq_or_lt_of_le (le_of_not_gt hnonpos) with hzero | hneg
  · have hr_root : p.IsRoot r := by simpa [Polynomial.IsRoot.def] using hzero
    exact lt_irrefl r (hgt r ((mem_roots hp.1).mpr hr_root))
  · obtain ⟨u, hu_le, hu_root⟩ := exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hneg ht
    exact not_lt_of_ge hu_le (hgt u ((mem_roots hp.1).mpr hu_root))

private lemma eval_neg_of_all_roots_gt_of_odd {p : ℝ[X]} {r : ℝ}
    (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 0 < p.degree) (hpar : Odd p.natDegree)
    (hgt : ∀ t ∈ p.roots, r < t) :
    p.eval r < 0 := by
  have ht : Tendsto (fun x => p.eval x) atBot atBot :=
    tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hp_pos hdeg hpar
  by_contra hnonneg
  rcases eq_or_lt_of_le (le_of_not_gt hnonneg) with hzero | hpos
  · have hr_root : p.IsRoot r := by simpa [eq_comm, Polynomial.IsRoot.def] using hzero
    exact lt_irrefl r (hgt r ((mem_roots hp.1).mpr hr_root))
  · obtain ⟨u, hu_le, hu_root⟩ := exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hpos ht
    exact not_lt_of_ge hu_le (hgt u ((mem_roots hp.1).mpr hu_root))

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

/-- A sign-based version of the Wagner (1) root-production helper: if the
    common right-hand roots are not roots of `f + g`, then we can produce the
    strict interlacing roots of `f + g` without assuming `f` and `g` are
    coprime. This is the more human-style hypothesis actually used in the
    interval argument. -/
private lemma wagner1_roots_exist_of_no_common_right (f g : ℝ[X])
    (hf : IsRealRooted f) (hg : IsRealRooted g)
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
      refine ⟨[], rfl, trivial, ?_, List.Pairwise.nil⟩
      intro u hu
      exact nomatch hu
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
        rw [h, Multiset.erase_cons_head]
      have hg_roots_erase : g.roots.erase sg = ↑rest_g + consumed_g := by
        have h := hss_g_eq.symm
        rw [← Multiset.cons_coe] at h
        rw [Multiset.cons_add] at h
        rw [h, Multiset.erase_cons_head]
      have hcons_f_le : ∀ r ∈ consumed_f, r ≤ a := hcons_f
      have hcons_g_le : ∀ r ∈ consumed_g, r ≤ a := hcons_g
      have hsf_root : f.IsRoot sf := by
        have : sf ∈ f.roots := by
          rw [← hss_f_eq]
          simp [Multiset.mem_add, Multiset.mem_cons]
        exact (mem_roots hf.1).mp this
      have hsg_root : g.IsRoot sg := by
        have : sg ∈ g.roots := by
          rw [← hss_g_eq]
          simp [Multiset.mem_add, Multiset.mem_cons]
        exact (mem_roots hg.1).mp this
      have hlen_f' : rest_f.length + 1 = (b :: rest_rs).length := by
        simp at hlen_f ⊢
        omega
      have hlen_g' : rest_g.length + 1 = (b :: rest_rs).length := by
        simp at hlen_g ⊢
        omega
      have hss_f_eq' : (↑rest_f : Multiset ℝ) + (sf ::ₘ consumed_f) = f.roots :=
        calc
          (↑rest_f : Multiset ℝ) + (sf ::ₘ consumed_f)
              = sf ::ₘ consumed_f + ↑rest_f := add_comm _ _
          _ = sf ::ₘ (consumed_f + ↑rest_f) := Multiset.cons_add ..
          _ = sf ::ₘ (↑rest_f + consumed_f) := by rw [add_comm consumed_f]
          _ = sf ::ₘ ↑rest_f + consumed_f := (Multiset.cons_add ..).symm
          _ = (↑(sf :: rest_f) : Multiset ℝ) + consumed_f := by simp
          _ = f.roots := hss_f_eq
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + (sg ::ₘ consumed_g) = g.roots :=
        calc
          (↑rest_g : Multiset ℝ) + (sg ::ₘ consumed_g)
              = sg ::ₘ consumed_g + ↑rest_g := add_comm _ _
          _ = sg ::ₘ (consumed_g + ↑rest_g) := Multiset.cons_add ..
          _ = sg ::ₘ (↑rest_g + consumed_g) := by rw [add_comm consumed_g]
          _ = sg ::ₘ ↑rest_g + consumed_g := (Multiset.cons_add ..).symm
          _ = (↑(sg :: rest_g) : Multiset ℝ) + consumed_g := by simp
          _ = g.roots := hss_g_eq
      have hcons_f' : ∀ r ∈ (sf ::ₘ consumed_f), r ≤ b := by
        intro r hr
        rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact hsfb
        · exact le_trans (hcons_f_le r hr) hab
      have hcons_g' : ∀ r ∈ (sg ::ₘ consumed_g), r ≤ b := by
        intro r hr
        rcases Multiset.mem_cons.mp hr with rfl | hr
        · exact hsgb
        · exact le_trans (hcons_g_le r hr) hab
      rcases eq_or_lt_of_le hab with hab_eq | hab_lt
      · have hsf_eq : sf = a := le_antisymm (hab_eq.symm ▸ hsfb) hasf
        have hsg_eq : sg = a := le_antisymm (hab_eq.symm ▸ hsgb) hasg
        exfalso
        have hsg_sf : sg = sf := hsg_eq.trans hsf_eq.symm
        have hsg_root' : g.IsRoot sf := by
          simpa [hsg_sf] using hsg_root
        exact (hno_rs a (by simp)) <| by
          rw [← hsf_eq]
          exact IsRoot.add hsf_root hsg_root'
      · have hf_dichotomy : ∀ r ∈ f.roots.erase sf, r ≤ a ∨ b ≤ r := by
          rw [hf_roots_erase]
          intro r hr
          rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
          · right
            exact listInterlaces_all_ge rest_f rest_rs b hint_f_tail r (Multiset.mem_coe.mp hr_rest)
          · left
            exact hcons_f_le r hr_cons
        have hg_dichotomy : ∀ r ∈ g.roots.erase sg, r ≤ a ∨ b ≤ r := by
          rw [hg_roots_erase]
          intro r hr
          rcases Multiset.mem_add.mp hr with hr_rest | hr_cons
          · right
            exact listInterlaces_all_ge rest_g rest_rs b hint_g_tail r (Multiset.mem_coe.mp hr_rest)
          · left
            exact hcons_g_le r hr_cons
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
          have hlens : rest_f.length = rest_g.length := by
            simp only [List.length_cons] at hlen_f hlen_g
            omega
          rw [hcg_rest, hcf_rest, hcg_cons, hcf_cons]
          simp only [Multiset.coe_card]
          omega
        rcases le_or_gt sf sg with hsfsg | hsfsg
        · have hsign := opposite_sign_at_interlacing_roots hf hg hf_pos hg_pos hab
            hasf hsfb hasg hsgb hsfsg hsf_root hsg_root hf_dichotomy hg_dichotomy hcount_eq
          obtain ⟨u, huf, hub, hufg⟩ := sum_has_root_between hsfsg hsf_root hsg_root hsign
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist_of_no_common_right f g hf hg hf_pos hg_pos
              (sf ::ₘ consumed_f) (sg ::ₘ consumed_g)
              rest_f rest_g (b :: rest_rs) hlen_f' hlen_g' hint_f_tail hint_g_tail
              hss_f_eq' hss_g_eq' hcons_f' hcons_g'
              (fun r hr => hno_rs r (.tail _ hr))
          have hu_lt_b : u < b := by
            rcases lt_or_eq_of_le (le_trans hub hsgb) with h | h
            · exact h
            · exfalso
              exact (hno_rs b (by simp)) (h ▸ hufg)
          have hus_pw' : (u :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw =>
              lt_of_lt_of_le hu_lt_b (listInterlaces_all_ge us rest_rs b hus_int w hw), hus_pw⟩
          exact ⟨u :: us, by simp [hus_len],
            ⟨le_trans hasf huf, le_trans hub hsgb, hus_int⟩,
            fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hufg) (hus_root v),
            hus_pw'⟩
        · have hsgf := le_of_lt hsfsg
          have hsign := opposite_sign_at_interlacing_roots hg hf hg_pos hf_pos hab
            hasg hsgb hasf hsfb hsgf hsg_root hsf_root hg_dichotomy hf_dichotomy
            (hcount_eq.symm)
          obtain ⟨u, hug, huf, hufg⟩ :=
            sum_has_root_between hsgf hsg_root hsf_root
              (by linarith [mul_comm (Polynomial.eval sf g) (Polynomial.eval sg f)])
          have hufg' : (f + g).IsRoot u := by
            rwa [add_comm] at hufg
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist_of_no_common_right f g hf hg hf_pos hg_pos
              (sf ::ₘ consumed_f) (sg ::ₘ consumed_g)
              rest_f rest_g (b :: rest_rs) hlen_f' hlen_g' hint_f_tail hint_g_tail
              hss_f_eq' hss_g_eq' hcons_f' hcons_g'
              (fun r hr => hno_rs r (.tail _ hr))
          have hu_lt_b : u < b := by
            rcases lt_or_eq_of_le (le_trans huf hsfb) with h | h
            · exact h
            · exfalso
              exact (hno_rs b (by simp)) (h ▸ hufg')
          have hus_pw' : (u :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw =>
              lt_of_lt_of_le hu_lt_b (listInterlaces_all_ge us rest_rs b hus_int w hw), hus_pw⟩
          exact ⟨u :: us, by simp [hus_len],
            ⟨le_trans hasg hug, le_trans huf hsfb, hus_int⟩,
            fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ hufg') (hus_root v),
            hus_pw'⟩
  | [], [], [], hlen_f, _, _, _, _, _, _, _, _ => by
      simp only [List.length_nil] at hlen_f
      omega
  | [], [], _ :: _ :: _, hlen_f, _, _, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f
      omega
  | [], _ :: _, _, hlen_f, hlen_g, _, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f hlen_g
      omega
  | _ :: _, [], _, hlen_f, hlen_g, _, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f hlen_g
      omega
  | _ :: _, _ :: _, [], hlen_f, _, _, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f
      omega
  | _ :: _, _ :: _, [_], hlen_f, _, _, _, _, _, _, _, _ => by
      simp only [List.length_nil, List.length_cons] at hlen_f
      omega

/-- If `bigger` has a root `p` below all roots of `smaller`, and `smaller + bigger`
    and `smaller + bigger` has degree one more than `smaller`, then
    `smaller + bigger` has a root ≤ p. Used for the mixed-degree cases in Wagner (1). -/
lemma exists_root_le_of_mixed {smaller bigger : ℝ[X]}
    (hsmaller : IsRealRooted smaller)
    (hsmaller_pos : HasPosLeadingCoeff smaller)
    (hsum_pos : HasPosLeadingCoeff (smaller + bigger))
    {p : ℝ} (hbigp : bigger.IsRoot p)
    (hsmaller_gt : ∀ t ∈ smaller.roots, p < t)
    (hdeg : smaller.natDegree + 1 = (smaller + bigger).natDegree) :
    ∃ u₀ : ℝ, u₀ ≤ p ∧ (smaller + bigger).IsRoot u₀ := by
  have hsum_ne : smaller + bigger ≠ 0 := by
    intro h0
    simp [HasPosLeadingCoeff, h0] at hsum_pos
  have hbig0 : bigger.eval p = 0 := hbigp
  have hsum_eval : (smaller + bigger).eval p = smaller.eval p := by
    rw [eval_add, hbig0, add_zero]
  rcases Nat.even_or_odd smaller.natDegree with hpar | hpar
  · have hsmaller_pos_eval : 0 < smaller.eval p := by
      by_cases hdeg0 : smaller.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hdeg0, eval_C]
        have hcoeff0_eq : smaller.coeff 0 = smaller.leadingCoeff := by
          rw [Polynomial.leadingCoeff, hdeg0]
        rwa [hcoeff0_eq]
      · have hdeg_pos : 0 < smaller.degree := by
          rw [degree_eq_natDegree hsmaller.1]
          exact_mod_cast Nat.pos_of_ne_zero hdeg0
        exact eval_pos_of_all_roots_gt_of_even hsmaller hsmaller_pos hdeg_pos hpar hsmaller_gt
    have hsum_deg_pos : 0 < (smaller + bigger).degree := by
      rw [degree_eq_natDegree hsum_ne]
      have : 0 < (smaller + bigger).natDegree := by
        rw [← hdeg]
        omega
      exact_mod_cast this
    have hsum_odd : Odd (smaller + bigger).natDegree := by
      rcases hpar with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hdeg, hk]
      omega
    obtain ⟨u, hu_le, hu_root⟩ :=
      exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot
        (hsum_eval ▸ hsmaller_pos_eval)
        (tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hsum_pos hsum_deg_pos hsum_odd)
    exact ⟨u, hu_le, hu_root⟩
  · have hsmaller_neg_eval : smaller.eval p < 0 := by
      have hdeg_pos : 0 < smaller.degree := by
        rw [degree_eq_natDegree hsmaller.1]
        rcases hpar with ⟨k, hk⟩
        rw [hk]
        positivity
      exact eval_neg_of_all_roots_gt_of_odd hsmaller hsmaller_pos hdeg_pos hpar hsmaller_gt
    have hsum_deg_pos : 0 < (smaller + bigger).degree := by
      rw [degree_eq_natDegree hsum_ne]
      have : 0 < (smaller + bigger).natDegree := by
        rw [← hdeg]
        omega
      exact_mod_cast this
    have hsum_even : Even (smaller + bigger).natDegree := by
      rcases hpar with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [← hdeg, hk]
      omega
    obtain ⟨u, hu_le, hu_root⟩ :=
      exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop
        (hsum_eval ▸ hsmaller_neg_eval)
        (tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hsum_pos hsum_deg_pos hsum_even)
    exact ⟨u, hu_le, hu_root⟩

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
        · exact h
        · exfalso; subst h
          have hf0 : Polynomial.eval s₁_g f = 0 :=
            (mem_roots hf.1).mp (by rwa [hss_f_eq] at ht)
          have hg0 : Polynomial.eval s₁_g g = 0 := hs₁_root
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval s₁_g) hab
          simp [eval_add, eval_mul, eval_one, hf0, hg0] at this
      obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
        exists_root_le_of_mixed hf hf_pos hfg_pos hs₁_root hsmaller_gt (by
          rw [hfg_deg, hg_deg])
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
      have hfg_deg : (f + g).natDegree = f.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_lt hf_pos
      have hfg_pos : HasPosLeadingCoeff (f + g) :=
        hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg_lt hf_pos
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
      obtain ⟨u₀, hu₀_le, hu₀_root_gf⟩ :=
        exists_root_le_of_mixed hg hg_pos
          (by rw [show g + f = f + g from add_comm g f]; exact hfg_pos)
          hs₁_root hsmaller_gt (by
            rw [show g + f = f + g from add_comm g f, hfg_deg, hf_deg])
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
        wagner1_roots_exist_of_no_common_right f g hf hg hf_pos hg_pos 0 0
          ss_f ss_g rs_f hlen_f hlen_g hint_f hint_g
          (by simp [hss_f_eq]) (by simp [hss_g_eq])
          (by simp) (by simp) hno_rs_f
      have hus_nodup : us.Nodup := hus_pw.imp ne_of_lt
      have hfg_ne : f + g ≠ 0 := by
        intro h0
        have hg_natDeg : ss_g.length = g.natDegree := by
          rw [← hg.2, ← Multiset.coe_card, hss_g_eq]
        have hdeg_eq : f.natDegree = g.natDegree := by
          have hf_natDeg : ss_f.length = f.natDegree := by
            rw [← hf.2, ← Multiset.coe_card, hss_f_eq]
          omega
        have hcoeff_ne : (f + g).coeff f.natDegree ≠ 0 := by
          rw [coeff_add]
          have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
          have hgc : g.coeff f.natDegree = g.leadingCoeff := by
            unfold leadingCoeff
            rw [← hdeg_eq]
          rw [hfc, hgc]
          exact ne_of_gt (by
            unfold HasPosLeadingCoeff at hf_pos hg_pos
            linarith)
        exact hcoeff_ne (by simpa [h0])
      have hus_sub : (↑us : Multiset ℝ) ≤ (f + g).roots := by
        rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
        intro u hu
        exact (mem_roots hfg_ne).mpr (hus_root u (Multiset.mem_coe.mp hu))
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
            rw [max_eq_left hdeg_eq.symm.le] at h
            exact h
          have hdown : f.natDegree ≤ (f + g).natDegree := by
            apply le_natDegree_of_ne_zero
            rw [coeff_add]
            have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
            have hgc : g.coeff f.natDegree = g.leadingCoeff := by
              unfold leadingCoeff
              rw [← hdeg_eq]
            rw [hfc, hgc]
            exact ne_of_gt (by
              unfold HasPosLeadingCoeff at hf_pos hg_pos
              linarith)
          exact le_antisymm hup hdown
        omega
      have hus_eq : (↑us : Multiset ℝ) = (f + g).roots := by
        apply Multiset.eq_of_le_of_card_le hus_sub
        rw [Multiset.coe_card]
        calc
          (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
          _ = us.length := hfg_natDeg
      have hfg_rr : IsRealRooted (f + g) := by
        refine ⟨hfg_ne, ?_⟩
        rw [← hus_eq, Multiset.coe_card, hfg_natDeg]
      exact ⟨hfg_rr, hh, us, rs_f,
        pairwise_le_of_listInterlaces us rs_f hus_int, hrs_f_sorted, hus_eq, hrs_f_eq,
        Or.inl ⟨by rw [hus_len]; have := hlen_f; simp at this ⊢; omega, hus_int⟩⟩
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with
        | nil => simp at hlen_f
        | cons r rs => exact ⟨r, rs, rfl⟩
      obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
        cases ss_g with
        | nil => simp at hlen_g_alt
        | cons s rest => exact ⟨s, rest, rfl⟩
      obtain ⟨hs₁_le, hint_g_tail⟩ := halt_g
      have hs₁_root : g.IsRoot s₁_g :=
        (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
      have hf_deg : ss_f.length = f.natDegree := by
        have := hf.2
        rw [← hss_f_eq, Multiset.coe_card] at this
        exact this
      have hg_deg : g.natDegree = f.natDegree + 1 := by
        have : (s₁_g :: rest_g).length = g.natDegree := by
          have := hg.2
          rw [← hss_g_eq, Multiset.coe_card] at this
          exact this
        simp [List.length_cons] at this hlen_f hlen_g_alt
        omega
      have hdeg_lt : f.natDegree < g.natDegree := by omega
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
        · exact h
        · exfalso
          subst h
          have hf0 : Polynomial.eval s₁_g f = 0 :=
            (mem_roots hf.1).mp (by rwa [hss_f_eq] at ht)
          have hsum0 : (f + g).IsRoot s₁_g := by
            rw [Polynomial.IsRoot.def, Polynomial.eval_add, hf0, hs₁_root, zero_add]
          have hs_eq : s₁_g = r₁ := le_antisymm hs₁_le ht_ge
          have hr₁_root : h.IsRoot r₁ := (mem_roots hh.1).mp (by rw [← hrs_f_eq]; simp)
          exact hno s₁_g (hs_eq ▸ hr₁_root) hsum0
      obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
        exists_root_le_of_mixed hf hf_pos hfg_pos hs₁_root hsmaller_gt (by
          rw [hfg_deg, hg_deg])
      have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by
        simp [List.length_cons] at hlen_g_alt ⊢
        omega
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
        rw [← hss_g_eq, Multiset.coe_add]
        exact Multiset.coe_eq_coe.mpr List.perm_append_comm
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist_of_no_common_right f g hf hg hf_pos hg_pos 0 ↑[s₁_g]
          ss_f rest_g (r₁ :: rest_rs) hlen_f hlen_g_rest hint_f hint_g_tail
          (by simp [hss_f_eq]) hss_g_eq' (by simp)
          (by intro r hr; simp at hr; subst hr; exact hs₁_le)
          hno_rs_f
      have hu₀_lt_r₁ : u₀ < r₁ := by
        rcases lt_or_eq_of_le (le_trans hu₀_le hs₁_le) with h | h
        · exact h
        · exfalso
          exact hno r₁ ((mem_roots hh.1).mp (by rw [← hrs_f_eq]; simp))
            (h ▸ hu₀_root)
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw =>
          lt_of_lt_of_le hu₀_lt_r₁ (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup := (hpw.imp ne_of_lt : (u₀ :: us).Nodup)
      have hfg_ne : f + g ≠ 0 := by
        intro h0
        simp [HasPosLeadingCoeff, h0] at hfg_pos
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
            _ = us.length + 1 := by rw [hus_len, hf_deg]
        simpa using hcard_le'
      have hfg_rr : IsRealRooted (f + g) := by
        refine ⟨hfg_ne, ?_⟩
        rw [← hroots_eq, Multiset.coe_card]
        simp only [List.length_cons]
        rw [hfg_deg, hg_deg, hus_len]
        omega
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by simp only [List.length_cons] at hlen_f ⊢; omega,
                 ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
  · rcases hcase_g with ⟨hlen_g, hint_g⟩ | ⟨hlen_g_alt, halt_g⟩
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      obtain ⟨r₁, rest_rs, rfl⟩ : ∃ a l, rs_f = a :: l := by
        cases rs_f with
        | nil => simp at hlen_g
        | cons r rs => exact ⟨r, rs, rfl⟩
      obtain ⟨s₁_f, rest_f, rfl⟩ : ∃ a l, ss_f = a :: l := by
        cases ss_f with
        | nil => simp at hlen_f_alt
        | cons s rest => exact ⟨s, rest, rfl⟩
      obtain ⟨hs₁_le, hint_f_tail⟩ := halt_f
      have hs₁_root : f.IsRoot s₁_f :=
        (mem_roots hf.1).mp (by rw [← hss_f_eq]; simp)
      have hg_deg : ss_g.length = g.natDegree := by
        have := hg.2
        rw [← hss_g_eq, Multiset.coe_card] at this
        exact this
      have hf_deg : f.natDegree = g.natDegree + 1 := by
        have : (s₁_f :: rest_f).length = f.natDegree := by
          have := hf.2
          rw [← hss_f_eq, Multiset.coe_card] at this
          exact this
        simp [List.length_cons] at this hlen_g hlen_f_alt
        omega
      have hdeg_lt : g.natDegree < f.natDegree := by omega
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
        · exact h
        · exfalso
          subst h
          have hg0 : Polynomial.eval s₁_f g = 0 :=
            (mem_roots hg.1).mp (by rwa [hss_g_eq] at ht)
          have hsum0 : (f + g).IsRoot s₁_f := by
            rw [Polynomial.IsRoot.def, Polynomial.eval_add, hs₁_root, hg0, add_zero]
          have hs_eq : s₁_f = r₁ := le_antisymm hs₁_le ht_ge
          have hr₁_root : h.IsRoot r₁ := (mem_roots hh.1).mp (by rw [← hrs_f_eq]; simp)
          exact hno s₁_f (hs_eq ▸ hr₁_root) hsum0
      obtain ⟨u₀, hu₀_le, hu₀_root_gf⟩ :=
        exists_root_le_of_mixed hg hg_pos
          (by rw [show g + f = f + g from add_comm g f]; exact hfg_pos)
          hs₁_root hsmaller_gt (by
            rw [show g + f = f + g from add_comm g f, hfg_deg, hf_deg])
      have hu₀_root : (f + g).IsRoot u₀ := by rwa [add_comm] at hu₀_root_gf
      have hlen_f_rest : rest_f.length + 1 = (r₁ :: rest_rs).length := by
        simp [List.length_cons] at hlen_f_alt ⊢
        omega
      have hss_f_eq' : (↑rest_f : Multiset ℝ) + ↑[s₁_f] = f.roots := by
        rw [← hss_f_eq, Multiset.coe_add]
        exact Multiset.coe_eq_coe.mpr List.perm_append_comm
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist_of_no_common_right f g hf hg hf_pos hg_pos ↑[s₁_f] 0
          rest_f ss_g (r₁ :: rest_rs) hlen_f_rest hlen_g hint_f_tail hint_g
          hss_f_eq' (by simp [hss_g_eq])
          (by intro r hr; simp at hr; subst hr; exact hs₁_le) (by simp)
          hno_rs_f
      have hu₀_lt_r₁ : u₀ < r₁ := by
        rcases lt_or_eq_of_le (le_trans hu₀_le hs₁_le) with h | h
        · exact h
        · exfalso
          exact hno r₁ ((mem_roots hh.1).mp (by rw [← hrs_f_eq]; simp))
            (h ▸ hu₀_root)
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw =>
          lt_of_lt_of_le hu₀_lt_r₁ (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup := (hpw.imp ne_of_lt : (u₀ :: us).Nodup)
      have hfg_ne : f + g ≠ 0 := by
        intro h0
        simp [HasPosLeadingCoeff, h0] at hfg_pos
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
            _ = us.length + 1 := by
              rw [← hg_deg, hus_len]
              omega
        simpa using hcard_le'
      have hfg_rr : IsRealRooted (f + g) := by
        refine ⟨hfg_ne, ?_⟩
        rw [← hroots_eq, Multiset.coe_card]
        simp only [List.length_cons]
        rw [hfg_deg, hf_deg, hus_len]
        omega
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by simp only [List.length_cons] at hlen_f_alt ⊢; omega,
                 ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
    · have hrs_eq : rs_f = rs_g := by
        apply List.Perm.eq_of_pairwise' hrs_f_sorted hrs_g_sorted
        exact Multiset.coe_eq_coe.mp (hrs_f_eq.trans hrs_g_eq.symm)
      subst hrs_eq
      rcases rs_f with _ | ⟨r₁, rest_rs⟩
      ·
        simp only [List.length_nil] at hlen_f_alt hlen_g_alt
        have hfnd : f.natDegree = 0 := by
          have := hf.2
          rw [← hss_f_eq, Multiset.coe_card] at this
          omega
        have hgnd : g.natDegree = 0 := by
          have := hg.2
          rw [← hss_g_eq, Multiset.coe_card] at this
          omega
        have hfgnd : (f + g).natDegree = 0 := by
          have := natDegree_add_le f g
          omega
        have hfg_ne : f + g ≠ 0 := by
          intro h0
          have hcoeff_ne : (f + g).coeff 0 ≠ 0 := by
            rw [coeff_add]
            have hfc : f.coeff 0 = f.leadingCoeff := by
              simpa [hfnd] using (show f.coeff f.natDegree = f.leadingCoeff from rfl)
            have hgc : g.coeff 0 = g.leadingCoeff := by
              simpa [hgnd] using (show g.coeff g.natDegree = g.leadingCoeff from rfl)
            rw [hfc, hgc]
            exact ne_of_gt (by
              unfold HasPosLeadingCoeff at hf_pos hg_pos
              linarith)
          exact hcoeff_ne (by simpa [h0])
        have hfg_rr : IsRealRooted (f + g) := by
          refine ⟨hfg_ne, ?_⟩
          have hcard_le : (f + g).roots.card ≤ 0 := by
            calc
              (f + g).roots.card ≤ (f + g).natDegree := card_roots' (f + g)
              _ = 0 := hfgnd
          omega
        refine ⟨hfg_rr, hh, [], [], List.Pairwise.nil, List.Pairwise.nil, ?_,
          hrs_f_eq, Or.inr ⟨rfl, trivial⟩⟩
        have hroots0 : (f + g).roots.card = 0 := by
          calc
            (f + g).roots.card = (f + g).natDegree := hfg_rr.2
            _ = 0 := hfgnd
        exact (Multiset.card_eq_zero.mp hroots0).symm
      · obtain ⟨s₁_f, rest_f, rfl⟩ : ∃ a l, ss_f = a :: l := by
          cases ss_f with
          | nil => simp at hlen_f_alt
          | cons s rest => exact ⟨s, rest, rfl⟩
        obtain ⟨s₁_g, rest_g, rfl⟩ : ∃ a l, ss_g = a :: l := by
          cases ss_g with
          | nil => simp at hlen_g_alt
          | cons s rest => exact ⟨s, rest, rfl⟩
        obtain ⟨hs₁f_le, hint_f_tail⟩ := halt_f
        obtain ⟨hs₁g_le, hint_g_tail⟩ := halt_g
        have hs₁f_root : f.IsRoot s₁_f :=
          (mem_roots hf.1).mp (by rw [← hss_f_eq]; simp)
        have hs₁g_root : g.IsRoot s₁_g :=
          (mem_roots hg.1).mp (by rw [← hss_g_eq]; simp)
        have hf_deg : (s₁_f :: rest_f).length = f.natDegree := by
          have := hf.2
          rw [← hss_f_eq, Multiset.coe_card] at this
          exact this
        have hg_deg : (s₁_g :: rest_g).length = g.natDegree := by
          have := hg.2
          rw [← hss_g_eq, Multiset.coe_card] at this
          exact this
        have hdeg_eq : f.natDegree = g.natDegree := by
          simp [List.length_cons] at hf_deg hg_deg hlen_f_alt hlen_g_alt
          omega
        have hfg_deg : (f + g).natDegree = f.natDegree := by
          apply le_antisymm
          · have h := natDegree_add_le f g
            rw [max_eq_left hdeg_eq.symm.le] at h
            exact h
          · apply le_natDegree_of_ne_zero
            rw [coeff_add]
            have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
            have hgc : g.coeff f.natDegree = g.leadingCoeff := by
              unfold leadingCoeff
              rw [← hdeg_eq]
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
          rw [hcg, hcf]
          simp only [Multiset.coe_card]
          simp [List.length_cons] at hlen_f_alt hlen_g_alt
          omega
        have hlen_f_rest : rest_f.length + 1 = (r₁ :: rest_rs).length := by
          simp [List.length_cons] at hlen_f_alt ⊢
          omega
        have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by
          simp [List.length_cons] at hlen_g_alt ⊢
          omega
        have hss_f_eq' : (↑rest_f : Multiset ℝ) + ↑[s₁_f] = f.roots := by
          rw [← hss_f_eq, Multiset.coe_add]
          exact Multiset.coe_eq_coe.mpr List.perm_append_comm
        have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
          rw [← hss_g_eq, Multiset.coe_add]
          exact Multiset.coe_eq_coe.mpr List.perm_append_comm
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
          have hsign := opposite_sign_at_interlacing_roots hf hg hf_pos hg_pos
            hs₁f_le (le_refl _) hs₁f_le hsfsg hs₁g_le hsfsg
            hs₁f_root hs₁g_root hf_dich hg_dich hcount_eq
          obtain ⟨c, hcf, hcg, hc_root⟩ :=
            sum_has_root_between hsfsg hs₁f_root hs₁g_root hsign
          have hc_lt_r₁ : c < r₁ := by
            rcases lt_or_eq_of_le (le_trans hcg hs₁g_le) with h | h
            · exact h
            · exfalso
              exact hno r₁ ((mem_roots hh.1).mp (by rw [← hrs_f_eq]; simp))
                (h ▸ hc_root)
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist_of_no_common_right f g hf hg hf_pos hg_pos ↑[s₁_f] ↑[s₁_g]
              rest_f rest_g (r₁ :: rest_rs) hlen_f_rest hlen_g_rest
              hint_f_tail hint_g_tail hss_f_eq' hss_g_eq'
              (by intro r hr; simp at hr; subst hr; exact hs₁f_le)
              (by intro r hr; simp at hr; subst hr; exact hs₁g_le)
              hno_rs_f
          have hpw : (c :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw =>
              lt_of_lt_of_le hc_lt_r₁ (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
          have hnodup := (hpw.imp ne_of_lt : (c :: us).Nodup)
          have hfg_ne : f + g ≠ 0 := by
            intro h0
            have hcoeff_ne : (f + g).coeff f.natDegree ≠ 0 := by
              rw [coeff_add]
              have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
              have hgc : g.coeff f.natDegree = g.leadingCoeff := by
                unfold leadingCoeff
                rw [← hdeg_eq]
              rw [hfc, hgc]
              exact ne_of_gt (by
                unfold HasPosLeadingCoeff at hf_pos hg_pos
                linarith)
            exact hcoeff_ne (by simpa [h0])
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
                _ = us.length + 1 := by
                  simp only [List.length_cons] at hf_deg
                  rw [hus_len, hf_deg]
            simpa using hcard_le'
          have hfg_rr : IsRealRooted (f + g) := by
            refine ⟨hfg_ne, ?_⟩
            rw [← hroots_eq, Multiset.coe_card]
            simp only [List.length_cons]
            simp only [List.length_cons] at hf_deg
            rw [hfg_deg, hus_len, hf_deg]
          exact ⟨hfg_rr, hh, c :: us, r₁ :: rest_rs,
            hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
            Or.inr ⟨by simp only [List.length_cons] at hlen_f_alt ⊢; omega,
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
          have hsign := opposite_sign_at_interlacing_roots hg hf hg_pos hf_pos
            hs₁g_le (le_refl _) hs₁g_le hsgf hs₁f_le hsgf
            hs₁g_root hs₁f_root hg_dich hf_dich hcount_eq.symm
          obtain ⟨c, hcg, hcf, hc_root_gf⟩ :=
            sum_has_root_between hsgf hs₁g_root hs₁f_root
              (by linarith [mul_comm (Polynomial.eval s₁_f g) (Polynomial.eval s₁_g f)])
          have hc_root : (f + g).IsRoot c := by rwa [add_comm] at hc_root_gf
          have hc_lt_r₁ : c < r₁ := by
            rcases lt_or_eq_of_le (le_trans hcf hs₁f_le) with h | h
            · exact h
            · exfalso
              exact hno r₁ ((mem_roots hh.1).mp (by rw [← hrs_f_eq]; simp))
                (h ▸ hc_root)
          obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
            wagner1_roots_exist_of_no_common_right f g hf hg hf_pos hg_pos ↑[s₁_f] ↑[s₁_g]
              rest_f rest_g (r₁ :: rest_rs) hlen_f_rest hlen_g_rest
              hint_f_tail hint_g_tail hss_f_eq' hss_g_eq'
              (by intro r hr; simp at hr; subst hr; exact hs₁f_le)
              (by intro r hr; simp at hr; subst hr; exact hs₁g_le)
              hno_rs_f
          have hpw : (c :: us).Pairwise (· < ·) :=
            List.pairwise_cons.mpr ⟨fun w hw =>
              lt_of_lt_of_le hc_lt_r₁ (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
          have hnodup := (hpw.imp ne_of_lt : (c :: us).Nodup)
          have hfg_ne : f + g ≠ 0 := by
            intro h0
            have hcoeff_ne : (f + g).coeff f.natDegree ≠ 0 := by
              rw [coeff_add]
              have hfc : f.coeff f.natDegree = f.leadingCoeff := rfl
              have hgc : g.coeff f.natDegree = g.leadingCoeff := by
                unfold leadingCoeff
                rw [← hdeg_eq]
              rw [hfc, hgc]
              exact ne_of_gt (by
                unfold HasPosLeadingCoeff at hf_pos hg_pos
                linarith)
            exact hcoeff_ne (by simpa [h0])
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
                _ = us.length + 1 := by
                  simp only [List.length_cons] at hf_deg
                  rw [hus_len, hf_deg]
            simpa using hcard_le'
          have hfg_rr : IsRealRooted (f + g) := by
            refine ⟨hfg_ne, ?_⟩
            rw [← hroots_eq, Multiset.coe_card]
            simp only [List.length_cons]
            simp only [List.length_cons] at hf_deg
            rw [hfg_deg, hus_len, hf_deg]
          exact ⟨hfg_rr, hh, c :: us, r₁ :: rest_rs,
            hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
            Or.inr ⟨by simp only [List.length_cons] at hlen_f_alt ⊢; omega,
                     ⟨le_trans hcf hs₁f_le, hus_int⟩⟩⟩

/-- A common-factor version of Wagner (1): if `d` is real-rooted and the reduced
    summands satisfy the usual coprime addition theorem, then the original
    summands also satisfy it after multiplying back by `d`. This keeps the
    high-level proof closer to the human argument "factor out the shared part,
    add the quotients, then multiply back". -/
theorem prec_add_of_prec_right_of_common_factor {d f g h : ℝ[X]}
    (hd : IsRealRooted d)
    {f' g' h' : ℝ[X]}
    (hf_def : f = d * f') (hg_def : g = d * g') (hh_def : h = d * h')
    (hfh : Prec f' h') (hgh : Prec g' h')
    (hf'_pos : HasPosLeadingCoeff f') (hg'_pos : HasPosLeadingCoeff g')
    (hfg'_rr : IsRealRooted (f' + g'))
    (hcop : IsCoprime f' g') :
    Prec (f + g) h := by
  subst hf_def hg_def hh_def
  have hsum : Prec (f' + g') h' :=
    prec_add_of_prec_right hfh hgh hf'_pos hg'_pos hfg'_rr hcop
  have hmul : Prec (d * (f' + g')) (d * h') := prec_mul_common_factor hd hsum
  simpa [left_distrib, right_distrib, mul_add, add_comm, add_left_comm, add_assoc] using hmul

/-- A common-factor version of the no-common-right Wagner theorem. This is the
factor-out-the-shared-part form of the boundary-collision argument. -/
theorem prec_add_of_prec_right_of_common_factor_of_no_common_right {d f g h : ℝ[X]}
    (hd : IsRealRooted d)
    {f' g' h' : ℝ[X]}
    (hf_def : f = d * f') (hg_def : g = d * g') (hh_def : h = d * h')
    (hfh : Prec f' h') (hgh : Prec g' h')
    (hf'_pos : HasPosLeadingCoeff f') (hg'_pos : HasPosLeadingCoeff g')
    (hno : ∀ r : ℝ, h'.IsRoot r → ¬ (f' + g').IsRoot r) :
    Prec (f + g) h := by
  subst hf_def hg_def hh_def
  have hsum : Prec (f' + g') h' :=
    prec_add_of_prec_right_of_no_common_right hfh hgh hf'_pos hg'_pos hno
  have hmul : Prec (d * (f' + g')) (d * h') := prec_mul_common_factor hd hsum
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
            simpa [hqf, hqh] using hfh
          have hgh' : Prec qg qh := by
            apply prec_of_prec_mul_X_sub_C_both r
            simpa [hqg, hqh] using hgh
          have hqf_pos : HasPosLeadingCoeff qf := by
            unfold HasPosLeadingCoeff at hf_pos ⊢
            simpa [hqf, leadingCoeff_mul, leadingCoeff_X_sub_C] using hf_pos
          have hqg_pos : HasPosLeadingCoeff qg := by
            unfold HasPosLeadingCoeff at hg_pos ⊢
            simpa [hqg, leadingCoeff_mul, leadingCoeff_X_sub_C] using hg_pos
          have hh_ne : h ≠ 0 := hfh.2.1.1
          have hqh_ne : qh ≠ 0 := by
            intro h0
            apply hh_ne
            rw [hqh, h0, mul_zero]
          have hqh_lt : qh.natDegree < n := by
            have hqh_succ : qh.natDegree + 1 = h.natDegree := by
              rw [hqh, natDegree_mul (X_sub_C_ne_zero r) hqh_ne, natDegree_X_sub_C]
              omega
            rw [hn] at hqh_succ
            omega
          have hsum' : Prec (qf + qg) qh := by
            exact ih qh.natDegree hqh_lt qf qg qh rfl hfh' hgh' hqf_pos hqg_pos
          have hmul : Prec ((X - C r) * (qf + qg)) ((X - C r) * qh) :=
            prec_mul_common_factor (isRealRooted_X_sub_C r) hsum'
          simpa [hqf, hqg, hqh, left_distrib, right_distrib, mul_add, add_comm, add_left_comm,
            add_assoc] using hmul
        · have hno : ∀ r : ℝ, h.IsRoot r → ¬ (f + g).IsRoot r := by
            intro r hr hrfg
            exact hcommon ⟨r, hr, hrfg⟩
          exact prec_add_of_prec_right_of_no_common_right hfh hgh hf_pos hg_pos hno)
  exact hP h.natDegree f g h rfl hfh hgh hf_pos hg_pos

/-- A mixed-degree version of Wagner (1): if `f` precedes `h` with degree one less,
    `g` precedes `h` with the same degree, and `f` and `g` are coprime, then
    `f + g` precedes `h`. This packages the branch needed for the derangement
    recurrence, avoiding a separate `IsRealRooted (f + g)` hypothesis. -/
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
          rw [← Multiset.coe_card, hss_g_eq, hg.2]
        have hrs_len : rs_g.length = h.natDegree := by
          rw [← Multiset.coe_card, hrs_g_eq, hh.2]
        omega
      omega
    · have hrs_eq : rs_f = rs_g := by
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
      have hf_deg : ss_f.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_f_eq, hf.2]
      have hg_deg : g.natDegree = f.natDegree + 1 := by
        have hss_len : (s₁_g :: rest_g).length = g.natDegree := by
          rw [← Multiset.coe_card, hss_g_eq, hg.2]
        omega
      have hdeg_lt : f.natDegree < g.natDegree := by omega
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
        · exact h
        · exfalso
          subst h
          have hf0 : Polynomial.eval s₁_g f = 0 :=
            (mem_roots hf.1).mp (by rwa [hss_f_eq] at ht)
          have hg0 : Polynomial.eval s₁_g g = 0 := hs₁_root
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval s₁_g) hab
          simp [eval_add, eval_mul, eval_one, hf0, hg0] at this
      obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
        exists_root_le_of_mixed hf hf_pos hfg_pos hs₁_root hsmaller_gt (by
          rw [hfg_deg, hg_deg])
      have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by
        simp [List.length_cons] at hlen_g_alt ⊢
        omega
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
        rw [← hss_g_eq, Multiset.coe_add]
        exact Multiset.coe_eq_coe.mpr List.perm_append_comm
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist f g hf hg hf_pos hg_pos hcop 0 ↑[s₁_g]
          ss_f rest_g (r₁ :: rest_rs) hlen_f hlen_g_rest hint_f hint_g_tail
          (by simp [hss_f_eq]) hss_g_eq' (by simp)
          (by
            intro r hr
            simp at hr
            subst hr
            exact hs₁_le)
      have hu₀_lt_r₁ : u₀ < r₁ := by
        rcases lt_or_eq_of_le (le_trans hu₀_le hs₁_le) with h | h
        · exact h
        · exfalso
          have hs_eq : s₁_g = r₁ := le_antisymm hs₁_le (h ▸ hu₀_le)
          have hgr₁ : Polynomial.eval r₁ g = 0 := by
            rw [← hs_eq]
            exact hs₁_root
          have hfr₁ : Polynomial.eval r₁ f = 0 := by
            have : (f + g).IsRoot r₁ := h ▸ hu₀_root
            simp [IsRoot.def, eval_add, hgr₁] at this
            exact this
          obtain ⟨a, b, hab⟩ := hcop
          have := congr_arg (Polynomial.eval r₁) hab
          simp [eval_add, eval_mul, eval_one, hfr₁, hgr₁] at this
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu₀_lt_r₁
          (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup : (u₀ :: us).Nodup := hpw.imp ne_of_lt
      have hfg_ne : f + g ≠ 0 := by
        intro h0
        simp [HasPosLeadingCoeff, h0] at hfg_pos
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
            _ = us.length + 1 := by rw [hus_len, hf_deg]
        rw [Multiset.coe_card]
        simpa using hcard_le'
      have hfg_rr : IsRealRooted (f + g) := by
        refine ⟨hfg_ne, ?_⟩
        rw [← hroots_eq, Multiset.coe_card]
        simp only [List.length_cons]
        rw [hfg_deg]
        omega
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by simp only [List.length_cons] at hlen_f ⊢; omega,
          ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
  · have hf_deg' : f.natDegree = h.natDegree := by
      have hss_len : ss_f.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_f_eq, hf.2]
      have hrs_len : rs_f.length = h.natDegree := by
        rw [← Multiset.coe_card, hrs_f_eq, hh.2]
      omega
    omega

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
          rw [← Multiset.coe_card, hss_g_eq, hg.2]
        have hrs_len : rs_g.length = h.natDegree := by
          rw [← Multiset.coe_card, hrs_g_eq, hh.2]
        omega
      omega
    · have hrs_eq : rs_f = rs_g := by
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
      have hf_deg : ss_f.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_f_eq, hf.2]
      have hg_deg : g.natDegree = f.natDegree + 1 := by
        have hss_len : (s₁_g :: rest_g).length = g.natDegree := by
          rw [← Multiset.coe_card, hss_g_eq, hg.2]
        omega
      have hdeg_lt : f.natDegree < g.natDegree := by omega
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
        · exact h
        · exfalso
          subst h
          have hf0 : Polynomial.eval s₁_g f = 0 :=
            (mem_roots hf.1).mp (by rwa [hss_f_eq] at ht)
          have hsum0 : (f + g).IsRoot s₁_g := by
            rw [Polynomial.IsRoot.def, Polynomial.eval_add, hf0, hs₁_root, zero_add]
          have hs_eq : s₁_g = r₁ := le_antisymm hs₁_le ht_ge
          have hr₁_root : h.IsRoot r₁ := (mem_roots hh.1).mp (by rw [← hrs_f_eq]; simp)
          exact hno s₁_g (hs_eq ▸ hr₁_root) hsum0
      obtain ⟨u₀, hu₀_le, hu₀_root⟩ :=
        exists_root_le_of_mixed hf hf_pos hfg_pos hs₁_root hsmaller_gt (by
          rw [hfg_deg, hg_deg])
      have hlen_g_rest : rest_g.length + 1 = (r₁ :: rest_rs).length := by
        simp [List.length_cons] at hlen_g_alt ⊢
        omega
      have hss_g_eq' : (↑rest_g : Multiset ℝ) + ↑[s₁_g] = g.roots := by
        rw [← hss_g_eq, Multiset.coe_add]
        exact Multiset.coe_eq_coe.mpr List.perm_append_comm
      obtain ⟨us, hus_len, hus_int, hus_root, hus_pw⟩ :=
        wagner1_roots_exist_of_no_common_right f g hf hg hf_pos hg_pos 0 ↑[s₁_g]
          ss_f rest_g (r₁ :: rest_rs) hlen_f hlen_g_rest hint_f hint_g_tail
          (by simp [hss_f_eq]) hss_g_eq' (by simp)
          (by
            intro r hr
            simp at hr
            subst hr
            exact hs₁_le)
          hno_rs_f
      have hu₀_lt_r₁ : u₀ < r₁ := by
        rcases lt_or_eq_of_le (le_trans hu₀_le hs₁_le) with h | h
        · exact h
        · exfalso
          exact hno r₁ ((mem_roots hh.1).mp (by rw [← hrs_f_eq]; simp))
            (h ▸ hu₀_root)
      have hpw : (u₀ :: us).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨fun w hw => lt_of_lt_of_le hu₀_lt_r₁
          (listInterlaces_all_ge us rest_rs r₁ hus_int w hw), hus_pw⟩
      have hnodup : (u₀ :: us).Nodup := hpw.imp ne_of_lt
      have hfg_ne : f + g ≠ 0 := by
        intro h0
        simp [HasPosLeadingCoeff, h0] at hfg_pos
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
            _ = us.length + 1 := by rw [hus_len, hf_deg]
        rw [Multiset.coe_card]
        simpa using hcard_le'
      have hfg_rr : IsRealRooted (f + g) := by
        refine ⟨hfg_ne, ?_⟩
        rw [← hroots_eq, Multiset.coe_card]
        simp only [List.length_cons]
        rw [hfg_deg]
        omega
      exact ⟨hfg_rr, hh, u₀ :: us, r₁ :: rest_rs,
        hpw.imp le_of_lt, hrs_f_sorted, hroots_eq, hrs_f_eq,
        Or.inr ⟨by simp only [List.length_cons] at hlen_f ⊢; omega,
          ⟨le_trans hu₀_le hs₁_le, hus_int⟩⟩⟩
  · have hf_deg' : f.natDegree = h.natDegree := by
      have hss_len : ss_f.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_f_eq, hf.2]
      have hrs_len : rs_f.length = h.natDegree := by
        rw [← Multiset.coe_card, hrs_f_eq, hh.2]
      omega
    omega

/-- A common-factor version of the mixed-degree Wagner addition theorem. -/
theorem prec_add_of_prec_right_mixed_of_natDegree_of_common_factor {d f g h : ℝ[X]}
    (hd : IsRealRooted d)
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
  have hmul : Prec (d * (f' + g')) (d * h') := prec_mul_common_factor hd hsum
  simpa [left_distrib, right_distrib, mul_add, add_comm, add_left_comm, add_assoc] using hmul

/-- A common-factor version of the mixed-degree no-common-right Wagner theorem. -/
theorem prec_add_of_prec_right_mixed_of_natDegree_of_common_factor_of_no_common_right
    {d f g h : ℝ[X]}
    (hd : IsRealRooted d)
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
  have hmul : Prec (d * (f' + g')) (d * h') := prec_mul_common_factor hd hsum
  simpa [left_distrib, right_distrib, mul_add, add_comm, add_left_comm, add_assoc] using hmul


end
end RealRooted
