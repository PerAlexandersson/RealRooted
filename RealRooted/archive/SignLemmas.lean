/-
# Sign analysis lemmas for Wagner's lemma

Key ingredients for proving Wagner (1) and (2):
- `eval_eq_leadingCoeff_mul_prod_sub`: factored evaluation of real-rooted polynomials
- `opposite_sign_at_interlacing_roots`: sign lemma for paired interlacing roots
- `sum_has_root_between`: IVT-based root existence between sign changes
- `exists_root_le_of_mixed`: root existence for mixed-degree cases
-/
import RealRooted.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Polynomial

open Polynomial

noncomputable section

namespace RealRooted

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
lemma sign_of_prod_countP (s : Multiset ℝ) (f : ℝ → ℝ) (p : ℝ → Prop) [DecidablePred p]
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

end RealRooted
