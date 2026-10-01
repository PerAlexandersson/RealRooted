import RealRooted.DerivativeRecurrence.Interlacing
import RealRooted.SameDegreeDerivative
import RealRooted.WagnerRightSum.Sign

/-!
# Root windows for derivative recurrences

`derivRec_interlaces` needs `A n ≤ 0` at the roots of `P n`.  When `A n ≤ 0` only
on an interval, it suffices to know that the roots of every row stay in that
interval.  For `P (n + 1) = A n * (P n)' + B n * P n` this propagates:

* if the roots of `f` are at most `U`, then `f, f' > 0` beyond `U`, so `F = A f' + B f`
  has no root beyond `U` as soon as `A ≥ 0` and `B > 0` there;
* if the roots of `f` are at least `L`, then `(-1)^d f > 0` and `(-1)^(d+1) f' ≥ 0`
  below `L` (`d = deg f`), so `F` has no root below `L` as soon as `A ≥ 0` and
  `B < 0` there.

## Main results

* `eval_pos_of_roots_le`, `neg_one_pow_mul_eval_pos_of_roots_ge`: signs beyond the roots.
* `derivRec_roots_le_step`, `derivRec_roots_ge_step`: one step of the window.
* `derivRec_interlaces_of_window`: the induction for any window predicate.
* `derivRec_interlaces_of_roots_mem_Icc`, `derivRec_interlaces_of_roots_le`: the
  windows `[L, U]` and `(-∞, U]`.
-/

open Polynomial

namespace RealRooted

section Signs

variable {p : ℝ[X]} {L U x : ℝ}

theorem eval_pos_of_roots_le (hs : p.Splits) (hpos : 0 < p.leadingCoeff)
    (h : ∀ t ∈ p.roots, t ≤ U) (hx : U < x) : 0 < p.eval x := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hs x]
  refine mul_pos hpos (Multiset.prod_pos fun y hy => ?_)
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
  linarith [h t ht]

theorem neg_one_pow_mul_eval_pos_of_roots_ge (hs : p.Splits) (hpos : 0 < p.leadingCoeff)
    (h : ∀ t ∈ p.roots, L ≤ t) (hx : x < L) : 0 < (-1) ^ p.natDegree * p.eval x := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hs x, ← card_roots_of_splits hs, mul_left_comm,
    show p.roots.card = (p.roots.map (x - ·)).card by simp, ← Multiset.prod_map_neg]
  refine mul_pos hpos (Multiset.prod_pos fun y hy => ?_)
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hz
  linarith [h t ht]

theorem derivative_eval_nonneg_of_roots_le (hs : p.Splits) (hpos : 0 < p.leadingCoeff)
    (h : ∀ t ∈ p.roots, t ≤ U) (hx : U < x) : 0 ≤ p.derivative.eval x := by
  rcases Nat.lt_or_ge p.natDegree 2 with hd | hd
  · -- `p'` is a nonnegative constant
    rw [eq_C_of_natDegree_le_zero (p := p.derivative)
      ((natDegree_derivative_le p).trans (by omega)), eval_C, coeff_derivative]
    rcases Nat.lt_or_ge p.natDegree 1 with hd1 | hd1
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
    · rw [show p.coeff (0 + 1) = p.leadingCoeff by
        rw [leadingCoeff, show p.natDegree = 1 by omega]]
      positivity
  · exact (eval_pos_of_roots_le (splits_derivative_of_two_le_natDegree hs hd)
      (HasPosLeadingCoeff.derivative hpos (by omega))
      (roots_derivative_le_of_roots_le hs hd h) hx).le

theorem derivative_neg_one_pow_mul_eval_nonneg_of_roots_ge (hs : p.Splits)
    (hpos : 0 < p.leadingCoeff) (h : ∀ t ∈ p.roots, L ≤ t) (hx : x < L) :
    0 ≤ (-1) ^ (p.natDegree + 1) * p.derivative.eval x := by
  rcases Nat.lt_or_ge p.natDegree 2 with hd | hd
  · rw [eq_C_of_natDegree_le_zero (p := p.derivative)
      ((natDegree_derivative_le p).trans (by omega)), eval_C, coeff_derivative]
    rcases Nat.lt_or_ge p.natDegree 1 with hd1 | hd1
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
    · rw [show p.coeff (0 + 1) = p.leadingCoeff by
        rw [leadingCoeff, show p.natDegree = 1 by omega], show p.natDegree = 1 by omega]
      norm_num
      positivity
  · have hpow : (-1 : ℝ) ^ (p.natDegree + 1) = (-1) ^ p.derivative.natDegree := by
      rw [natDegree_derivative, show p.natDegree + 1 = (p.natDegree - 1) + 2 by omega, pow_add]
      norm_num
    rw [hpow]
    exact (neg_one_pow_mul_eval_pos_of_roots_ge (splits_derivative_of_two_le_natDegree hs hd)
      (HasPosLeadingCoeff.derivative hpos (by omega))
      (le_roots_derivative_of_le_roots hs hd h) hx).le

end Signs

section Step

variable {f F A B : ℝ[X]} {L U : ℝ}

/-- Roots stay at most `U` when `A ≥ 0` and `B > 0` beyond `U`. -/
theorem derivRec_roots_le_step (hF : F = A * f.derivative + B * f) (hs : f.Splits)
    (hpos : 0 < f.leadingCoeff) (hU : ∀ t ∈ f.roots, t ≤ U)
    (hA : ∀ x, U < x → 0 ≤ A.eval x) (hB : ∀ x, U < x → 0 < B.eval x) :
    ∀ t ∈ F.roots, t ≤ U := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := (isRoot_of_mem_roots ht)
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  nlinarith [mul_nonneg (hA t hlt) (derivative_eval_nonneg_of_roots_le hs hpos hU hlt),
    mul_pos (hB t hlt) (eval_pos_of_roots_le hs hpos hU hlt)]

/-- Roots stay at least `L` when `A ≥ 0` and `B < 0` below `L`. -/
theorem derivRec_roots_ge_step (hF : F = A * f.derivative + B * f) (hs : f.Splits)
    (hpos : 0 < f.leadingCoeff) (hL : ∀ t ∈ f.roots, L ≤ t)
    (hA : ∀ x, x < L → 0 ≤ A.eval x) (hB : ∀ x, x < L → B.eval x < 0) :
    ∀ t ∈ F.roots, L ≤ t := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := (isRoot_of_mem_roots ht)
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  have h1 := derivative_neg_one_pow_mul_eval_nonneg_of_roots_ge hs hpos hL hlt
  have h2 := neg_one_pow_mul_eval_pos_of_roots_ge hs hpos hL hlt
  have hsq : ((-1 : ℝ) ^ f.natDegree) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  -- multiply `F(t) = 0` by `(-1)^(d+1)`
  have : (-1 : ℝ) ^ (f.natDegree + 1) * (A.eval t * f.derivative.eval t +
      B.eval t * f.eval t) = 0 := by rw [h0, mul_zero]
  rw [pow_succ] at this h1
  nlinarith [mul_nonneg (hA t hlt) h1, mul_pos (neg_pos.mpr (hB t hlt)) h2]

end Step

section Sequence

variable {P A B : ℕ → ℝ[X]} {D₀ : ℕ}

/-- Interlacing from a root window `W`: `A n ≤ 0` on `W`, and the recurrence keeps
the roots of every row in `W`. -/
theorem derivRec_interlaces_of_window (W : ℝ → Prop)
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, W x → (A n).eval x ≤ 0)
    (hW : ∀ n, (P n).Splits → (∀ t ∈ (P n).roots, W t) → ∀ t ∈ (P (n + 1)).roots, W t)
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, W t)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  have hroot : ∀ n, (∀ t ∈ (P n).roots, W t) → ∀ r, (P n).IsRoot r → (A n).eval r ≤ 0 :=
    fun n hw r hr => hA n r (hw r ((mem_roots (leadingCoeff_ne_zero.mp (hpos n).ne')).mpr hr))
  have key : ∀ n, (P n).Splits ∧ (∀ t ∈ (P n).roots, W t) ∧ Interlaces (P n) (P (n + 1)) := by
    intro n
    induction n with
    | zero =>
        refine ⟨h0, hW0, ?_⟩
        rcases Nat.eq_zero_or_pos D₀ with hD | hD
        · exact h01 hD
        · exact derivRec_interlaces_step hrec hdeg hpos 0 (hroot 0 hW0) h0 (by omega)
    | succ n ih =>
        obtain ⟨hs, hw, hi⟩ := ih
        have hw' := hW n hs hw
        exact ⟨hi.1.2, hw', derivRec_interlaces_step hrec hdeg hpos (n + 1)
          (hroot (n + 1) hw') hi.1.2 (by omega)⟩
  exact fun n => (key n).2.2

/-- Roots in `[L, U]`: `A n ≤ 0` on `[L, U]`; beyond the window `A n ≥ 0`,
with `B n > 0` above and `B n < 0` below. -/
theorem derivRec_interlaces_of_roots_mem_Icc {L U : ℝ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, L ≤ x → x ≤ U → (A n).eval x ≤ 0)
    (hAU : ∀ n x, U < x → 0 ≤ (A n).eval x) (hBU : ∀ n x, U < x → 0 < (B n).eval x)
    (hAL : ∀ n x, x < L → 0 ≤ (A n).eval x) (hBL : ∀ n x, x < L → (B n).eval x < 0)
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, L ≤ t ∧ t ≤ U)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_window (fun x => L ≤ x ∧ x ≤ U) hrec hdeg hpos
    (fun n x hx => hA n x hx.1 hx.2)
    (fun n hs hw t ht =>
      ⟨derivRec_roots_ge_step (hrec n) hs (hpos n) (fun t ht => (hw t ht).1) (hAL n) (hBL n) t ht,
        derivRec_roots_le_step (hrec n) hs (hpos n) (fun t ht => (hw t ht).2) (hAU n) (hBU n)
          t ht⟩)
    h0 hW0 h01 n

/-- Roots at most `U`: `A n ≤ 0` up to `U`; beyond it `A n ≥ 0` and `B n > 0`. -/
theorem derivRec_interlaces_of_roots_le {U : ℝ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, x ≤ U → (A n).eval x ≤ 0)
    (hAU : ∀ n x, U < x → 0 ≤ (A n).eval x) (hBU : ∀ n x, U < x → 0 < (B n).eval x)
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, t ≤ U)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_window (fun x => x ≤ U) hrec hdeg hpos hA
    (fun n hs hw => derivRec_roots_le_step (hrec n) hs (hpos n) hw (hAU n) (hBU n))
    h0 hW0 h01 n

end Sequence

section ThreeTerm

variable {P a b : ℕ → ℝ[X]} {D₀ : ℕ}

/-- Roots of `F = a f + b g` stay at most `U` when `a > 0` and `b ≥ 0` beyond `U`. -/
theorem threeTerm_roots_le_step {f g F a b : ℝ[X]} {U : ℝ} (hF : F = a * f + b * g)
    (hfs : f.Splits) (hfpos : 0 < f.leadingCoeff) (hgs : g.Splits) (hgpos : 0 < g.leadingCoeff)
    (hfU : ∀ t ∈ f.roots, t ≤ U) (hgU : ∀ t ∈ g.roots, t ≤ U)
    (ha : ∀ x, U < x → 0 < a.eval x) (hb : ∀ x, U < x → 0 ≤ b.eval x) :
    ∀ t ∈ F.roots, t ≤ U := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := isRoot_of_mem_roots ht
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  nlinarith [mul_pos (ha t hlt) (eval_pos_of_roots_le hfs hfpos hfU hlt),
    mul_nonneg (hb t hlt) (eval_pos_of_roots_le hgs hgpos hgU hlt).le]

/-- Roots of `F = a f + b g`, `deg f = deg g + 1`, stay at least `L` when `a < 0`
and `b ≥ 0` below `L`. -/
theorem threeTerm_roots_ge_step {f g F a b : ℝ[X]} {L : ℝ} (hF : F = a * f + b * g)
    (hfs : f.Splits) (hfpos : 0 < f.leadingCoeff) (hgs : g.Splits) (hgpos : 0 < g.leadingCoeff)
    (hdeg : f.natDegree = g.natDegree + 1)
    (hfL : ∀ t ∈ f.roots, L ≤ t) (hgL : ∀ t ∈ g.roots, L ≤ t)
    (ha : ∀ x, x < L → a.eval x < 0) (hb : ∀ x, x < L → 0 ≤ b.eval x) :
    ∀ t ∈ F.roots, L ≤ t := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := isRoot_of_mem_roots ht
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  have hf := neg_one_pow_mul_eval_pos_of_roots_ge hfs hfpos hfL hlt
  have hg := neg_one_pow_mul_eval_pos_of_roots_ge hgs hgpos hgL hlt
  rw [hdeg, pow_succ] at hf
  -- `(-1)^d F(t) = -a(t) · ((-1)^(d+1) f(t)) + b(t) · ((-1)^d g(t)) > 0`
  have : (-1 : ℝ) ^ g.natDegree * (a.eval t * f.eval t + b.eval t * g.eval t) = 0 := by
    rw [h0, mul_zero]
  nlinarith [mul_pos (neg_pos.mpr (ha t hlt)) hf, mul_nonneg (hb t hlt) hg.le]

/-- Interlacing of a three-term recurrence from a root window `W`. -/
theorem threeTerm_interlaces_of_window (W : ℝ → Prop)
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hb : ∀ n x, W x → (b n).eval x ≤ 0)
    (hW : ∀ n, (P n).Splits → (P (n + 1)).Splits → (∀ t ∈ (P n).roots, W t) →
      (∀ t ∈ (P (n + 1)).roots, W t) → ∀ t ∈ (P (n + 2)).roots, W t)
    (hW0 : ∀ t ∈ (P 0).roots, W t) (hW1 : ∀ t ∈ (P 1).roots, W t)
    (h01 : Interlaces (P 0) (P 1)) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  have key : ∀ n, (∀ t ∈ (P n).roots, W t) ∧ (∀ t ∈ (P (n + 1)).roots, W t) ∧
      Interlaces (P n) (P (n + 1)) := by
    intro n
    induction n with
    | zero => exact ⟨hW0, hW1, h01⟩
    | succ n ih =>
        obtain ⟨hw0, hw1, hi⟩ := ih
        have hne : P (n + 1) ≠ 0 := leadingCoeff_ne_zero.mp (hpos (n + 1)).ne'
        have hF : P (n + 2) = a n * P (n + 1) + b n * P n := hrec n
        have hprec : StrictInterl (P (n + 1)) (a n * P (n + 1) + b n * P n) :=
          strictInterl_of_interlaces_evalCoeff_nonpos hi (hpos n)
            (by rw [← hF]; exact hpos (n + 2))
            (by rw [← hF, hdeg, hdeg]; omega) (by rw [← hF, hdeg, hdeg]; omega)
            (fun r hr => hb n r (hw1 r ((mem_roots hne).mpr hr)))
        rw [← hF] at hprec
        have hi' := hprec.toInterlaces (by rw [hdeg, hdeg]; omega)
        exact ⟨hw1, hW n hi.2.1.2 hi.1.2 hw0 hw1, hi'⟩
  exact fun n => (key n).2.2

/-- Three-term interlacing with roots in `[L, U]`. -/
theorem threeTerm_interlaces_of_roots_mem_Icc {L U : ℝ}
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hb : ∀ n x, L ≤ x → x ≤ U → (b n).eval x ≤ 0)
    (haU : ∀ n x, U < x → 0 < (a n).eval x) (hbU : ∀ n x, U < x → 0 ≤ (b n).eval x)
    (haL : ∀ n x, x < L → (a n).eval x < 0) (hbL : ∀ n x, x < L → 0 ≤ (b n).eval x)
    (hW0 : ∀ t ∈ (P 0).roots, L ≤ t ∧ t ≤ U) (hW1 : ∀ t ∈ (P 1).roots, L ≤ t ∧ t ≤ U)
    (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  threeTerm_interlaces_of_window (fun x => L ≤ x ∧ x ≤ U) hrec hdeg hpos
    (fun n x hx => hb n x hx.1 hx.2)
    (fun n hs0 hs1 hw0 hw1 t ht =>
      ⟨threeTerm_roots_ge_step (hrec n) hs1 (hpos (n + 1)) hs0 (hpos n)
          (by rw [hdeg, hdeg]; omega) (fun t ht => (hw1 t ht).1) (fun t ht => (hw0 t ht).1)
          (haL n) (hbL n) t ht,
        threeTerm_roots_le_step (hrec n) hs1 (hpos (n + 1)) hs0 (hpos n)
          (fun t ht => (hw1 t ht).2) (fun t ht => (hw0 t ht).2) (haU n) (hbU n) t ht⟩)
    hW0 hW1 h01 n

/-- Three-term interlacing with roots at most `U`. -/
theorem threeTerm_interlaces_of_roots_le {U : ℝ}
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hb : ∀ n x, x ≤ U → (b n).eval x ≤ 0)
    (haU : ∀ n x, U < x → 0 < (a n).eval x) (hbU : ∀ n x, U < x → 0 ≤ (b n).eval x)
    (hW0 : ∀ t ∈ (P 0).roots, t ≤ U) (hW1 : ∀ t ∈ (P 1).roots, t ≤ U)
    (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  threeTerm_interlaces_of_window (fun x => x ≤ U) hrec hdeg hpos hb
    (fun n hs0 hs1 hw0 hw1 =>
      threeTerm_roots_le_step (hrec n) hs1 (hpos (n + 1)) hs0 (hpos n) hw1 hw0 (haU n) (hbU n))
    hW0 hW1 h01 n

end ThreeTerm

end RealRooted
