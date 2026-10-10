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
* `derivRec_interlaces_of_windows`, `derivRec_interlaces_of_window`: the induction for
  window predicates that may depend on the row, or not.
* `derivRec_interlaces_of_roots_mem_Icc`, `derivRec_interlaces_of_roots_le`: the
  windows `[L, U]` and `(-∞, U]`; `derivRec_interlaces_of_roots_mem_Icc_mono`: the windows
  `[L n, U]` with `L` nonincreasing.
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
      ((natDegree_derivative_le p).trans (by lia)), eval_C, coeff_derivative]
    rcases Nat.lt_or_ge p.natDegree 1 with hd1 | hd1
    · rw [coeff_eq_zero_of_natDegree_lt (by lia)]; simp
    · rw [show p.coeff (0 + 1) = p.leadingCoeff by
        rw [leadingCoeff, show p.natDegree = 1 by lia]]
      positivity
  · exact (eval_pos_of_roots_le (splits_derivative_of_two_le_natDegree hs hd)
      (HasPosLeadingCoeff.derivative hpos (by lia))
      (roots_derivative_le_of_roots_le hs hd h) hx).le

theorem derivative_neg_one_pow_mul_eval_nonneg_of_roots_ge (hs : p.Splits)
    (hpos : 0 < p.leadingCoeff) (h : ∀ t ∈ p.roots, L ≤ t) (hx : x < L) :
    0 ≤ (-1) ^ (p.natDegree + 1) * p.derivative.eval x := by
  rcases Nat.lt_or_ge p.natDegree 2 with hd | hd
  · rw [eq_C_of_natDegree_le_zero (p := p.derivative)
      ((natDegree_derivative_le p).trans (by lia)), eval_C, coeff_derivative]
    rcases Nat.lt_or_ge p.natDegree 1 with hd1 | hd1
    · rw [coeff_eq_zero_of_natDegree_lt (by lia)]; simp
    · rw [show p.coeff (0 + 1) = p.leadingCoeff by
        rw [leadingCoeff, show p.natDegree = 1 by lia], show p.natDegree = 1 by lia]
      norm_num
      positivity
  · have hpow : (-1 : ℝ) ^ (p.natDegree + 1) = (-1) ^ p.derivative.natDegree := by
      rw [natDegree_derivative, show p.natDegree + 1 = (p.natDegree - 1) + 2 by lia, pow_add]
      norm_num
    rw [hpow]
    exact (neg_one_pow_mul_eval_pos_of_roots_ge (splits_derivative_of_two_le_natDegree hs hd)
      (HasPosLeadingCoeff.derivative hpos (by lia))
      (le_roots_derivative_of_le_roots hs hd h) hx).le

theorem derivative_eval_pos_of_roots_le (hs : p.Splits) (hpos : 0 < p.leadingCoeff)
    (hd : p.natDegree ≠ 0) (h : ∀ t ∈ p.roots, t ≤ U) (hx : U < x) :
    0 < p.derivative.eval x := by
  rcases Nat.lt_or_ge p.natDegree 2 with hd2 | hd2
  · rw [eq_C_of_natDegree_le_zero (p := p.derivative)
      ((natDegree_derivative_le p).trans (by lia)), eval_C, coeff_derivative,
      show p.coeff (0 + 1) = p.leadingCoeff by rw [leadingCoeff, show p.natDegree = 1 by lia]]
    norm_num
    exact hpos
  · exact eval_pos_of_roots_le (splits_derivative_of_two_le_natDegree hs hd2)
      (HasPosLeadingCoeff.derivative hpos (by lia)) (roots_derivative_le_of_roots_le hs hd2 h) hx

theorem derivative_neg_one_pow_mul_eval_pos_of_roots_ge (hs : p.Splits)
    (hpos : 0 < p.leadingCoeff) (hd : p.natDegree ≠ 0) (h : ∀ t ∈ p.roots, L ≤ t)
    (hx : x < L) : 0 < (-1) ^ (p.natDegree + 1) * p.derivative.eval x := by
  rcases Nat.lt_or_ge p.natDegree 2 with hd2 | hd2
  · rw [eq_C_of_natDegree_le_zero (p := p.derivative)
      ((natDegree_derivative_le p).trans (by lia)), eval_C, coeff_derivative,
      show p.coeff (0 + 1) = p.leadingCoeff by rw [leadingCoeff, show p.natDegree = 1 by lia],
      show p.natDegree = 1 by lia]
    norm_num
    exact hpos
  · have hpow : (-1 : ℝ) ^ (p.natDegree + 1) = (-1) ^ p.derivative.natDegree := by
      rw [natDegree_derivative, show p.natDegree + 1 = (p.natDegree - 1) + 2 by lia, pow_add]
      norm_num
    rw [hpow]
    exact neg_one_pow_mul_eval_pos_of_roots_ge (splits_derivative_of_two_le_natDegree hs hd2)
      (HasPosLeadingCoeff.derivative hpos (by lia)) (le_roots_derivative_of_le_roots hs hd2 h) hx

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

/-- Roots stay at most `U` when `A > 0` and `B ≥ 0` beyond `U`, for `f` of positive degree. -/
theorem derivRec_roots_le_step_of_pos (hF : F = A * f.derivative + B * f) (hs : f.Splits)
    (hpos : 0 < f.leadingCoeff) (hd : f.natDegree ≠ 0) (hU : ∀ t ∈ f.roots, t ≤ U)
    (hA : ∀ x, U < x → 0 < A.eval x) (hB : ∀ x, U < x → 0 ≤ B.eval x) :
    ∀ t ∈ F.roots, t ≤ U := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := (isRoot_of_mem_roots ht)
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  nlinarith [mul_pos (hA t hlt) (derivative_eval_pos_of_roots_le hs hpos hd hU hlt),
    mul_nonneg (hB t hlt) (eval_pos_of_roots_le hs hpos hU hlt).le]

/-- Roots stay at least `L` when `A > 0` and `B ≤ 0` below `L`, for `f` of positive degree. -/
theorem derivRec_roots_ge_step_of_pos (hF : F = A * f.derivative + B * f) (hs : f.Splits)
    (hpos : 0 < f.leadingCoeff) (hd : f.natDegree ≠ 0) (hL : ∀ t ∈ f.roots, L ≤ t)
    (hA : ∀ x, x < L → 0 < A.eval x) (hB : ∀ x, x < L → B.eval x ≤ 0) :
    ∀ t ∈ F.roots, L ≤ t := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := (isRoot_of_mem_roots ht)
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  have h1 := derivative_neg_one_pow_mul_eval_pos_of_roots_ge hs hpos hd hL hlt
  have h2 := neg_one_pow_mul_eval_pos_of_roots_ge hs hpos hL hlt
  have : (-1 : ℝ) ^ (f.natDegree + 1) * (A.eval t * f.derivative.eval t +
      B.eval t * f.eval t) = 0 := by rw [h0, mul_zero]
  rw [pow_succ] at this h1
  nlinarith [mul_pos (hA t hlt) h1, mul_nonneg (neg_nonneg.mpr (hB t hlt)) h2.le]

end Step

section Sequence

variable {P A B : ℕ → ℝ[X]} {D₀ : ℕ}

/-- Interlacing from root windows `W n` that may depend on the row: `A n ≤ 0` on `W n`, and
the recurrence moves the roots of each row from `W n` into `W (n + 1)`. -/
theorem derivRec_interlaces_of_windows (W : ℕ → ℝ → Prop)
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, W n x → (A n).eval x ≤ 0)
    (hW : ∀ n, (P n).Splits → (∀ t ∈ (P n).roots, W n t) → ∀ t ∈ (P (n + 1)).roots,
      W (n + 1) t)
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, W 0 t)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  have hroot : ∀ n, (∀ t ∈ (P n).roots, W n t) → ∀ r, (P n).IsRoot r → (A n).eval r ≤ 0 :=
    fun n hw r hr => hA n r (hw r ((mem_roots (leadingCoeff_ne_zero.mp (hpos n).ne')).mpr hr))
  have key : ∀ n, (P n).Splits ∧ (∀ t ∈ (P n).roots, W n t) ∧ Interlaces (P n) (P (n + 1)) := by
    intro n
    induction n with
    | zero =>
        refine ⟨h0, hW0, ?_⟩
        rcases Nat.eq_zero_or_pos D₀ with hD | hD
        · exact h01 hD
        · exact derivRec_interlaces_step hrec hdeg hpos 0 (hroot 0 hW0) h0 (by lia)
    | succ n ih =>
        obtain ⟨hs, hw, hi⟩ := ih
        have hw' := hW n hs hw
        exact ⟨hi.1.2, hw', derivRec_interlaces_step hrec hdeg hpos (n + 1)
          (hroot (n + 1) hw') hi.1.2 (by lia)⟩
  exact fun n => (key n).2.2

/-- Interlacing from a root window `W`: `A n ≤ 0` on `W`, and the recurrence keeps
the roots of every row in `W`. -/
theorem derivRec_interlaces_of_window (W : ℝ → Prop)
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, W x → (A n).eval x ≤ 0)
    (hW : ∀ n, (P n).Splits → (∀ t ∈ (P n).roots, W t) → ∀ t ∈ (P (n + 1)).roots, W t)
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, W t)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) :
    ∀ n, Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_windows (fun _ => W) hrec hdeg hpos hA hW h0 hW0 h01

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

/-- Roots in `[L, U]` for rows of positive degree: `A n ≤ 0` on `[L, U]`, and beyond the
window `A n > 0`, with `B n ≥ 0` above and `B n ≤ 0` below; `B n` may vanish there, as for
`P (n + 1) = X (1 + X) P n'`. -/
theorem derivRec_interlaces_of_roots_mem_Icc_of_pos {L U : ℝ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n) (hD : D₀ ≠ 0)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, L ≤ x → x ≤ U → (A n).eval x ≤ 0)
    (hAU : ∀ n x, U < x → 0 < (A n).eval x) (hBU : ∀ n x, U < x → 0 ≤ (B n).eval x)
    (hAL : ∀ n x, x < L → 0 < (A n).eval x) (hBL : ∀ n x, x < L → (B n).eval x ≤ 0)
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, L ≤ t ∧ t ≤ U) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_window (fun x => L ≤ x ∧ x ≤ U) hrec hdeg hpos
    (fun n x hx => hA n x hx.1 hx.2)
    (fun n hs hw t ht =>
      ⟨derivRec_roots_ge_step_of_pos (hrec n) hs (hpos n) (by rw [hdeg]; lia)
          (fun t ht => (hw t ht).1) (hAL n) (hBL n) t ht,
        derivRec_roots_le_step_of_pos (hrec n) hs (hpos n) (by rw [hdeg]; lia)
          (fun t ht => (hw t ht).2) (hAU n) (hBU n) t ht⟩)
    h0 hW0 (fun h => absurd h hD) n

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

/-- Roots in `[L n, U]` with a nonincreasing lower bound `L`: `A n ≤ 0` on `[L n, U]`, and the
plain sign conditions beyond `U` and below `L (n + 1)`. -/
theorem derivRec_interlaces_of_roots_mem_Icc_mono {L : ℕ → ℝ} {U : ℝ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hL : ∀ n, L (n + 1) ≤ L n)
    (hA : ∀ n x, L n ≤ x → x ≤ U → (A n).eval x ≤ 0)
    (hAU : ∀ n x, U < x → 0 ≤ (A n).eval x) (hBU : ∀ n x, U < x → 0 < (B n).eval x)
    (hAL : ∀ n x, x < L (n + 1) → 0 ≤ (A n).eval x)
    (hBL : ∀ n x, x < L (n + 1) → (B n).eval x < 0)
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, L 0 ≤ t ∧ t ≤ U)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_windows (fun n x => L n ≤ x ∧ x ≤ U) hrec hdeg hpos
    (fun n x hx => hA n x hx.1 hx.2)
    (fun n hs hw t ht =>
      ⟨derivRec_roots_ge_step (hrec n) hs (hpos n) (fun t ht => (hL n).trans (hw t ht).1)
          (hAL n) (hBL n) t ht,
        derivRec_roots_le_step (hrec n) hs (hpos n) (fun t ht => (hw t ht).2) (hAU n) (hBU n)
          t ht⟩)
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
            (by rw [← hF, hdeg, hdeg]; lia) (by rw [← hF, hdeg, hdeg]; lia)
            (fun r hr => hb n r (hw1 r ((mem_roots hne).mpr hr)))
        rw [← hF] at hprec
        have hi' := hprec.toInterlaces (by rw [hdeg, hdeg]; lia)
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
          (by rw [hdeg, hdeg]; lia) (fun t ht => (hw1 t ht).1) (fun t ht => (hw0 t ht).1)
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

/-- Interlaced root lists `r₁ ≤ s₁ ≤ r₂ ≤ ⋯ ≤ sₘ ≤ r_{m+1} ≤ U`: beyond `U`,
`(x - U) ∏ (x - sᵢ) ≤ ∏ (x - rᵢ)`. -/
private theorem prod_sub_le_of_listInterlaces {U x : ℝ} (hx : U < x) :
    ∀ (ss rs : List ℝ), rs.length = ss.length + 1 → ListInterlaces ss rs → (∀ r ∈ rs, r ≤ U) →
      (x - U) * (ss.map (x - ·)).prod ≤ (rs.map (x - ·)).prod
  | [], [], hl, _, _ => by simp at hl
  | [], [r], _, _, hU => by
      simp only [List.map_nil, List.prod_nil, mul_one, List.map_cons, List.prod_cons]
      linarith [hU r (by simp)]
  | s :: ss, r₁ :: r₂ :: rs, hl, h, hU => by
      obtain ⟨h1, h2, h3⟩ := h
      have ih := prod_sub_le_of_listInterlaces hx ss (r₂ :: rs) (by simpa using hl) h3
        (fun r hr => hU r (List.mem_cons_of_mem _ hr))
      have hr₂ : r₂ ≤ U := hU r₂ (by simp)
      have hnn : 0 ≤ ((r₂ :: rs).map (x - ·)).prod :=
        List.prod_nonneg fun y hy => by
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
          linarith [hU t (List.mem_cons_of_mem _ ht)]
      simp only [List.map_cons, List.prod_cons] at ih hnn ⊢
      have hs : 0 ≤ x - s := by linarith
      calc (x - U) * ((x - s) * (ss.map (x - ·)).prod)
          = (x - s) * ((x - U) * (ss.map (x - ·)).prod) := by ring
        _ ≤ (x - s) * ((x - r₂) * (rs.map (x - ·)).prod) := mul_le_mul_of_nonneg_left ih hs
        _ ≤ (x - r₁) * ((x - r₂) * (rs.map (x - ·)).prod) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
  | [], _ :: _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl
  | _ :: _, [_], hl, _, _ => by simp at hl

/-- If `g` interlaces `f` and the roots of `f` are at most `U`, then beyond `U`,
`lc f · (x - U) · g(x) ≤ lc g · f(x)`. -/
theorem leadingCoeff_mul_sub_mul_eval_le_of_interlaces {f g : ℝ[X]} {U x : ℝ}
    (h : Interlaces g f) (hfpos : 0 < f.leadingCoeff) (hgpos : 0 < g.leadingCoeff)
    (hU : ∀ t ∈ f.roots, t ≤ U) (hx : U < x) :
    f.leadingCoeff * (x - U) * g.eval x ≤ g.leadingCoeff * f.eval x := by
  obtain ⟨⟨_, hfs⟩, ⟨_, hgs⟩, hdeg, rs, ss, _, _, hrs, hss, hint⟩ := h
  have hlen : rs.length = ss.length + 1 := by
    rw [← Multiset.coe_card, ← Multiset.coe_card, hrs, hss, card_roots_of_splits hfs,
      card_roots_of_splits hgs, hdeg]
  have key := prod_sub_le_of_listInterlaces hx ss rs hlen hint
    (fun r hr => hU r (by rw [← hrs]; exact Multiset.mem_coe.mpr hr))
  rw [eval_eq_leadingCoeff_mul_prod_sub hgs x, eval_eq_leadingCoeff_mul_prod_sub hfs x,
    ← hrs, ← hss, Multiset.map_coe, Multiset.map_coe, Multiset.prod_coe, Multiset.prod_coe]
  have hc : 0 ≤ f.leadingCoeff * g.leadingCoeff := (mul_pos hfpos hgpos).le
  nlinarith [mul_le_mul_of_nonneg_left key hc]

/-- Roots of `F = a f + b g` stay at most `U` when `g` interlaces `f`, both have roots at most
`U`, `a ≥ 0` beyond `U` and `a ρ (x - U) + b > 0` there, where `ρ` bounds the ratio of the
leading coefficients from below. -/
theorem threeTerm_roots_le_step_of_ratio {f g F a b : ℝ[X]} {U ρ : ℝ} (hF : F = a * f + b * g)
    (hgf : Interlaces g f) (hfpos : 0 < f.leadingCoeff) (hgpos : 0 < g.leadingCoeff)
    (hfU : ∀ t ∈ f.roots, t ≤ U) (hgU : ∀ t ∈ g.roots, t ≤ U)
    (hρ : ρ * g.leadingCoeff ≤ f.leadingCoeff) (ha : ∀ x, U < x → 0 ≤ a.eval x)
    (hab : ∀ x, U < x → 0 < a.eval x * ρ * (x - U) + b.eval x) :
    ∀ t ∈ F.roots, t ≤ U := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := isRoot_of_mem_roots ht
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  have hg : 0 < g.eval t := eval_pos_of_roots_le hgf.2.1.2 hgpos hgU hlt
  have hkey := leadingCoeff_mul_sub_mul_eval_le_of_interlaces hgf hfpos hgpos hfU hlt
  have hxU : 0 < t - U := by linarith
  -- `f t ≥ ρ (t - U) g t`
  have hf : ρ * (t - U) * g.eval t ≤ f.eval t := by
    have h1 : ρ * g.leadingCoeff * ((t - U) * g.eval t) ≤
        f.leadingCoeff * ((t - U) * g.eval t) :=
      mul_le_mul_of_nonneg_right hρ (mul_pos hxU hg).le
    have h2 : g.leadingCoeff * (ρ * (t - U) * g.eval t) ≤ g.leadingCoeff * f.eval t := by
      nlinarith
    exact le_of_mul_le_mul_left h2 hgpos
  have := hab t hlt
  nlinarith [mul_le_mul_of_nonneg_left hf (ha t hlt), mul_pos hg this]

/-- `threeTerm_interlaces_of_window` with the interlacing of the two previous rows available
to the window step. -/
theorem threeTerm_interlaces_of_window_of_interlaces (W : ℝ → Prop)
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hb : ∀ n x, W x → (b n).eval x ≤ 0)
    (hW : ∀ n, Interlaces (P n) (P (n + 1)) → (∀ t ∈ (P n).roots, W t) →
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
            (by rw [← hF, hdeg, hdeg]; lia) (by rw [← hF, hdeg, hdeg]; lia)
            (fun r hr => hb n r (hw1 r ((mem_roots hne).mpr hr)))
        rw [← hF] at hprec
        have hi' := hprec.toInterlaces (by rw [hdeg, hdeg]; lia)
        exact ⟨hw1, hW n hi hw0 hw1, hi'⟩
  exact fun n => (key n).2.2

/-- Three-term interlacing with roots in `(-∞, U]`, where `b n` may be negative beyond `U`
as long as `a n ρ n (x - U) + b n > 0` there, `ρ n` bounding the ratio of consecutive leading
coefficients from below. -/
theorem threeTerm_interlaces_of_roots_le_of_ratio {U : ℝ} {ρ : ℕ → ℝ}
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hb : ∀ n x, x ≤ U → (b n).eval x ≤ 0)
    (hρ : ∀ n, ρ n * (P n).leadingCoeff ≤ (P (n + 1)).leadingCoeff)
    (ha : ∀ n x, U < x → 0 ≤ (a n).eval x)
    (hab : ∀ n x, U < x → 0 < (a n).eval x * ρ n * (x - U) + (b n).eval x)
    (hW0 : ∀ t ∈ (P 0).roots, t ≤ U) (hW1 : ∀ t ∈ (P 1).roots, t ≤ U)
    (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  threeTerm_interlaces_of_window_of_interlaces (fun x => x ≤ U) hrec hdeg hpos hb
    (fun n hi hw0 hw1 => threeTerm_roots_le_step_of_ratio (hrec n) hi (hpos (n + 1)) (hpos n)
      hw1 hw0 (hρ n) (ha n) (hab n))
    hW0 hW1 h01 n

/-- Values beyond the roots of a three-term recurrence under a ratio barrier: if
`0 < ρ ≤ a n` and `ρ ^ 2 ≤ a n ρ + b n` at `x`, then `0 < P n` and `ρ P n ≤ P (n + 1)` at `x`
propagate from `n = 0`, whatever the sign of `b n`. -/
theorem threeTerm_eval_pos_of_barrier {x ρ : ℝ}
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hρ : 0 < ρ) (ha : ∀ n, ρ ≤ (a n).eval x)
    (hab : ∀ n, ρ ^ 2 ≤ (a n).eval x * ρ + (b n).eval x)
    (h0 : 0 < (P 0).eval x) (h1 : ρ * (P 0).eval x ≤ (P 1).eval x) (n : ℕ) :
    0 < (P n).eval x ∧ ρ * (P n).eval x ≤ (P (n + 1)).eval x := by
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ n ih =>
      obtain ⟨hp, hr⟩ := ih
      refine ⟨(mul_pos hρ hp).trans_le hr, ?_⟩
      rw [show n + 1 + 1 = n + 2 from rfl, hrec, eval_add, eval_mul, eval_mul]
      nlinarith [mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr (ha n)),
        mul_nonneg (sub_nonneg.mpr (hab n)) hp.le]

/-- Roots of a three-term recurrence stay at most `U` under a ratio barrier beyond `U`
(`threeTerm_eval_pos_of_barrier`). -/
theorem threeTerm_roots_le_of_barrier {U : ℝ} {ρ : ℝ → ℝ}
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hρ : ∀ x, U < x → 0 < ρ x) (ha : ∀ n x, U < x → ρ x ≤ (a n).eval x)
    (hab : ∀ n x, U < x → ρ x ^ 2 ≤ (a n).eval x * ρ x + (b n).eval x)
    (h0 : ∀ x, U < x → 0 < (P 0).eval x) (h1 : ∀ x, U < x → ρ x * (P 0).eval x ≤ (P 1).eval x)
    (n : ℕ) : ∀ t ∈ (P n).roots, t ≤ U := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h := (threeTerm_eval_pos_of_barrier hrec (hρ t hlt) (fun n => ha n t hlt)
    (fun n => hab n t hlt) (h0 t hlt) (h1 t hlt) n).1
  rw [(isRoot_of_mem_roots ht).eq_zero] at h
  exact lt_irrefl 0 h

/-- Three-term interlacing with roots in `[L, U]`, where `b n` may be negative beyond `U`: a
ratio barrier `0 < ρ ≤ a n`, `ρ ^ 2 ≤ a n ρ + b n` beyond `U`, started by `ρ P 0 ≤ P 1`, keeps
every row positive there.  This covers Chebyshev-like rows such as
`P (n + 2) = 2 (1 + X) P (n + 1) - (1 + X) P n` (`ρ = 1`). -/
theorem threeTerm_interlaces_of_roots_mem_Icc_of_barrier {L U : ℝ} {ρ : ℝ → ℝ}
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hb : ∀ n x, L ≤ x → x ≤ U → (b n).eval x ≤ 0)
    (hρ : ∀ x, U < x → 0 < ρ x) (haU : ∀ n x, U < x → ρ x ≤ (a n).eval x)
    (habU : ∀ n x, U < x → ρ x ^ 2 ≤ (a n).eval x * ρ x + (b n).eval x)
    (h1U : ∀ x, U < x → ρ x * (P 0).eval x ≤ (P 1).eval x)
    (haL : ∀ n x, x < L → (a n).eval x < 0) (hbL : ∀ n x, x < L → 0 ≤ (b n).eval x)
    (hW0 : ∀ t ∈ (P 0).roots, L ≤ t ∧ t ≤ U) (hW1 : ∀ t ∈ (P 1).roots, L ≤ t ∧ t ≤ U)
    (h01 : Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  have hU := threeTerm_roots_le_of_barrier hrec hρ haU habU
    (fun _ hx => eval_pos_of_roots_le h01.2.1.2 (hpos 0) (fun t ht => (hW0 t ht).2) hx) h1U
  threeTerm_interlaces_of_window (fun x => L ≤ x ∧ x ≤ U) hrec hdeg hpos
    (fun n x hx => hb n x hx.1 hx.2)
    (fun n hs0 hs1 hw0 hw1 t ht =>
      ⟨threeTerm_roots_ge_step (hrec n) hs1 (hpos (n + 1)) hs0 (hpos n)
          (by rw [hdeg, hdeg]; lia) (fun t ht => (hw1 t ht).1) (fun t ht => (hw0 t ht).1)
          (haL n) (hbL n) t ht, hU (n + 2) t ht⟩)
    hW0 hW1 h01 n

end ThreeTerm

end RealRooted

/-!
## Degree-bounded root windows for derivative recurrences

`RootWindow.lean` needs `A n ≥ 0` beyond the window.  For `F = A f' + B f` with `f`
real-rooted and all roots at most `U`, the logarithmic derivative bound
`f' (x) / f x = ∑ 1 / (x - r) ≤ deg f / (x - U)` for `x > U` lets `A` be negative:
it suffices that `B (x - U) + min A 0 * deg f > 0`.

## Main results

* `derivative_eval_mul_sub_le_of_roots_le`, `derivative_eval_mul_sub_le_of_roots_ge`:
  the bounds `f' (x) (x - U) ≤ deg f * f x` and the mirrored one below `L`.
* `derivRec_roots_le_step_of_degree`, `derivRec_roots_ge_step_of_degree`: one step;
  `derivRec_roots_le_step_of_or`: either condition, chosen pointwise.
* `derivRec_interlaces_of_roots_le_of_degree`, `derivRec_interlaces_of_roots_ge_of_degree`,
  `derivRec_interlaces_of_roots_mem_Icc_of_degree`: the induction for the windows
  `(-∞, U]`, `[L, ∞)` and `[L, U]`; `derivRec_interlaces_of_roots_le_mono`: the windows
  `(-∞, U n]` with `U` nondecreasing.
-/

open Polynomial

namespace RealRooted

section Bounds

variable {f : ℝ[X]} {L U x : ℝ}

/-- For real-rooted `f` with positive leading coefficient and all roots at most `U`,
`f' (x) (x - U) ≤ deg f * f x` for `x > U`. -/
theorem derivative_eval_mul_sub_le_of_roots_le (hs : f.Splits) (hpos : 0 < f.leadingCoeff)
    (hU : ∀ t ∈ f.roots, t ≤ U) (hx : U < x) :
    f.derivative.eval x * (x - U) ≤ f.natDegree * f.eval x := by
  have hf := eval_pos_of_roots_le hs hpos hU hx
  rw [hs.eval_derivative_eq_eval_mul_sum hf.ne']
  have hle : (x - U) * (f.roots.map fun z => 1 / (x - z)).sum ≤ f.natDegree := by
    rw [← Multiset.sum_map_mul_left, ← card_roots_of_splits hs]
    refine (Multiset.sum_le_card_nsmul _ (1 : ℝ) fun y hy => ?_).trans (by simp)
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
    have := hU z hz
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  generalize (f.roots.map fun z => 1 / (x - z)).sum = S at hle
  nlinarith [mul_nonneg hf.le (sub_nonneg.2 hle)]

/-- For real-rooted `f` with positive leading coefficient and all roots at least `L`,
`(-1)^(d+1) f' (x) (L - x) ≤ d * ((-1)^d f x)` for `x < L`, `d = deg f`. -/
theorem derivative_eval_mul_sub_le_of_roots_ge (hs : f.Splits) (hpos : 0 < f.leadingCoeff)
    (hL : ∀ t ∈ f.roots, L ≤ t) (hx : x < L) :
    (-1) ^ (f.natDegree + 1) * f.derivative.eval x * (L - x) ≤
      f.natDegree * ((-1) ^ f.natDegree * f.eval x) := by
  have hf := neg_one_pow_mul_eval_pos_of_roots_ge hs hpos hL hx
  have hne : f.eval x ≠ 0 := fun h => by simp [h] at hf
  rw [hs.eval_derivative_eq_eval_mul_sum hne]
  have hle : (x - L) * (f.roots.map fun z => 1 / (x - z)).sum ≤ f.natDegree := by
    rw [← Multiset.sum_map_mul_left, ← card_roots_of_splits hs]
    refine (Multiset.sum_le_card_nsmul _ (1 : ℝ) fun y hy => ?_).trans (by simp)
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
    have := hL z hz
    rw [mul_one_div, div_le_one_of_neg (by linarith)]
    linarith
  generalize (f.roots.map fun z => 1 / (x - z)).sum = S at hle
  rw [pow_succ]
  nlinarith [mul_nonneg hf.le (sub_nonneg.2 hle)]

end Bounds

section Step

variable {f F A B : ℝ[X]} {L U : ℝ}

/-- Roots stay at most `U` when `B (x - U) + min A 0 * deg f > 0` beyond `U`. -/
theorem derivRec_roots_le_step_of_degree (hF : F = A * f.derivative + B * f)
    (hs : f.Splits) (hpos : 0 < f.leadingCoeff) (hU : ∀ t ∈ f.roots, t ≤ U)
    (hAB : ∀ x, U < x → 0 < B.eval x * (x - U) + min (A.eval x) 0 * f.natDegree) :
    ∀ t ∈ F.roots, t ≤ U := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := isRoot_of_mem_roots ht
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  have hf := eval_pos_of_roots_le hs hpos hU hlt
  have hf' := derivative_eval_nonneg_of_roots_le hs hpos hU hlt
  have hb := derivative_eval_mul_sub_le_of_roots_le hs hpos hU hlt
  have hab := hAB t hlt
  have hd : (0 : ℝ) ≤ f.natDegree := Nat.cast_nonneg _
  have hsub : 0 < t - U := by linarith
  rcases le_total (A.eval t) 0 with h | h
  · rw [min_eq_left h] at hab
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr hb), mul_pos hf hab]
  · rw [min_eq_right h] at hab
    nlinarith [mul_nonneg (mul_nonneg h hf') hsub.le, mul_pos hf hab]

/-- Roots stay at most `U` when, at each point beyond `U`, either `A ≥ 0` and `B > 0`, or
`B (x - U) + min A 0 * deg f > 0`. -/
theorem derivRec_roots_le_step_of_or (hF : F = A * f.derivative + B * f)
    (hs : f.Splits) (hpos : 0 < f.leadingCoeff) (hU : ∀ t ∈ f.roots, t ≤ U)
    (hAB : ∀ x, U < x → (0 ≤ A.eval x ∧ 0 < B.eval x) ∨
      0 < B.eval x * (x - U) + min (A.eval x) 0 * f.natDegree) :
    ∀ t ∈ F.roots, t ≤ U := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := isRoot_of_mem_roots ht
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  have hf := eval_pos_of_roots_le hs hpos hU hlt
  have hf' := derivative_eval_nonneg_of_roots_le hs hpos hU hlt
  rcases hAB t hlt with ⟨hA, hB⟩ | hab
  · nlinarith [mul_nonneg hA hf', mul_pos hB hf]
  · have hb := derivative_eval_mul_sub_le_of_roots_le hs hpos hU hlt
    have hd : (0 : ℝ) ≤ f.natDegree := Nat.cast_nonneg _
    have hsub : 0 < t - U := by linarith
    rcases le_total (A.eval t) 0 with h | h
    · rw [min_eq_left h] at hab
      nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr hb), mul_pos hf hab]
    · rw [min_eq_right h] at hab
      nlinarith [mul_nonneg (mul_nonneg h hf') hsub.le, mul_pos hf hab]

/-- Roots stay at least `L` when `B (x - L) + min A 0 * deg f > 0` below `L`. -/
theorem derivRec_roots_ge_step_of_degree (hF : F = A * f.derivative + B * f)
    (hs : f.Splits) (hpos : 0 < f.leadingCoeff) (hL : ∀ t ∈ f.roots, L ≤ t)
    (hAB : ∀ x, x < L → 0 < B.eval x * (x - L) + min (A.eval x) 0 * f.natDegree) :
    ∀ t ∈ F.roots, L ≤ t := by
  intro t ht
  refine le_of_not_gt fun hlt => ?_
  have h0 : F.eval t = 0 := isRoot_of_mem_roots ht
  rw [hF, eval_add, eval_mul, eval_mul] at h0
  have hf := neg_one_pow_mul_eval_pos_of_roots_ge hs hpos hL hlt
  have hf' := derivative_neg_one_pow_mul_eval_nonneg_of_roots_ge hs hpos hL hlt
  have hb := derivative_eval_mul_sub_le_of_roots_ge hs hpos hL hlt
  have hab := hAB t hlt
  have hd : (0 : ℝ) ≤ f.natDegree := Nat.cast_nonneg _
  have hsub : 0 < L - t := by linarith
  -- multiply `F t = 0` by `(-1)^(d+1)`
  have key : (-1 : ℝ) ^ (f.natDegree + 1) * (A.eval t * f.derivative.eval t +
      B.eval t * f.eval t) = 0 := by rw [h0, mul_zero]
  rw [pow_succ] at key hf' hb
  rcases le_total (A.eval t) 0 with h | h
  · rw [min_eq_left h] at hab
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (sub_nonneg.mpr hb), mul_pos hf hab]
  · rw [min_eq_right h] at hab
    nlinarith [mul_nonneg (mul_nonneg h hf') hsub.le, mul_pos hf hab]

end Step

section Sequence

variable {P A B : ℕ → ℝ[X]} {D₀ : ℕ}

/-- Roots at most `U`: `A n ≤ 0` up to `U`, and `B (x - U) + min A 0 * (D₀ + n) > 0` beyond. -/
theorem derivRec_interlaces_of_roots_le_of_degree {U : ℝ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, x ≤ U → (A n).eval x ≤ 0)
    (hAB : ∀ n x, U < x → 0 < (B n).eval x * (x - U) + min ((A n).eval x) 0 * (D₀ + n))
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, t ≤ U)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_window (fun x => x ≤ U) hrec hdeg hpos hA
    (fun n hs hw => derivRec_roots_le_step_of_degree (hrec n) hs (hpos n) hw
      fun x hx => by simpa [hdeg n] using hAB n x hx)
    h0 hW0 h01 n

/-- Roots at least `L`: `A n ≤ 0` from `L` on, and `B (x - L) + min A 0 * (D₀ + n) > 0`
below. -/
theorem derivRec_interlaces_of_roots_ge_of_degree {L : ℝ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, L ≤ x → (A n).eval x ≤ 0)
    (hAB : ∀ n x, x < L → 0 < (B n).eval x * (x - L) + min ((A n).eval x) 0 * (D₀ + n))
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, L ≤ t)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_window (fun x => L ≤ x) hrec hdeg hpos hA
    (fun n hs hw => derivRec_roots_ge_step_of_degree (hrec n) hs (hpos n) hw
      fun x hx => by simpa [hdeg n] using hAB n x hx)
    h0 hW0 h01 n

/-- Roots in `[L, U]`: `A n ≤ 0` on `[L, U]`, with the degree-bounded conditions outside. -/
theorem derivRec_interlaces_of_roots_mem_Icc_of_degree {L U : ℝ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, L ≤ x → x ≤ U → (A n).eval x ≤ 0)
    (hABU : ∀ n x, U < x → 0 < (B n).eval x * (x - U) + min ((A n).eval x) 0 * (D₀ + n))
    (hABL : ∀ n x, x < L → 0 < (B n).eval x * (x - L) + min ((A n).eval x) 0 * (D₀ + n))
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, L ≤ t ∧ t ≤ U)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_window (fun x => L ≤ x ∧ x ≤ U) hrec hdeg hpos
    (fun n x hx => hA n x hx.1 hx.2)
    (fun n hs hw t ht =>
      ⟨derivRec_roots_ge_step_of_degree (hrec n) hs (hpos n) (fun t ht => (hw t ht).1)
          (fun x hx => by simpa [hdeg n] using hABL n x hx) t ht,
        derivRec_roots_le_step_of_degree (hrec n) hs (hpos n) (fun t ht => (hw t ht).2)
          (fun x hx => by simpa [hdeg n] using hABU n x hx) t ht⟩)
    h0 hW0 h01 n

/-- `derivRec_interlaces_of_roots_mem_Icc_mono` with the lower bound `L n = p n / q n`,
`q n > 0`, and every condition multiplied out, so that no hypothesis contains a quotient.
The condition `A n ≥ 0` is asked below `L n`, which contains `(-∞, L (n + 1))`: this is the
natural form when `L n` is a root of `A n`. -/
theorem derivRec_interlaces_of_roots_mem_Icc_mono_div {p q : ℕ → ℝ} {U : ℝ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hq : ∀ n, 0 < q n) (hL : ∀ n, p (n + 1) * q n ≤ p n * q (n + 1))
    (hA : ∀ n x, p n ≤ q n * x → x ≤ U → (A n).eval x ≤ 0)
    (hAU : ∀ n x, U < x → 0 ≤ (A n).eval x) (hBU : ∀ n x, U < x → 0 < (B n).eval x)
    (hAL : ∀ n x, q n * x < p n → 0 ≤ (A n).eval x)
    (hBL : ∀ n x, q (n + 1) * x < p (n + 1) → (B n).eval x < 0)
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, p 0 ≤ q 0 * t ∧ t ≤ U)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have hle (m : ℕ) (x : ℝ) : p m / q m ≤ x ↔ p m ≤ q m * x := by
    rw [div_le_iff₀ (hq m), mul_comm]
  have hlt (m : ℕ) (x : ℝ) : x < p m / q m ↔ q m * x < p m := by
    rw [lt_div_iff₀ (hq m), mul_comm]
  have hmono (m : ℕ) : p (m + 1) / q (m + 1) ≤ p m / q m := by
    rw [div_le_div_iff₀ (hq _) (hq _)]; exact hL m
  refine derivRec_interlaces_of_roots_mem_Icc_mono (L := fun m => p m / q m) hrec hdeg hpos
    hmono (fun m x h1 h2 => hA m x ((hle m x).mp h1) h2) hAU hBU
    (fun m x h => hAL m x ((hlt m x).mp (h.trans_le (hmono m))))
    (fun m x h => hBL m x ((hlt _ x).mp h)) h0
    (fun t ht => ⟨(hle 0 t).mpr (hW0 t ht).1, (hW0 t ht).2⟩) h01 n

/-- Roots at most `U n` with a nondecreasing bound `U`: `A n ≤ 0` up to `U n`, and beyond
`U (n + 1)` at each point either the plain conditions `A n ≥ 0`, `B n > 0` or the
degree-bounded one. -/
theorem derivRec_interlaces_of_roots_le_mono {U : ℕ → ℝ}
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hU : ∀ n, U n ≤ U (n + 1))
    (hA : ∀ n x, x ≤ U n → (A n).eval x ≤ 0)
    (hAB : ∀ n x, U (n + 1) < x → (0 ≤ (A n).eval x ∧ 0 < (B n).eval x) ∨
      0 < (B n).eval x * (x - U (n + 1)) + min ((A n).eval x) 0 * (D₀ + n))
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, t ≤ U 0)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) (n : ℕ) :
    Interlaces (P n) (P (n + 1)) :=
  derivRec_interlaces_of_windows (fun n x => x ≤ U n) hrec hdeg hpos hA
    (fun n hs hw => derivRec_roots_le_step_of_or (hrec n) hs (hpos n)
      (fun t ht => (hw t ht).trans (hU n))
      fun x hx => by simpa [hdeg n] using hAB n x hx)
    h0 hW0 h01 n

end Sequence

end RealRooted
