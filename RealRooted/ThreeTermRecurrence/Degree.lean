import RealRooted.DerivativeRecurrence.Degree

/-!
# Degrees of three-term recurrences

For `P (n + 2) = a n * P (n + 1) + b n * P n` with `natDegree (a n) ≤ d` and
`natDegree (b n) ≤ 2 d`, the coefficients `t n` of `P n` in degree `D₀ + d n`
satisfy the scalar recurrence

`t (n + 2) = α n * t (n + 1) + β n * t n`,   `α n = (a n)_d`, `β n = (b n)_{2d}`.

So the rows have degree exactly `D₀ + d n`, with positive leading coefficients,
as soon as `t` stays positive.  Two regimes cover the OEIS triangles:

* `α n, β n ≥ 0` with `α n + β n > 0` (`threeTermPos_*`);
* `β n ≤ 0` and `ρ ^ 2 ≤ ρ α n + β n` for some `ρ > 0` with `ρ t 0 ≤ t 1`; then
  `t (n + 1) ≥ ρ t n > 0` throughout (`threeTermRatio_*`).

## Main results

* `threeTerm_step`: the degree bound and the top coefficient of one step.
* `twoStep_top_of_invariant`: the induction for any invariant `R (t n) (t (n + 1))`
  preserved by the scalar recurrence, for any two-step recurrence whose one-step
  degree computation has this shape (three-term rows here, derivative-lag rows in
  `RealRooted.DerivativeRecurrence.LagDegree`).
* `twoStep_natDegree_eq_and_leadingCoeff_pos`: the nonnegative regime of the above.
* `threeTermPos_natDegree`, `threeTermPos_ne_zero`, `threeTermPos_leadingCoeff_pos`
  and the `threeTermRatio_*` versions.
* `threeTerm_eval_zero_pos`, `threeTermRatio_eval_zero_pos`: positivity of the rows
  at `0`, from the same two scalar regimes applied to `x n = (P n).eval 0`.
-/

open Polynomial

namespace RealRooted

variable {P a b : ℕ → ℝ[X]} {d D₀ : ℕ}

/-- A two-step recurrence `P (n + 2) = a n * P (n + 1)` as a three-term recurrence. -/
theorem threeTerm_rec_of_left (h : ∀ n, P (n + 2) = a n * P (n + 1)) :
    ∀ n, P (n + 2) = a n * P (n + 1) + (fun _ => (0 : ℝ[X])) n * P n := by
  simpa using h

/-- A two-step recurrence `P (n + 2) = b n * P n` as a three-term recurrence. -/
theorem threeTerm_rec_of_right (h : ∀ n, P (n + 2) = b n * P n) :
    ∀ n, P (n + 2) = (fun _ => (0 : ℝ[X])) n * P (n + 1) + b n * P n := by
  simpa using h

/-- A three-term recurrence certified through its remainder: if the remainder
`r n = C (δ n) * P (n + 2) - a n * P (n + 1) - b n * P n` vanishes at `0` and satisfies
`r (n + 1) = c n * r n` (for instance when `P` satisfies a recurrence of order three that
factors through the three-term one), then `P` satisfies the three-term recurrence. -/
theorem threeTerm_rec_of_remainder {c : ℕ → ℝ[X]} {δ : ℕ → ℝ} (hδ : ∀ n, δ n ≠ 0)
    (hstep : ∀ n, C (δ (n + 1)) * P (n + 3) - a (n + 1) * P (n + 2) - b (n + 1) * P (n + 1) =
      c n * (C (δ n) * P (n + 2) - a n * P (n + 1) - b n * P n))
    (h0 : C (δ 0) * P 2 - a 0 * P 1 - b 0 * P 0 = 0) :
    ∀ n, P (n + 2) = (C (δ n)⁻¹ * a n) * P (n + 1) + (C (δ n)⁻¹ * b n) * P n := by
  have hr : ∀ n, C (δ n) * P (n + 2) - a n * P (n + 1) - b n * P n = 0 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact (hstep n).trans (by rw [ih, mul_zero])
  intro n
  have hC : C (δ n)⁻¹ * C (δ n) = 1 := by rw [← C_mul, inv_mul_cancel₀ (hδ n), C_1]
  have h : C (δ n) * P (n + 2) = a n * P (n + 1) + b n * P n := by
    rw [← sub_eq_zero, ← sub_sub]
    exact hr n
  rw [← one_mul (P (n + 2)), ← hC, mul_assoc, h]
  ring

/-- One step of a three-term recurrence: the degree bound and the coefficient in
the bounding degree. -/
theorem threeTerm_step (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d) (n : ℕ)
    (h0 : (P n).natDegree ≤ D₀ + d * n) (h1 : (P (n + 1)).natDegree ≤ D₀ + d * (n + 1)) :
    (P (n + 2)).natDegree ≤ D₀ + d * (n + 2) ∧
      (P (n + 2)).coeff (D₀ + d * (n + 2)) =
        (a n).coeff d * (P (n + 1)).coeff (D₀ + d * (n + 1)) +
          (b n).coeff (2 * d) * (P n).coeff (D₀ + d * n) := by
  have e1 : D₀ + d * (n + 2) = d + (D₀ + d * (n + 1)) := by ring
  have e0 : D₀ + d * (n + 2) = 2 * d + (D₀ + d * n) := by ring
  rw [hrec n]
  refine ⟨natDegree_add_le_of_degree_le ?_ ?_, ?_⟩
  · rw [e1]; exact natDegree_mul_le_of_le (ha n) h1
  · rw [e0]; exact natDegree_mul_le_of_le (hb n) h0
  · rw [coeff_add, e1, coeff_mul_add_of_natDegree_le (ha n) h1, ← e1, e0,
      coeff_mul_add_of_natDegree_le (hb n) h0]

/-- The induction behind the two-step degree theorems.  Suppose that whenever two
consecutive rows satisfy the degree bounds, so does the next row, and its
coefficient in the bounding degree is `α n * t (n + 1) + β n * t n`, where `t n`
is the coefficient of `P n` in degree `D₀ + d * n`.  Then every invariant `R` of
consecutive top coefficients that is preserved by this scalar recurrence holds
for all `n`. -/
theorem twoStep_top_of_invariant {α β : ℕ → ℝ}
    (hstep : ∀ n, (P n).natDegree ≤ D₀ + d * n → (P (n + 1)).natDegree ≤ D₀ + d * (n + 1) →
      (P (n + 2)).natDegree ≤ D₀ + d * (n + 2) ∧
        (P (n + 2)).coeff (D₀ + d * (n + 2)) =
          α n * (P (n + 1)).coeff (D₀ + d * (n + 1)) + β n * (P n).coeff (D₀ + d * n))
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (R : ℝ → ℝ → Prop) (hR01 : R ((P 0).coeff D₀) ((P 1).coeff (D₀ + d)))
    (hRstep : ∀ n x y, R x y → R y (α n * y + β n * x)) :
    ∀ n, (P n).natDegree ≤ D₀ + d * n ∧ (P (n + 1)).natDegree ≤ D₀ + d * (n + 1) ∧
      R ((P n).coeff (D₀ + d * n)) ((P (n + 1)).coeff (D₀ + d * (n + 1)))
  | 0 => ⟨by simpa using h0, by simpa using h1, by simpa using hR01⟩
  | n + 1 => by
      obtain ⟨hn0, hn1, hR⟩ := twoStep_top_of_invariant hstep h0 h1 R hR01 hRstep n
      have hs := hstep n hn0 hn1
      exact ⟨hn1, hs.1, by rw [hs.2]; exact hRstep n _ _ hR⟩

private theorem top_pos_of_invariant {α β : ℕ → ℝ}
    (hstep : ∀ n, (P n).natDegree ≤ D₀ + d * n → (P (n + 1)).natDegree ≤ D₀ + d * (n + 1) →
      (P (n + 2)).natDegree ≤ D₀ + d * (n + 2) ∧
        (P (n + 2)).coeff (D₀ + d * (n + 2)) =
          α n * (P (n + 1)).coeff (D₀ + d * (n + 1)) + β n * (P n).coeff (D₀ + d * n))
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (R : ℝ → ℝ → Prop) (hR01 : R ((P 0).coeff D₀) ((P 1).coeff (D₀ + d)))
    (hRpos : ∀ x y, R x y → 0 < x)
    (hRstep : ∀ n x y, R x y → R y (α n * y + β n * x)) (n : ℕ) :
    (P n).natDegree = D₀ + d * n ∧ 0 < (P n).leadingCoeff := by
  obtain ⟨hle, -, hR⟩ := twoStep_top_of_invariant hstep h0 h1 R hR01 hRstep n
  have hpos := hRpos _ _ hR
  have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hle hpos.ne'
  exact ⟨hdeg, by rwa [leadingCoeff, hdeg]⟩

/-- The scalar companion of `twoStep_top_of_invariant`: an invariant of
consecutive terms of `x (n + 2) = α n * x (n + 1) + β n * x n`. -/
private theorem scalar_of_invariant {α β s : ℕ → ℝ}
    (hs : ∀ n, s (n + 2) = α n * s (n + 1) + β n * s n)
    (R : ℝ → ℝ → Prop) (hR01 : R (s 0) (s 1))
    (hRstep : ∀ n x y, R x y → R y (α n * y + β n * x)) :
    ∀ n, R (s n) (s (n + 1))
  | 0 => hR01
  | n + 1 => by
      rw [show n + 1 + 1 = n + 2 from rfl, hs n]
      exact hRstep n _ _ (scalar_of_invariant hs R hR01 hRstep n)

section Positive

/-- Nonnegative multipliers: `α n, β n ≥ 0` and `α n + β n > 0`. -/
private theorem pos_invariant {α β : ℕ → ℝ}
    (hα : ∀ n, 0 ≤ α n) (hβ : ∀ n, 0 ≤ β n) (hαβ : ∀ n, 0 < α n + β n) (n : ℕ) (x y : ℝ)
    (h : 0 < x ∧ 0 < y) :
    0 < y ∧ 0 < α n * y + β n * x := by
  refine ⟨h.2, ?_⟩
  rcases (hα n).lt_or_eq with hα' | hα'
  · nlinarith [mul_nonneg (hβ n) h.1.le, mul_pos hα' h.2]
  · have hβpos : 0 < β n := by linarith [hαβ n]
    rw [← hα']
    nlinarith [mul_pos hβpos h.1]

/-- Rows of a two-step recurrence whose top coefficients follow
`t (n + 2) = α n * t (n + 1) + β n * t n` with `α n, β n ≥ 0` and
`α n + β n > 0` have degree `D₀ + d * n` and positive leading coefficients.
`hstep` is the one-step degree computation for the concrete recurrence shape. -/
theorem twoStep_natDegree_eq_and_leadingCoeff_pos {α β : ℕ → ℝ}
    (hstep : ∀ n, (P n).natDegree ≤ D₀ + d * n → (P (n + 1)).natDegree ≤ D₀ + d * (n + 1) →
      (P (n + 2)).natDegree ≤ D₀ + d * (n + 2) ∧
        (P (n + 2)).coeff (D₀ + d * (n + 2)) =
          α n * (P (n + 1)).coeff (D₀ + d * (n + 1)) + β n * (P n).coeff (D₀ + d * n))
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ α n) (hβ : ∀ n, 0 ≤ β n) (hαβ : ∀ n, 0 < α n + β n) (n : ℕ) :
    (P n).natDegree = D₀ + d * n ∧ 0 < (P n).leadingCoeff :=
  top_pos_of_invariant hstep h0 h1 (fun x y => 0 < x ∧ 0 < y) ⟨hc0, hc1⟩
    (fun _ _ h => h.1) (pos_invariant hα hβ hαβ) n

theorem threeTermPos_natDegree_eq_and_leadingCoeff_pos
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ (a n).coeff d) (hβ : ∀ n, 0 ≤ (b n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    (P n).natDegree = D₀ + d * n ∧ 0 < (P n).leadingCoeff :=
  twoStep_natDegree_eq_and_leadingCoeff_pos (threeTerm_step hrec ha hb) h0 h1 hc0 hc1
    hα hβ hαβ n

theorem threeTermPos_natDegree (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ (a n).coeff d) (hβ : ∀ n, 0 ≤ (b n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    (P n).natDegree = D₀ + d * n :=
  (threeTermPos_natDegree_eq_and_leadingCoeff_pos hrec ha hb h0 h1 hc0 hc1 hα hβ hαβ n).1

theorem threeTermPos_leadingCoeff_pos (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ (a n).coeff d) (hβ : ∀ n, 0 ≤ (b n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    0 < (P n).leadingCoeff :=
  (threeTermPos_natDegree_eq_and_leadingCoeff_pos hrec ha hb h0 h1 hc0 hc1 hα hβ hαβ n).2

theorem threeTermPos_ne_zero (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ (a n).coeff d) (hβ : ∀ n, 0 ≤ (b n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    P n ≠ 0 :=
  leadingCoeff_ne_zero.mp
    (threeTermPos_leadingCoeff_pos hrec ha hb h0 h1 hc0 hc1 hα hβ hαβ n).ne'

end Positive

section Ratio

variable {ρ : ℝ}

/-- Nonpositive `β n` with growth ratio `ρ`: `ρ ^ 2 ≤ ρ α n + β n`. -/
private theorem ratio_invariant {α β : ℕ → ℝ} (hρ : 0 < ρ) (hβ : ∀ n, β n ≤ 0)
    (hαβ : ∀ n, ρ ^ 2 ≤ ρ * α n + β n) (n : ℕ) (x y : ℝ) (h : 0 < x ∧ ρ * x ≤ y) :
    0 < y ∧ ρ * y ≤ α n * y + β n * x := by
  have hy : 0 < y := lt_of_lt_of_le (mul_pos hρ h.1) h.2
  refine ⟨hy, ?_⟩
  -- `ρ (α y + β x) ≥ (ρ α + β) y ≥ ρ² y`, using `β x ≥ β y / ρ`
  have h1 : β n * y ≤ ρ * (β n * x) := by
    nlinarith [mul_le_mul_of_nonpos_left h.2 (hβ n)]
  have h2 : ρ * (ρ * y) ≤ ρ * (α n * y + β n * x) := by
    nlinarith [mul_le_mul_of_nonneg_right (hαβ n) hy.le]
  exact le_of_mul_le_mul_left h2 hρ

theorem threeTermRatio_natDegree_eq_and_leadingCoeff_pos
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hρ : 0 < ρ) (hc1 : ρ * (P 0).coeff D₀ ≤ (P 1).coeff (D₀ + d))
    (hβ : ∀ n, (b n).coeff (2 * d) ≤ 0)
    (hαβ : ∀ n, ρ ^ 2 ≤ ρ * (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    (P n).natDegree = D₀ + d * n ∧ 0 < (P n).leadingCoeff :=
  top_pos_of_invariant (threeTerm_step hrec ha hb) h0 h1 (fun x y => 0 < x ∧ ρ * x ≤ y)
    ⟨hc0, hc1⟩ (fun _ _ h => h.1) (ratio_invariant hρ hβ hαβ) n

theorem threeTermRatio_natDegree
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hρ : 0 < ρ) (hc1 : ρ * (P 0).coeff D₀ ≤ (P 1).coeff (D₀ + d))
    (hβ : ∀ n, (b n).coeff (2 * d) ≤ 0)
    (hαβ : ∀ n, ρ ^ 2 ≤ ρ * (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    (P n).natDegree = D₀ + d * n :=
  (threeTermRatio_natDegree_eq_and_leadingCoeff_pos hrec ha hb h0 h1 hc0 hρ hc1 hβ hαβ n).1

theorem threeTermRatio_leadingCoeff_pos
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hρ : 0 < ρ) (hc1 : ρ * (P 0).coeff D₀ ≤ (P 1).coeff (D₀ + d))
    (hβ : ∀ n, (b n).coeff (2 * d) ≤ 0)
    (hαβ : ∀ n, ρ ^ 2 ≤ ρ * (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    0 < (P n).leadingCoeff :=
  (threeTermRatio_natDegree_eq_and_leadingCoeff_pos hrec ha hb h0 h1 hc0 hρ hc1 hβ hαβ n).2

/-- Under the hypotheses of `threeTermRatio_natDegree`, consecutive leading coefficients grow
at least by the factor `ρ`. -/
theorem threeTermRatio_mul_leadingCoeff_le
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hρ : 0 < ρ) (hc1 : ρ * (P 0).coeff D₀ ≤ (P 1).coeff (D₀ + d))
    (hβ : ∀ n, (b n).coeff (2 * d) ≤ 0)
    (hαβ : ∀ n, ρ ^ 2 ≤ ρ * (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    ρ * (P n).leadingCoeff ≤ (P (n + 1)).leadingCoeff := by
  obtain ⟨-, -, hR⟩ := twoStep_top_of_invariant (threeTerm_step hrec ha hb) h0 h1
    (fun x y => 0 < x ∧ ρ * x ≤ y) ⟨hc0, hc1⟩ (ratio_invariant hρ hβ hαβ) n
  have hd0 := threeTermRatio_natDegree hrec ha hb h0 h1 hc0 hρ hc1 hβ hαβ n
  have hd1 := threeTermRatio_natDegree hrec ha hb h0 h1 hc0 hρ hc1 hβ hαβ (n + 1)
  rw [leadingCoeff, leadingCoeff, hd0, hd1]
  exact hR.2

theorem threeTermRatio_ne_zero (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hρ : 0 < ρ) (hc1 : ρ * (P 0).coeff D₀ ≤ (P 1).coeff (D₀ + d))
    (hβ : ∀ n, (b n).coeff (2 * d) ≤ 0)
    (hαβ : ∀ n, ρ ^ 2 ≤ ρ * (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    P n ≠ 0 :=
  leadingCoeff_ne_zero.mp
    (threeTermRatio_leadingCoeff_pos hrec ha hb h0 h1 hc0 hρ hc1 hβ hαβ n).ne'

end Ratio

section EvalZero

/-! ### Values at zero

Evaluation at `0` is multiplicative, so `x n = (P n).eval 0` satisfies the scalar
recurrence `x (n + 2) = (a n).eval 0 * x (n + 1) + (b n).eval 0 * x n`, with no
degree hypotheses.  The two positivity regimes of the top coefficients apply
verbatim. -/

private theorem threeTerm_eval_zero_rec (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (n : ℕ) :
    (P (n + 2)).eval 0 = (a n).eval 0 * (P (n + 1)).eval 0 + (b n).eval 0 * (P n).eval 0 := by
  rw [hrec n, eval_add, eval_mul, eval_mul]

/-- Rows of `P (n + 2) = a n * P (n + 1) + b n * P n` are positive at `0` when the
first two rows are, `a n` and `b n` are nonnegative at `0`, and their values at `0`
do not both vanish. -/
theorem threeTerm_eval_zero_pos (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (h0 : 0 < (P 0).eval 0) (h1 : 0 < (P 1).eval 0)
    (ha : ∀ n, 0 ≤ (a n).eval 0) (hb : ∀ n, 0 ≤ (b n).eval 0)
    (hab : ∀ n, 0 < (a n).eval 0 + (b n).eval 0) (n : ℕ) :
    0 < (P n).eval 0 :=
  (scalar_of_invariant (s := fun n => (P n).eval 0) (threeTerm_eval_zero_rec hrec)
    (fun x y => 0 < x ∧ 0 < y) ⟨h0, h1⟩ (pos_invariant ha hb hab) n).1

/-- The growth-ratio version of `threeTerm_eval_zero_pos`, for `b n` nonpositive
at `0`: if `ρ > 0`, `ρ (P 0)(0) ≤ (P 1)(0)` and `ρ ^ 2 ≤ ρ a n(0) + b n(0)`, then
`(P (n + 1))(0) ≥ ρ (P n)(0) > 0` throughout. -/
theorem threeTermRatio_eval_zero_pos {ρ : ℝ}
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (h0 : 0 < (P 0).eval 0) (hρ : 0 < ρ) (h1 : ρ * (P 0).eval 0 ≤ (P 1).eval 0)
    (hb : ∀ n, (b n).eval 0 ≤ 0) (hab : ∀ n, ρ ^ 2 ≤ ρ * (a n).eval 0 + (b n).eval 0)
    (n : ℕ) : 0 < (P n).eval 0 :=
  (scalar_of_invariant (s := fun n => (P n).eval 0) (threeTerm_eval_zero_rec hrec)
    (fun x y => 0 < x ∧ ρ * x ≤ y) ⟨h0, h1⟩ (ratio_invariant hρ hb hab) n).1

/-- OEIS A113413: `P (n + 2) = (1 + X) P (n + 1) + X P n` with `P 0 = 1`,
`P 1 = 2 + X`. -/
example (P : ℕ → ℝ[X]) (h0 : P 0 = 1) (h1 : P 1 = 2 + X)
    (hrec : ∀ n, P (n + 2) = (1 + X) * P (n + 1) + X * P n) (n : ℕ) :
    0 < (P n).eval 0 :=
  threeTerm_eval_zero_pos (a := fun _ => 1 + X) (b := fun _ => X) hrec (by simp [h0])
    (by simp [h1]) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) n

/-- A Narayana-type scalar recurrence (the values at `0` of OEIS A001263): `b n` is
negative at `0`, and `ρ = 1` works since `a n (0) + b n (0) = 1`. -/
example (P : ℕ → ℝ[X]) (h0 : P 0 = 1) (h1 : P 1 = 1)
    (hrec : ∀ n, P (n + 2) =
      C (((2 : ℝ) * n + 5) / (n + 4)) * P (n + 1) - C (((n : ℝ) + 1) / (n + 4)) * P n)
    (n : ℕ) : 0 < (P n).eval 0 := by
  refine threeTermRatio_eval_zero_pos (ρ := 1)
    (a := fun n => C (((2 : ℝ) * n + 5) / (n + 4)))
    (b := fun n => -C (((n : ℝ) + 1) / (n + 4))) (fun n => by rw [hrec n]; ring)
    (by simp [h0]) one_pos (by simp [h0, h1]) (fun _ => ?_) (fun n => ?_) n
  · simp only [eval_neg, eval_C, Left.neg_nonpos_iff]
    positivity
  · simp only [eval_C, eval_neg]
    rw [one_pow, one_mul, ← sub_eq_add_neg, ← sub_div, le_div_iff₀ (by positivity)]
    linarith

end EvalZero

section Half

/-! ### Half growth

If `a n` is a constant and `natDegree (b n) ≤ d`, the degree grows by `d` every
second step: `P n` has degree `D₀ + d ⌊(n + e) / 2⌋`, where `e ∈ {0, 1}` records
whether `P 1` already has the larger degree (Fibonacci-type polynomials).  In the
steps where `P (n + 1)` stays below the new degree, only `b n * P n` reaches it,
so the top coefficients stay positive when `a n ≥ 0` and `b n` has a positive
top coefficient. -/

/-- One half-growth step: the degree bound and the coefficient in the bounding
degree. -/
theorem threeTermHalf_step (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (hb : ∀ n, (b n).natDegree ≤ d) (e n : ℕ)
    (h0 : (P n).natDegree ≤ D₀ + d * ((n + e) / 2))
    (h1 : (P (n + 1)).natDegree ≤ D₀ + d * ((n + 1 + e) / 2)) :
    (P (n + 2)).natDegree ≤ D₀ + d * ((n + 2 + e) / 2) ∧
      (P (n + 2)).coeff (D₀ + d * ((n + 2 + e) / 2)) =
        (a n).coeff 0 * (P (n + 1)).coeff (D₀ + d * ((n + 2 + e) / 2)) +
          (b n).coeff d * (P n).coeff (D₀ + d * ((n + e) / 2)) := by
  have hk : (n + 2 + e) / 2 = (n + e) / 2 + 1 := by lia
  have hmono : D₀ + d * ((n + 1 + e) / 2) ≤ D₀ + d * ((n + 2 + e) / 2) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left d (by lia)) D₀
  have e0 : D₀ + d * ((n + 2 + e) / 2) = d + (D₀ + d * ((n + e) / 2)) := by rw [hk]; ring
  have hcoeffA : ∀ k, (a n * P (n + 1)).coeff k = (a n).coeff 0 * (P (n + 1)).coeff k := by
    intro k
    conv_lhs => rw [eq_C_of_natDegree_le_zero (ha n)]
    exact coeff_C_mul _
  rw [hrec n]
  refine ⟨natDegree_add_le_of_degree_le ?_ ?_, ?_⟩
  · refine (natDegree_mul_le_of_le (ha n) h1).trans ?_
    rw [zero_add]
    exact hmono
  · rw [e0]; exact natDegree_mul_le_of_le (hb n) h0
  · rw [coeff_add, hcoeffA, e0, coeff_mul_add_of_natDegree_le (hb n) h0]

/-- The half-growth induction: degree bounds and positive top coefficients for two
consecutive rows. -/
theorem threeTermHalf_top (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (hb : ∀ n, (b n).natDegree ≤ d) {e : ℕ} (he : e ≤ 1)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d * e)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d * e))
    (hα : ∀ n, 0 ≤ (a n).coeff 0) (hβ : ∀ n, 0 < (b n).coeff d) :
    ∀ n, (P n).natDegree ≤ D₀ + d * ((n + e) / 2) ∧
      (P (n + 1)).natDegree ≤ D₀ + d * ((n + 1 + e) / 2) ∧
      0 < (P n).coeff (D₀ + d * ((n + e) / 2)) ∧
      0 < (P (n + 1)).coeff (D₀ + d * ((n + 1 + e) / 2))
  | 0 => by
      have he0 : (0 + e) / 2 = 0 := by lia
      have he1 : (0 + 1 + e) / 2 = e := by lia
      rw [he0, he1, mul_zero, add_zero]
      exact ⟨h0, h1, hc0, hc1⟩
  | n + 1 => by
      obtain ⟨hn0, hn1, hp0, hp1⟩ :=
        threeTermHalf_top hrec ha hb he h0 h1 hc0 hc1 hα hβ n
      have hs := threeTermHalf_step hrec ha hb e n hn0 hn1
      have hidx : n + 1 + 1 = n + 2 := rfl
      have hidx' : n + 1 + 1 + e = n + 2 + e := by lia
      rw [hidx, hidx']
      refine ⟨hn1, hs.1, hp1, ?_⟩
      rw [hs.2]
      -- the first summand is `α n` times the top coefficient or times `0`
      have hfirst : 0 ≤ (P (n + 1)).coeff (D₀ + d * ((n + 2 + e) / 2)) := by
        have hmono : D₀ + d * ((n + 1 + e) / 2) ≤ D₀ + d * ((n + 2 + e) / 2) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left d (by lia)) D₀
        rcases hmono.eq_or_lt with h | h
        · rw [← h]; exact hp1.le
        · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hn1 h)]
      nlinarith [mul_nonneg (hα n) hfirst, mul_pos (hβ n) hp0]

private theorem half_pos (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (hb : ∀ n, (b n).natDegree ≤ d) {e : ℕ} (he : e ≤ 1)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d * e)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d * e))
    (hα : ∀ n, 0 ≤ (a n).coeff 0) (hβ : ∀ n, 0 < (b n).coeff d) (n : ℕ) :
    (P n).natDegree = D₀ + d * ((n + e) / 2) ∧ 0 < (P n).leadingCoeff := by
  obtain ⟨hle, -, hpos, -⟩ := threeTermHalf_top hrec ha hb he h0 h1 hc0 hc1 hα hβ n
  have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hle hpos.ne'
  exact ⟨hdeg, by rwa [leadingCoeff, hdeg]⟩

theorem threeTermHalf_natDegree (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (hb : ∀ n, (b n).natDegree ≤ d) {e : ℕ} (he : e ≤ 1)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d * e)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d * e))
    (hα : ∀ n, 0 ≤ (a n).coeff 0) (hβ : ∀ n, 0 < (b n).coeff d) (n : ℕ) :
    (P n).natDegree = D₀ + d * ((n + e) / 2) :=
  (half_pos hrec ha hb he h0 h1 hc0 hc1 hα hβ n).1

theorem threeTermHalf_leadingCoeff_pos (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (hb : ∀ n, (b n).natDegree ≤ d) {e : ℕ} (he : e ≤ 1)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d * e)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d * e))
    (hα : ∀ n, 0 ≤ (a n).coeff 0) (hβ : ∀ n, 0 < (b n).coeff d) (n : ℕ) :
    0 < (P n).leadingCoeff :=
  (half_pos hrec ha hb he h0 h1 hc0 hc1 hα hβ n).2

theorem threeTermHalf_ne_zero (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (hb : ∀ n, (b n).natDegree ≤ d) {e : ℕ} (he : e ≤ 1)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d * e)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d * e))
    (hα : ∀ n, 0 ≤ (a n).coeff 0) (hβ : ∀ n, 0 < (b n).coeff d) (n : ℕ) :
    P n ≠ 0 :=
  leadingCoeff_ne_zero.mp
    (threeTermHalf_leadingCoeff_pos hrec ha hb he h0 h1 hc0 hc1 hα hβ n).ne'

end Half

/-! ### Two-step products -/

/-- Rows of a two-step product `P (n + 2) = q * P n`. -/
theorem twoStepProduct_rows {P : ℕ → ℝ[X]} {q : ℝ[X]} (hrec : ∀ n, P (n + 2) = q * P n) :
    ∀ m, P (2 * m) = q ^ m * P 0 ∧ P (2 * m + 1) = q ^ m * P 1
  | 0 => by simp
  | m + 1 => by
      obtain ⟨h0, h1⟩ := twoStepProduct_rows hrec m
      refine ⟨?_, ?_⟩
      · rw [show 2 * (m + 1) = 2 * m + 2 by ring, hrec, h0]; ring
      · rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, hrec, h1]; ring

/-- The degrees of a two-step product `P (n + 2) = q * P n`: the row `P n` is
`q ^ (n / 2) * P (n % 2)`, so its degree is `n / 2 * deg q + deg P (n % 2)`, or `0` when the
base row of its parity vanishes. -/
theorem twoStepProduct_natDegree {P : ℕ → ℝ[X]} {q : ℝ[X]} (hrec : ∀ n, P (n + 2) = q * P n)
    (hq : q ≠ 0) (n : ℕ) :
    (P n).natDegree =
      if P (n % 2) = 0 then 0 else n / 2 * q.natDegree + (P (n % 2)).natDegree := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨h0, -⟩ := twoStepProduct_rows hrec m
    have hm : 2 * m / 2 = m := by lia
    rw [h0, Nat.mul_mod_right, hm]
    by_cases hP : P 0 = 0
    · simp [hP]
    · simp only [hP, ↓reduceIte]
      rw [natDegree_mul (pow_ne_zero _ hq) hP, natDegree_pow]
  · obtain ⟨-, h1⟩ := twoStepProduct_rows hrec m
    have hm : (2 * m + 1) / 2 = m := by lia
    have hr : (2 * m + 1) % 2 = 1 := by lia
    rw [h1, hr, hm]
    by_cases hP : P 1 = 0
    · simp [hP]
    · simp only [hP, ↓reduceIte]
      rw [natDegree_mul (pow_ne_zero _ hq) hP, natDegree_pow]

end RealRooted
