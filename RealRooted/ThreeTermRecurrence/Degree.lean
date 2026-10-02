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
* `threeTerm_top_of_invariant`: the induction for any invariant `R (t n) (t (n + 1))`
  preserved by the scalar recurrence and forcing `t n > 0`.
* `threeTermPos_natDegree`, `threeTermPos_ne_zero`, `threeTermPos_leadingCoeff_pos`
  and the `threeTermRatio_*` versions.
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

/-- The induction behind the three-term degree theorems: an invariant `R` of
consecutive top coefficients, preserved by the scalar recurrence and forcing
positivity of the first entry. -/
theorem threeTerm_top_of_invariant (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (R : ℝ → ℝ → Prop) (hR01 : R ((P 0).coeff D₀) ((P 1).coeff (D₀ + d)))
    (hRpos : ∀ x y, R x y → 0 < x)
    (hRstep : ∀ n x y, R x y → R y ((a n).coeff d * y + (b n).coeff (2 * d) * x)) :
    ∀ n, (P n).natDegree ≤ D₀ + d * n ∧ (P (n + 1)).natDegree ≤ D₀ + d * (n + 1) ∧
      R ((P n).coeff (D₀ + d * n)) ((P (n + 1)).coeff (D₀ + d * (n + 1)))
  | 0 => ⟨by simpa using h0, by simpa using h1, by simpa using hR01⟩
  | n + 1 => by
      obtain ⟨hn0, hn1, hR⟩ := threeTerm_top_of_invariant hrec ha hb h0 h1 R hR01 hRpos hRstep n
      have hs := threeTerm_step hrec ha hb n hn0 hn1
      exact ⟨hn1, hs.1, by rw [hs.2]; exact hRstep n _ _ hR⟩

private theorem top_pos_of_invariant (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (R : ℝ → ℝ → Prop) (hR01 : R ((P 0).coeff D₀) ((P 1).coeff (D₀ + d)))
    (hRpos : ∀ x y, R x y → 0 < x)
    (hRstep : ∀ n x y, R x y → R y ((a n).coeff d * y + (b n).coeff (2 * d) * x)) (n : ℕ) :
    (P n).natDegree = D₀ + d * n ∧ 0 < (P n).leadingCoeff := by
  obtain ⟨hle, -, hR⟩ := threeTerm_top_of_invariant hrec ha hb h0 h1 R hR01 hRpos hRstep n
  have hpos := hRpos _ _ hR
  have hdeg := natDegree_eq_of_le_of_coeff_ne_zero hle hpos.ne'
  exact ⟨hdeg, by rwa [leadingCoeff, hdeg]⟩

section Positive

/-- Nonnegative top multipliers: `α n, β n ≥ 0` and `α n + β n > 0`. -/
private theorem pos_invariant
    (hα : ∀ n, 0 ≤ (a n).coeff d) (hβ : ∀ n, 0 ≤ (b n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) (x y : ℝ)
    (h : 0 < x ∧ 0 < y) :
    0 < y ∧ 0 < (a n).coeff d * y + (b n).coeff (2 * d) * x := by
  refine ⟨h.2, ?_⟩
  rcases (hα n).lt_or_eq with hα' | hα'
  · nlinarith [mul_nonneg (hβ n) h.1.le, mul_pos hα' h.2]
  · have hβpos : 0 < (b n).coeff (2 * d) := by linarith [hαβ n]
    rw [← hα']
    nlinarith [mul_pos hβpos h.1]

theorem threeTermPos_natDegree (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ (a n).coeff d) (hβ : ∀ n, 0 ≤ (b n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    (P n).natDegree = D₀ + d * n :=
  (top_pos_of_invariant hrec ha hb h0 h1 (fun x y => 0 < x ∧ 0 < y) ⟨hc0, hc1⟩
    (fun _ _ h => h.1) (pos_invariant hα hβ hαβ) n).1

theorem threeTermPos_leadingCoeff_pos (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ (a n).coeff d) (hβ : ∀ n, 0 ≤ (b n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    0 < (P n).leadingCoeff :=
  (top_pos_of_invariant hrec ha hb h0 h1 (fun x y => 0 < x ∧ 0 < y) ⟨hc0, hc1⟩
    (fun _ _ h => h.1) (pos_invariant hα hβ hαβ) n).2

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
private theorem ratio_invariant (hρ : 0 < ρ) (hβ : ∀ n, (b n).coeff (2 * d) ≤ 0)
    (hαβ : ∀ n, ρ ^ 2 ≤ ρ * (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) (x y : ℝ)
    (h : 0 < x ∧ ρ * x ≤ y) :
    0 < y ∧ ρ * y ≤ (a n).coeff d * y + (b n).coeff (2 * d) * x := by
  have hy : 0 < y := lt_of_lt_of_le (mul_pos hρ h.1) h.2
  refine ⟨hy, ?_⟩
  -- `ρ (α y + β x) ≥ (ρ α + β) y ≥ ρ² y`, using `β x ≥ β y / ρ`
  have h1 : (b n).coeff (2 * d) * y ≤ ρ * ((b n).coeff (2 * d) * x) := by
    nlinarith [mul_le_mul_of_nonpos_left h.2 (hβ n)]
  have h2 : ρ * (ρ * y) ≤ ρ * ((a n).coeff d * y + (b n).coeff (2 * d) * x) := by
    nlinarith [mul_le_mul_of_nonneg_right (hαβ n) hy.le]
  exact le_of_mul_le_mul_left h2 hρ

theorem threeTermRatio_natDegree (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hρ : 0 < ρ) (hc1 : ρ * (P 0).coeff D₀ ≤ (P 1).coeff (D₀ + d))
    (hβ : ∀ n, (b n).coeff (2 * d) ≤ 0)
    (hαβ : ∀ n, ρ ^ 2 ≤ ρ * (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    (P n).natDegree = D₀ + d * n :=
  (top_pos_of_invariant hrec ha hb h0 h1 (fun x y => 0 < x ∧ ρ * x ≤ y) ⟨hc0, hc1⟩
    (fun _ _ h => h.1) (ratio_invariant hρ hβ hαβ) n).1

theorem threeTermRatio_leadingCoeff_pos
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ d) (hb : ∀ n, (b n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hρ : 0 < ρ) (hc1 : ρ * (P 0).coeff D₀ ≤ (P 1).coeff (D₀ + d))
    (hβ : ∀ n, (b n).coeff (2 * d) ≤ 0)
    (hαβ : ∀ n, ρ ^ 2 ≤ ρ * (a n).coeff d + (b n).coeff (2 * d)) (n : ℕ) :
    0 < (P n).leadingCoeff :=
  (top_pos_of_invariant hrec ha hb h0 h1 (fun x y => 0 < x ∧ ρ * x ≤ y) ⟨hc0, hc1⟩
    (fun _ _ h => h.1) (ratio_invariant hρ hβ hαβ) n).2

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

end RealRooted
