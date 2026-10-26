module

public import RealRooted.SymmetricDecomposition.FPolynomial

/-!
# Derivative recurrences for the `f`-polynomial transform

A first-order derivative recurrence for `Q` transforms into a first-order
derivative recurrence for `fPolynomial n (Q n)`.
-/

public section

open Polynomial

namespace RealRooted

private lemma fPolynomial_deriv_term (d k : ℕ) (hk : k ≤ d) (c : ℝ) :
    (X + 1) ^ 2 * derivative (C c * X ^ k * (X + 1) ^ (d - k)) =
      C (d : ℝ) * (X + 1) * (C c * X ^ k * (X + 1) ^ (d - k)) +
        C (c * k) * X ^ (k - 1) * (X + 1) ^ (d + 1 - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = k + m := ⟨d - k, by lia⟩
  rw [Nat.add_sub_cancel_left, show k + m + 1 - k = m + 1 by lia]
  rcases k with _ | j <;> rcases m with _ | i <;>
    simp [derivative_mul, derivative_pow] <;> ring

/-- The derivative rule for the `f`-polynomial transform. -/
theorem fPolynomial_derivative {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    (X + 1) ^ 2 * (fPolynomial d p).derivative =
      C (d : ℝ) * (X + 1) * fPolynomial d p + fPolynomial d p.derivative := by
  have hT : fPolynomial d p.derivative = ∑ k ∈ Finset.range (d + 1),
      C (p.coeff k * k) * X ^ (k - 1) * (X + 1) ^ (d + 1 - k) := by
    have h2 := Finset.sum_range_succ (fun k => C (p.coeff k * k) * X ^ (k - 1) *
      (X + 1) ^ (d + 1 - k)) (d + 1)
    rw [Finset.sum_range_succ'] at h2
    rw [coeff_eq_zero_of_natDegree_lt (p := p) (n := d + 1) (by lia)] at h2
    simp only [zero_mul, map_zero, add_zero, CharP.cast_eq_zero, mul_zero] at h2
    refine Eq.trans ?_ h2
    unfold fPolynomial
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [coeff_derivative, Nat.add_sub_add_right]
  rw [hT]
  unfold fPolynomial
  rw [derivative_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact fPolynomial_deriv_term d k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) _

private lemma fPolynomial_mul_deg2 {d : ℕ} {a r : ℝ[X]} (ha : a.natDegree ≤ 2)
    (hr : r.natDegree ≤ d) :
    fPolynomial (d + 2) (a * r) = fPolynomial 2 a * fPolynomial d r := by
  have ha' : a = C (a.coeff 0) + C (a.coeff 1) * X + C (a.coeff 2) * X ^ 2 := by
    conv_lhs => rw [as_sum_range' a 3 (by lia)]
    simp [Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial]
  have hfa : fPolynomial 2 a = C (a.coeff 0) * (X + 1) ^ 2 +
      C (a.coeff 1) * X * (X + 1) + C (a.coeff 2) * X ^ 2 := by
    simp [fPolynomial, Finset.sum_range_succ]
  have har : a * r = C (a.coeff 0) * r + C (a.coeff 1) * (X * r) +
      C (a.coeff 2) * (X * (X * r)) := by
    conv_lhs => rw [ha']
    ring
  have hXr : (X * r).natDegree ≤ d + 1 :=
    natDegree_mul_le.trans (by rw [natDegree_X]; lia)
  have e1 : fPolynomial (d + 2) r = (X + 1) ^ 2 * fPolynomial d r := by
    rw [fPolynomial_succ_of_natDegree_le (hr.trans (by lia)),
      fPolynomial_succ_of_natDegree_le hr]
    ring
  have e2 : fPolynomial (d + 2) (X * r) = (X + 1) * X * fPolynomial d r := by
    rw [fPolynomial_succ_of_natDegree_le hXr, fPolynomial_X_mul_succ]
    ring
  have e3 : fPolynomial (d + 2) (X * (X * r)) = X * X * fPolynomial d r := by
    rw [fPolynomial_X_mul_succ, fPolynomial_X_mul_succ]
    ring
  rw [har, fPolynomial_add, fPolynomial_add, fPolynomial_C_mul, fPolynomial_C_mul,
    fPolynomial_C_mul, e1, e2, e3, hfa]
  ring

private lemma fPolynomial_mul_deg1 {d : ℕ} {b r : ℝ[X]} (hb : b.natDegree ≤ 1)
    (hr : r.natDegree ≤ d) :
    fPolynomial (d + 1) (b * r) = fPolynomial 1 b * fPolynomial d r := by
  have hb' : b = C (b.coeff 0) + C (b.coeff 1) * X := by
    conv_lhs => rw [as_sum_range' b 2 (by lia)]
    simp [Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial]
  have hfb : fPolynomial 1 b = C (b.coeff 0) * (X + 1) + C (b.coeff 1) * X := by
    simp [fPolynomial, Finset.sum_range_succ]
  have hbr : b * r = C (b.coeff 0) * r + C (b.coeff 1) * (X * r) := by
    conv_lhs => rw [hb']
    ring
  rw [hbr, fPolynomial_add, fPolynomial_C_mul, fPolynomial_C_mul,
    fPolynomial_succ_of_natDegree_le hr, fPolynomial_X_mul_succ, hfb]
  ring

/-- The transform of a first-order derivative step for a quadratic coefficient. -/
theorem fPolynomial_derivativeRecurrence_step {d : ℕ} {a b q : ℝ[X]} (ha : a.natDegree ≤ 2)
    (hb : b.natDegree ≤ 1) (hq : q.natDegree ≤ d)
    (hstep : (a * q.derivative + b * q).natDegree ≤ d + 1) :
    fPolynomial (d + 1) (a * q.derivative + b * q) =
      (X + 1) * fPolynomial 2 a * (fPolynomial d q).derivative +
        (fPolynomial 1 b - C (d : ℝ) * fPolynomial 2 a) * fPolynomial d q := by
  have hq' : q.derivative.natDegree ≤ d :=
    (natDegree_derivative_le q).trans (by lia)
  have hbq : (b * q).natDegree ≤ d + 1 :=
    natDegree_mul_le.trans (by lia)
  have h1 := fPolynomial_succ_of_natDegree_le hstep
  have h2 : fPolynomial (d + 1 + 1) (a * q.derivative + b * q) =
      fPolynomial 2 a * fPolynomial d q.derivative +
        (X + 1) * (fPolynomial 1 b * fPolynomial d q) := by
    rw [fPolynomial_add, fPolynomial_mul_deg2 ha hq',
      fPolynomial_succ_of_natDegree_le hbq, fPolynomial_mul_deg1 hb hq]
  have h3 := fPolynomial_derivative hq
  have hX : (X + 1 : ℝ[X]) ≠ 0 := by simpa using X_add_C_ne_zero (1 : ℝ)
  apply mul_left_cancel₀ hX
  linear_combination -h1 + h2 - fPolynomial 2 a * h3

/-- Rows of a first-order derivative recurrence transform to rows of the transformed recurrence. -/
theorem eq_fPolynomial_of_derivRec {P Q a b : ℕ → ℝ[X]}
    (ha : ∀ n, (a n).natDegree ≤ 2) (hb : ∀ n, (b n).natDegree ≤ 1)
    (hQ : ∀ n, Q (n + 1) = a n * (Q n).derivative + b n * Q n)
    (hQdeg : ∀ n, (Q n).natDegree ≤ n)
    (hP : ∀ n, P (n + 1) = (X + 1) * fPolynomial 2 (a n) * (P n).derivative +
      (fPolynomial 1 (b n) - C (n : ℝ) * fPolynomial 2 (a n)) * P n)
    (h0 : P 0 = fPolynomial 0 (Q 0)) (n : ℕ) :
    P n = fPolynomial n (Q n) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hP, ih, hQ]
    exact (fPolynomial_derivativeRecurrence_step (ha n) (hb n) (hQdeg n)
      (by rw [← hQ]; exact hQdeg (n + 1))).symm

/-- A derivative recurrence with quadratic and linear coefficients increases degree
by at most one at each step. -/
theorem natDegree_le_of_derivRec {Q a b : ℕ → ℝ[X]} (ha : ∀ n, (a n).natDegree ≤ 2)
    (hb : ∀ n, (b n).natDegree ≤ 1)
    (hQ : ∀ n, Q (n + 1) = a n * (Q n).derivative + b n * Q n)
    (h0 : (Q 0).natDegree = 0) (n : ℕ) : (Q n).natDegree ≤ n := by
  induction n with
  | zero => exact h0.le
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        rw [hQ 0]
        have hder : (Q 0).derivative = 0 := Polynomial.derivative_eq_zero.mpr h0
        rw [hder, mul_zero, zero_add]
        have hb0 := hb 0
        exact natDegree_mul_le.trans (by lia)
      · rw [hQ n]
        apply natDegree_add_le_of_degree_le
        · apply natDegree_mul_le.trans
          have hder : (Q n).derivative.natDegree ≤ n - 1 := by
            rw [Polynomial.natDegree_derivative]
            exact Nat.sub_le_sub_right ih 1
          have han := ha n
          lia
        · apply natDegree_mul_le.trans
          have hbn := hb n
          lia

/-- The recurrence-transform identity assuming only a constant initial row. -/
theorem eq_fPolynomial_of_derivativeRecurrence_of_natDegree_zero {P Q a b : ℕ → ℝ[X]}
    (ha : ∀ n, (a n).natDegree ≤ 2) (hb : ∀ n, (b n).natDegree ≤ 1)
    (hQ : ∀ n, Q (n + 1) = a n * (Q n).derivative + b n * Q n)
    (h0deg : (Q 0).natDegree = 0)
    (hP : ∀ n, P (n + 1) = (X + 1) * fPolynomial 2 (a n) * (P n).derivative +
      (fPolynomial 1 (b n) - C (n : ℝ) * fPolynomial 2 (a n)) * P n)
    (h0 : P 0 = fPolynomial 0 (Q 0)) (n : ℕ) :
    P n = fPolynomial n (Q n) := by
  exact eq_fPolynomial_of_derivRec ha hb hQ
    (natDegree_le_of_derivRec ha hb hQ h0deg) hP h0 n

/-- Rows that are `f`-polynomial transforms of splitting rows split. -/
theorem splits_of_eq_fPolynomial {P Q : ℕ → ℝ[X]}
    (hPQ : ∀ n, P n = fPolynomial n (Q n))
    (hdeg : ∀ n, (Q n).natDegree ≤ n) (hs : ∀ n, (Q n).Splits) (n : ℕ) :
    (P n).Splits := by
  rw [hPQ n]
  exact splits_fPolynomial (hdeg n) (hs n)

/-- The degree-two transform in coefficient form. -/
theorem fPolynomial_two (p : ℝ[X]) :
    fPolynomial 2 p =
      C (p.coeff 0) * (X + 1) ^ 2 + C (p.coeff 1) * X * (X + 1) + C (p.coeff 2) * X ^ 2 := by
  simp [fPolynomial, Finset.sum_range_succ]

/-- The degree-one transform in coefficient form. -/
theorem fPolynomial_one (p : ℝ[X]) :
    fPolynomial 1 p = C (p.coeff 0) * (X + 1) + C (p.coeff 1) * X := by
  simp [fPolynomial, Finset.sum_range_succ]

end RealRooted
