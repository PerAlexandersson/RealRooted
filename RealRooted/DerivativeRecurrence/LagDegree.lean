import Mathlib.Tactic.ComputeDegree
import RealRooted.ThreeTermRecurrence.Degree

/-!
# Degrees of derivative-lag recurrences

For `P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` with
`natDegree (U n) ≤ d`, `natDegree (V n) ≤ d + 1` and `natDegree (W n) ≤ 2 d`,
the coefficients `t n` of `P n` in degree `D₀ + d n` satisfy the scalar recurrence

`t (n + 2) = α n * t (n + 1) + β n * t n`,

`α n = (U n)_d + (V n)_{d+1} (D₀ + d (n + 1))`,   `β n = (W n)_{2d}`.

So the rows have degree exactly `D₀ + d n`, with positive leading coefficients,
as soon as `α n, β n ≥ 0` and `α n + β n > 0`.  This is the three-term argument of
`RealRooted.ThreeTermRecurrence.Degree`, with the derivative term contributing
`(V n)_{d+1}` times the degree of `P (n + 1)`.

The interlacing backend for this shape is
`RealRooted.LiuWang.strictInterl_derivative_lag_sequence_of_root_signs`.

## Main results

* `derivLag_step`: the degree bound and the top coefficient of one step.
* `derivLag_natDegree`, `derivLag_ne_zero`, `derivLag_leadingCoeff_pos`.
-/

open Polynomial

namespace RealRooted

variable {P U V W : ℕ → ℝ[X]} {d D₀ : ℕ}

/-- One step of a derivative-lag recurrence: the degree bound and the coefficient
in the bounding degree. -/
theorem derivLag_step
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hU : ∀ n, (U n).natDegree ≤ d) (hV : ∀ n, (V n).natDegree ≤ d + 1)
    (hW : ∀ n, (W n).natDegree ≤ 2 * d) (n : ℕ)
    (h0 : (P n).natDegree ≤ D₀ + d * n) (h1 : (P (n + 1)).natDegree ≤ D₀ + d * (n + 1)) :
    (P (n + 2)).natDegree ≤ D₀ + d * (n + 2) ∧
      (P (n + 2)).coeff (D₀ + d * (n + 2)) =
        ((U n).coeff d + (V n).coeff (d + 1) * ((D₀ + d * (n + 1) : ℕ) : ℝ)) *
            (P (n + 1)).coeff (D₀ + d * (n + 1)) +
          (W n).coeff (2 * d) * (P n).coeff (D₀ + d * n) := by
  have e1 : D₀ + d * (n + 2) = D₀ + d * (n + 1) + d := by ring
  have e0 : D₀ + d * (n + 2) = 2 * d + (D₀ + d * n) := by ring
  have hUd := natDegree_mul_iterate_derivative_le (j := 0) (hU n) h1
  have hUc := coeff_mul_iterate_derivative_of_natDegree_le (j := 0) (hU n) h1
  have hVd := natDegree_mul_iterate_derivative_le (j := 1) (hV n) h1
  have hVc := coeff_mul_iterate_derivative_of_natDegree_le (j := 1) (hV n) h1
  simp only [Function.iterate_one, Function.iterate_zero, id_eq, add_zero,
    Nat.descFactorial_one, Nat.descFactorial_zero, Nat.cast_one, mul_one] at hUd hUc hVd hVc
  rw [hrec n]
  refine ⟨natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_, ?_⟩
  · rw [e1]; exact hUd
  · rw [e1]; exact hVd
  · rw [e0]; exact natDegree_mul_le_of_le (hW n) h0
  · rw [coeff_add, coeff_add, e1, hUc, hVc, ← e1, e0,
      coeff_mul_add_of_natDegree_le (hW n) h0]
    ring

/-- Rows of `P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))' + W n * P n` have
degree `D₀ + d * n` when the first two rows have positive coefficients in degrees
`D₀` and `D₀ + d` and the top multipliers
`α n = (U n)_d + (V n)_{d+1} (D₀ + d (n + 1))` and `β n = (W n)_{2d}` are
nonnegative with positive sum. -/
theorem derivLag_natDegree
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hU : ∀ n, (U n).natDegree ≤ d) (hV : ∀ n, (V n).natDegree ≤ d + 1)
    (hW : ∀ n, (W n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ (U n).coeff d + (V n).coeff (d + 1) * ((D₀ + d * (n + 1) : ℕ) : ℝ))
    (hβ : ∀ n, 0 ≤ (W n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (U n).coeff d + (V n).coeff (d + 1) * ((D₀ + d * (n + 1) : ℕ) : ℝ) +
      (W n).coeff (2 * d)) (n : ℕ) :
    (P n).natDegree = D₀ + d * n :=
  (twoStep_natDegree_eq_and_leadingCoeff_pos (derivLag_step hrec hU hV hW) h0 h1 hc0 hc1
    hα hβ hαβ n).1

/-- The positive-leading-coefficient companion of `derivLag_natDegree`. -/
theorem derivLag_leadingCoeff_pos
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hU : ∀ n, (U n).natDegree ≤ d) (hV : ∀ n, (V n).natDegree ≤ d + 1)
    (hW : ∀ n, (W n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ (U n).coeff d + (V n).coeff (d + 1) * ((D₀ + d * (n + 1) : ℕ) : ℝ))
    (hβ : ∀ n, 0 ≤ (W n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (U n).coeff d + (V n).coeff (d + 1) * ((D₀ + d * (n + 1) : ℕ) : ℝ) +
      (W n).coeff (2 * d)) (n : ℕ) :
    0 < (P n).leadingCoeff :=
  (twoStep_natDegree_eq_and_leadingCoeff_pos (derivLag_step hrec hU hV hW) h0 h1 hc0 hc1
    hα hβ hαβ n).2

/-- The nonvanishing companion of `derivLag_natDegree`. -/
theorem derivLag_ne_zero
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hU : ∀ n, (U n).natDegree ≤ d) (hV : ∀ n, (V n).natDegree ≤ d + 1)
    (hW : ∀ n, (W n).natDegree ≤ 2 * d)
    (h0 : (P 0).natDegree ≤ D₀) (h1 : (P 1).natDegree ≤ D₀ + d)
    (hc0 : 0 < (P 0).coeff D₀) (hc1 : 0 < (P 1).coeff (D₀ + d))
    (hα : ∀ n, 0 ≤ (U n).coeff d + (V n).coeff (d + 1) * ((D₀ + d * (n + 1) : ℕ) : ℝ))
    (hβ : ∀ n, 0 ≤ (W n).coeff (2 * d))
    (hαβ : ∀ n, 0 < (U n).coeff d + (V n).coeff (d + 1) * ((D₀ + d * (n + 1) : ℕ) : ℝ) +
      (W n).coeff (2 * d)) (n : ℕ) :
    P n ≠ 0 :=
  leadingCoeff_ne_zero.mp
    (derivLag_leadingCoeff_pos hrec hU hV hW h0 h1 hc0 hc1 hα hβ hαβ n).ne'

section Examples

/-- The second-order family of `RealRooted.natDegree_of_second_order_derivative`,
`P (n + 2) = (a X - a X ^ 2) P (n + 1)' + (1 + b n X) P (n + 1) + c X P n` with
`b n - a (n + 1) = 1` (for instance OEIS A144440 with `a = 3`, `b n = 3 n + 4`,
`c = 3`): here `d = 1`, `α n = b n - a (n + 1) = 1` and `β n = 0`. -/
example (P : ℕ → ℝ[X]) (a c : ℝ) (b : ℕ → ℝ) (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C (b n) * X) * P (n + 1) + (C c * X) * P n)
    (hcancel : ∀ n, b n - a * ((n : ℝ) + 1) = 1) (n : ℕ) :
    (P n).natDegree = n := by
  have hα : ∀ n : ℕ, (C 1 + C (b n) * X).coeff 1 +
      (C a * X + C (-a) * X ^ 2).coeff (1 + 1) * ((0 + 1 * (n + 1) : ℕ) : ℝ) = 1 := by
    intro n
    simp [coeff_one]
    linarith [hcancel n]
  have hβ : ∀ n : ℕ, (C c * X : ℝ[X]).coeff (2 * 1) = 0 := fun _ => by simp
  simpa using derivLag_natDegree (P := P) (d := 1) (D₀ := 0)
    (U := fun n => C 1 + C (b n) * X) (V := fun _ => C a * X + C (-a) * X ^ 2)
    (W := fun _ => C c * X) (fun n => by rw [hrec n]; ring)
    (fun _ => by compute_degree!) (fun _ => by compute_degree!)
    (fun _ => by compute_degree!) (by simp [h0]) (by rw [h1]; compute_degree!)
    (by simp [h0]) (by simp [h1, coeff_one]) (fun n => by rw [hα n]; norm_num)
    (fun n => by rw [hβ n]) (fun n => by rw [hα n, hβ n]; norm_num) n

end Examples

end RealRooted
