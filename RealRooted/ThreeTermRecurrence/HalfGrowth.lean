import RealRooted.ThreeTermRecurrence.Interlacing
import RealRooted.ThreeTermRecurrence.Degree

/-!
# Rows two apart of a half-growth three-term recurrence

If `P (n + 2) = a n * P (n + 1) + b n * P n` with every `a n` a positive constant, then
`α n * P (n + 4) = (α (n + 2) α (n + 1) α n + α n * b (n + 2) + α (n + 2) * b (n + 1)) *
  P (n + 2) - α (n + 2) * b (n + 1) * b n * P n`.
Hence the two subsequences `P (2 m)` and `P (2 m + 1)` again satisfy three-term recurrences,
with `b`-coefficient `-(α (n + 2) / α n) * b (n + 1) * b n`.  This is nonpositive whenever
`b (n + 1)` and `b n` never take opposite signs, and the subsequences have full degree growth
when `P` has half growth.
-/

open Polynomial

namespace RealRooted

variable {P a b : ℕ → ℝ[X]} {D₀ e : ℕ}

private theorem half_four_step (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (n : ℕ) :
    C ((a n).coeff 0) * P (n + 4) =
      (C ((a (n + 2)).coeff 0) * C ((a (n + 1)).coeff 0) * C ((a n).coeff 0) +
        C ((a n).coeff 0) * b (n + 2) + C ((a (n + 2)).coeff 0) * b (n + 1)) * P (n + 2) -
      C ((a (n + 2)).coeff 0) * (b (n + 1) * b n) * P n := by
  have h0 := hrec n
  have h1 := hrec (n + 1)
  have h2 := hrec (n + 2)
  rw [← eq_C_of_natDegree_le_zero (ha n)] at *
  rw [← eq_C_of_natDegree_le_zero (ha (n + 1))] at *
  rw [← eq_C_of_natDegree_le_zero (ha (n + 2))] at *
  linear_combination (a n) * h2 + (a n) * (a (n + 2)) * h1 - (a (n + 2)) * (b (n + 1)) * h0

private theorem half_sub_interlaces (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (hα : ∀ n, 0 < (a n).coeff 0)
    (hb : ∀ n r, 0 ≤ (b (n + 1)).eval r * (b n).eval r)
    (hdeg : ∀ n, (P n).natDegree = D₀ + (n + e) / 2) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (s : ℕ) (hbase : Interlaces (P s) (P (s + 2))) (m : ℕ) :
    Interlaces (P (2 * m + s)) (P (2 * m + s + 2)) := by
  have key := threeTerm_interlaces_of_eval_nonpos
    (P := fun m => P (2 * m + s))
    (a := fun m => C ((a (2 * m + s)).coeff 0)⁻¹ *
      (C ((a (2 * m + s + 2)).coeff 0) * C ((a (2 * m + s + 1)).coeff 0) *
        C ((a (2 * m + s)).coeff 0) + C ((a (2 * m + s)).coeff 0) * b (2 * m + s + 2) +
        C ((a (2 * m + s + 2)).coeff 0) * b (2 * m + s + 1)))
    (b := fun m => -(C ((a (2 * m + s + 2)).coeff 0) * C ((a (2 * m + s)).coeff 0)⁻¹ *
      (b (2 * m + s + 1) * b (2 * m + s))))
    (D₀ := D₀ + (s + e) / 2) ?_ ?_ ?_ ?_ ?_ m
  · have hidx : 2 * (m + 1) + s = 2 * m + s + 2 := by lia
    simpa only [hidx] using key
  · intro m
    have hi1 : 2 * (m + 1 + 1) + s = 2 * m + s + 4 := by lia
    have hi2 : 2 * (m + 1) + s = 2 * m + s + 2 := by lia
    simp only [hi1, hi2]
    have hinv : C ((a (2 * m + s)).coeff 0)⁻¹ * C ((a (2 * m + s)).coeff 0) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ (hα _).ne', C_1]
    linear_combination C ((a (2 * m + s)).coeff 0)⁻¹ * half_four_step hrec ha (2 * m + s) -
      P (2 * m + s + 4) * hinv
  · intro m
    simp only [hdeg]
    lia
  · intro m
    exact hpos _
  · intro m r
    have hr := hb (2 * m + s) r
    have h2 := hα (2 * m + s + 2)
    have h0 := inv_pos.mpr (hα (2 * m + s))
    simp only [eval_neg, eval_mul, eval_C]
    nlinarith [mul_nonneg (mul_pos h2 h0).le hr]
  · have h1 : 2 * (0 + 1) + s = s + 2 := by lia
    simpa only [h1, Nat.mul_zero, Nat.zero_add] using hbase

/-- Rows two apart of a half-growth three-term recurrence with positive constant `a n`
interlace when consecutive lags `b n`, `b (n + 1)` never take opposite signs. -/
theorem threeTermHalf_interlaces_add_two
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (hα : ∀ n, 0 < (a n).coeff 0)
    (hb : ∀ n r, 0 ≤ (b (n + 1)).eval r * (b n).eval r)
    (hdeg : ∀ n, (P n).natDegree = D₀ + (n + e) / 2) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (h02 : Interlaces (P 0) (P 2)) (h13 : Interlaces (P 1) (P 3)) (n : ℕ) :
    Interlaces (P n) (P (n + 2)) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · simpa using half_sub_interlaces hrec ha hα hb hdeg hpos 0 h02 m
  · exact half_sub_interlaces hrec ha hα hb hdeg hpos 1 h13 m

/-- Rows of a half-growth three-term recurrence with positive constant `a n` are real-rooted
when consecutive lags `b n`, `b (n + 1)` never take opposite signs. -/
theorem threeTermHalf_ne_zero_and_splits
    (hrec : ∀ n, P (n + 2) = a n * P (n + 1) + b n * P n)
    (ha : ∀ n, (a n).natDegree ≤ 0) (hα : ∀ n, 0 < (a n).coeff 0)
    (hb : ∀ n r, 0 ≤ (b (n + 1)).eval r * (b n).eval r)
    (hdeg : ∀ n, (P n).natDegree = D₀ + (n + e) / 2) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (h02 : Interlaces (P 0) (P 2)) (h13 : Interlaces (P 1) (P 3)) (n : ℕ) :
    P n ≠ 0 ∧ (P n).Splits :=
  (threeTermHalf_interlaces_add_two hrec ha hα hb hdeg hpos h02 h13 n).2.1

end RealRooted
