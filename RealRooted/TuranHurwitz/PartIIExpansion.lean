module

public import RealRooted.TuranHurwitz.PartIICoefficients
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A fixed-index expansion of the recurrence family

This finite expansion is the limit of the binomial approximants. We derive
it from the checked Laguerre normalization rather than a new recurrence.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The recurrence row has an explicit finite expansion in powers of the shifted variable. -/
theorem partIIFamily_eq_sum {c : PartIIParameters} (hc : c.Admissible) (j : ℕ) :
    partIIFamily c j = C (rising (c.a₂ / c.a₁) j / rising (1 / c.sigma) j) *
      ∑ r ∈ Finset.range (j + 1),
        C ((j.choose r : ℝ) * (c.a₁ / c.sigma) ^ (j - r) *
          (c.b₂ / c.sigma) ^ r / rising (c.a₂ / c.a₁) r) * partIIShift c ^ r := by
  let alpha := c.a₂ / c.a₁
  let A := c.a₁ / c.sigma
  let B := c.b₂ / c.sigma
  let R := c.b₂ / c.a₁
  have hAR : A * R = B := by
    dsimp [A, R, B]
    field_simp [hc.a₁_pos.ne', hc.sigma_pos.ne']
  have hpowers {r : ℕ} (hr : r ≤ j) : A ^ j * R ^ r = A ^ (j - r) * B ^ r := by
    rw [← hAR, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hr]
  have h := congrArg (fun p : ℝ[X] =>
      C (partIILaguerreScale c j * rising alpha j) * p.comp (partIILaguerreVariable c))
    (normalized_generalizedLaguerre_eq_sum hc.ratio_pos j)
  have hcancel : C (partIILaguerreScale c j * rising alpha j) *
      C ((rising alpha j)⁻¹) = C (partIILaguerreScale c j) := by
    rw [← map_mul, mul_inv_cancel_right₀ (rising_pos hc.ratio_pos j).ne']
  simp only [mul_comp, C_comp, sum_comp, pow_comp, X_comp] at h
  rw [← mul_assoc, hcancel, ← partIIFamily_eq_generalizedLaguerre hc] at h
  rw [h]
  simp only [Finset.mul_sum, partIILaguerreVariable, mul_pow, ← map_pow,
    ← mul_assoc, ← map_mul]
  apply Finset.sum_congr rfl
  intro r hr
  have hrj : r ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  congr 1
  apply congrArg C
  change (A ^ j / rising (1 / c.sigma) j * rising alpha j) *
      ((j.choose r : ℝ) / rising alpha r) * R ^ r =
    (rising alpha j / rising (1 / c.sigma) j) *
      ((j.choose r : ℝ) * A ^ (j - r) * B ^ r / rising alpha r)
  linear_combination
    ((j.choose r : ℝ) * rising alpha j /
      (rising (1 / c.sigma) j * rising alpha r)) * hpowers hrj

/-- Factorial normalization rewrites the same expansion as a finite Cauchy limit. -/
theorem partIIFamily_eq_factorial_sum {c : PartIIParameters} (hc : c.Admissible) (j : ℕ) :
    partIIFamily c j =
      C (rising (c.a₂ / c.a₁) j / rising (1 / c.sigma) j * (j.factorial : ℝ)) *
        ∑ r ∈ Finset.range (j + 1),
          C ((1 / ((j - r).factorial : ℝ)) * (c.a₁ / c.sigma) ^ (j - r) *
            (1 / (r.factorial : ℝ) / rising (c.a₂ / c.a₁) r) *
              (c.b₂ / c.sigma) ^ r) * partIIShift c ^ r := by
  rw [partIIFamily_eq_sum hc]
  simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
  apply Finset.sum_congr rfl
  intro r hr
  have hrj : r ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  rw [Nat.cast_choose ℝ hrj]
  congr 2
  ring

end RealRooted.TuranHurwitz
