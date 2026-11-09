/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.LaguerreInequalities
public import RealRooted.LaguerreInequalities.Forms
public import RealRooted.BrandenLeite.AffineNegativePower
import RealRooted.BrandenLeite.AffineNegativePowerRecurrence
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialPositive
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerCoefficients
import Mathlib.Tactic

/-!
# Coefficient-row induction for the two Laguerre inequalities

For a power series `Q` with `Q (0) = 1` let `F_n^κ (t) = [zⁿ] (Q (z) - t z) ^ (-κ)`
(`RealRooted.BrandenLeite.affineNegativePowerCoeff κ Q X n`), extended by zero to negative `n`
(`RealRooted.BrandenLeite.affineNegativePowerRow`).  Differentiating in `t` gives
`∂ₜ F_n^κ = κ F_{n-1}^{κ+1}`, so the derivatives of a row are again rows.  If both Laguerre forms
of every row `F_n^α` with a positive integer `α` are nonnegative, then every such row splits:
by induction on `n` the derivative `α F_{n-1}^{α+1}` of `F_n^α` splits, and the two Laguerre
inequalities then give that `F_n^α` splits
(`RealRooted.splits_iff_splits_derivative_and_forms_nonneg`).
-/

@[expose] public section

open PowerSeries

namespace RealRooted.BrandenLeite

/-- Shifting the rising factorial: `(k + 1) * multichoose a (k + 1) = a * multichoose (a + 1) k`. -/
theorem succ_mul_multichoose_succ (a : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Ring.multichoose a (k + 1) = a * Ring.multichoose (a + 1) k := by
  have h₁ := Ring.factorial_mul_multichoose a (k + 1)
  rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at h₁
  have h₂ := Ring.factorial_mul_multichoose (a + 1) k
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hk
  rw [Nat.factorial_succ] at h₁
  push_cast at h₁
  linear_combination h₁ - a * h₂

/-- The row `n` of `(Q - t X) ^ (-κ)`, extended by zero for negative `n`. -/
noncomputable def affineNegativePowerRow (κ : ℝ) (Q : PowerSeries ℝ) (n : ℤ) : Polynomial ℝ :=
  if 0 ≤ n then affineNegativePowerCoeff κ Q PowerSeries.X n.toNat else 0

/-- **Derivative of a coefficient row.**  Differentiating `[zⁿ⁺¹] (Q - t z) ^ (-κ)` in `t`
gives `κ [zⁿ] (Q - t z) ^ (-κ - 1)`. -/
theorem derivative_affineNegativePowerCoeff_succ (κ : ℝ) (Q : PowerSeries ℝ)
    (hQ : constantCoeff Q = 1) (n : ℕ) :
    Polynomial.derivative (affineNegativePowerCoeff κ Q PowerSeries.X (n + 1)) =
      Polynomial.C κ * affineNegativePowerCoeff (κ + 1) Q PowerSeries.X n := by
  unfold affineNegativePowerCoeff
  ext k
  rw [Polynomial.coeff_derivative, Polynomial.coeff_C_mul,
    coeff_coeff_subst_binomialSeries_neg Q PowerSeries.X hQ (by simp) κ (n + 1) (k + 1),
    coeff_coeff_subst_binomialSeries_neg Q PowerSeries.X hQ (by simp) (κ + 1) n k]
  have hexp : -κ - ((k + 1 : ℕ) : ℝ) = -(κ + 1) - (k : ℝ) := by push_cast; ring
  have hX (T : PowerSeries ℝ) :
      coeff (n + 1) (PowerSeries.X ^ (k + 1) * T) = coeff n (PowerSeries.X ^ k * T) := by
    rw [pow_succ', mul_assoc, coeff_succ_X_mul]
  rw [hexp, hX]
  have h := succ_mul_multichoose_succ κ k
  linear_combination
    coeff n (PowerSeries.X ^ k * subst (Q - 1) (binomialSeries ℝ (-(κ + 1) - (k : ℝ)))) * h

/-- On nonnegative indices the signed row is the canonical coefficient row. -/
theorem affineNegativePowerRow_natCast (κ : ℝ) (Q : PowerSeries ℝ) (n : ℕ) :
    affineNegativePowerRow κ Q n = affineNegativePowerCoeff κ Q PowerSeries.X n := by
  simp [affineNegativePowerRow]

/-- Rows with negative index vanish. -/
theorem affineNegativePowerRow_of_neg (κ : ℝ) (Q : PowerSeries ℝ) {n : ℤ} (hn : n < 0) :
    affineNegativePowerRow κ Q n = 0 := by
  simp [affineNegativePowerRow, not_le.mpr hn]

/-- The initial row is one. -/
theorem affineNegativePowerRow_zero (κ : ℝ) (Q : PowerSeries ℝ) (hQ : constantCoeff Q = 1) :
    affineNegativePowerRow κ Q 0 = 1 := by
  simpa [affineNegativePowerRow] using affineNegativePowerCoeff_zero κ Q PowerSeries.X hQ (by simp)

/-- **Derivative of a signed coefficient row**: `∂ₜ F_n^κ = κ F_{n-1}^{κ+1}` for all integers
`n`, with negative rows zero. -/
theorem derivative_affineNegativePowerRow (κ : ℝ) (Q : PowerSeries ℝ)
    (hQ : constantCoeff Q = 1) (n : ℤ) :
    Polynomial.derivative (affineNegativePowerRow κ Q n) =
      Polynomial.C κ * affineNegativePowerRow (κ + 1) Q (n - 1) := by
  rcases n with (_ | m) | m
  · change Polynomial.derivative (affineNegativePowerRow κ Q 0) =
      Polynomial.C κ * affineNegativePowerRow (κ + 1) Q (0 - 1)
    rw [affineNegativePowerRow_zero κ Q hQ,
      affineNegativePowerRow_of_neg _ Q (by lia : (0 : ℤ) - 1 < 0)]
    simp
  · change Polynomial.derivative (affineNegativePowerRow κ Q ((m + 1 : ℕ) : ℤ)) =
      Polynomial.C κ * affineNegativePowerRow (κ + 1) Q (((m + 1 : ℕ) : ℤ) - 1)
    have : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by lia
    rw [this, affineNegativePowerRow_natCast, affineNegativePowerRow_natCast,
      derivative_affineNegativePowerCoeff_succ κ Q hQ m]
  · rw [affineNegativePowerRow_of_neg _ Q (by lia : Int.negSucc m < 0),
      affineNegativePowerRow_of_neg _ Q (by lia : Int.negSucc m - 1 < 0)]
    simp

section Evaluation

variable (κ : ℝ) (Q : PowerSeries ℝ) (hQ : constantCoeff Q = 1) (n : ℤ)

include hQ

private theorem derivative_derivative_row :
    Polynomial.derivative (Polynomial.derivative (affineNegativePowerRow κ Q n)) =
      Polynomial.C (κ * (κ + 1)) * affineNegativePowerRow (κ + 2) Q (n - 2) := by
  rw [derivative_affineNegativePowerRow κ Q hQ, Polynomial.derivative_C_mul,
    derivative_affineNegativePowerRow _ Q hQ, ← mul_assoc, ← Polynomial.C_mul,
    show κ + 1 + 1 = κ + 2 by ring, show n - 1 - 1 = n - 2 by lia]

private theorem derivative_derivative_derivative_row :
    Polynomial.derivative (Polynomial.derivative (Polynomial.derivative
      (affineNegativePowerRow κ Q n))) =
      Polynomial.C (κ * (κ + 1) * (κ + 2)) * affineNegativePowerRow (κ + 3) Q (n - 3) := by
  rw [derivative_derivative_row κ Q hQ, Polynomial.derivative_C_mul,
    derivative_affineNegativePowerRow _ Q hQ, ← mul_assoc, ← Polynomial.C_mul,
    show κ + 2 + 1 = κ + 3 by ring, show n - 2 - 1 = n - 3 by lia]

private theorem derivative_derivative_derivative_derivative_row :
    Polynomial.derivative (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative
      (affineNegativePowerRow κ Q n)))) =
      Polynomial.C (κ * (κ + 1) * (κ + 2) * (κ + 3)) *
        affineNegativePowerRow (κ + 4) Q (n - 4) := by
  rw [derivative_derivative_derivative_row κ Q hQ, Polynomial.derivative_C_mul,
    derivative_affineNegativePowerRow _ Q hQ, ← mul_assoc, ← Polynomial.C_mul,
    show κ + 3 + 1 = κ + 4 by ring, show n - 3 - 1 = n - 4 by lia]

/-- The first Laguerre form of a row, evaluated: it is the combination of rows `F_{n-1}^{κ+1}`,
`F_n^κ`, `F_{n-2}^{κ+2}`. -/
theorem eval_laguerreForm_affineNegativePowerRow (t : ℝ) :
    (laguerreForm (affineNegativePowerRow κ Q n)).eval t =
      κ ^ 2 * (affineNegativePowerRow (κ + 1) Q (n - 1)).eval t ^ 2 -
        κ * (κ + 1) * (affineNegativePowerRow κ Q n).eval t *
          (affineNegativePowerRow (κ + 2) Q (n - 2)).eval t := by
  rw [eval_laguerreForm, derivative_derivative_row κ Q hQ,
    derivative_affineNegativePowerRow κ Q hQ]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- The second Laguerre form of a row, evaluated. -/
theorem eval_secondLaguerreForm_affineNegativePowerRow (t : ℝ) :
    (secondLaguerreForm (affineNegativePowerRow κ Q n)).eval t =
      (3 * (κ * (κ + 1)) ^ 2 * (affineNegativePowerRow (κ + 2) Q (n - 2)).eval t ^ 2 -
        4 * κ * (κ * (κ + 1) * (κ + 2)) * (affineNegativePowerRow (κ + 1) Q (n - 1)).eval t *
          (affineNegativePowerRow (κ + 3) Q (n - 3)).eval t +
        κ * (κ + 1) * (κ + 2) * (κ + 3) * (affineNegativePowerRow κ Q n).eval t *
          (affineNegativePowerRow (κ + 4) Q (n - 4)).eval t) / 12 := by
  rw [eval_secondLaguerreForm, derivative_derivative_derivative_derivative_row κ Q hQ,
    derivative_derivative_derivative_row κ Q hQ, derivative_derivative_row κ Q hQ,
    derivative_affineNegativePowerRow κ Q hQ]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

end Evaluation

/-- **Coefficient-row induction for the two Laguerre inequalities.**  Let `Q (0) = 1` and let
`F_n^α (t) = [zⁿ] (Q (z) - t z) ^ (-α)`, with `F_n^α = 0` for `n < 0`.  If the two inequalities
`α² (F_{n-1}^{α+1})² - α (α + 1) F_n^α F_{n-2}^{α+2} ≥ 0` and
`3 ((α)₂ F_{n-2}^{α+2})² - 4 α (α)₃ F_{n-1}^{α+1} F_{n-3}^{α+3} + (α)₄ F_n^α F_{n-4}^{α+4} ≥ 0`
hold at every real `t`, for every integer `n` and every positive integer `α`, then every row
`F_n^α` with `n ≥ 0` and positive integer `α` splits.  Here `(α)ₖ` is the rising factorial. -/
theorem splits_affineNegativePowerRow_of_inequalities (Q : PowerSeries ℝ)
    (hQ : constantCoeff Q = 1)
    (h₁ : ∀ (α : ℕ) (n : ℤ) (t : ℝ), 0 < α →
      0 ≤ (α : ℝ) ^ 2 * (affineNegativePowerRow ((α : ℝ) + 1) Q (n - 1)).eval t ^ 2 -
        (α : ℝ) * ((α : ℝ) + 1) * (affineNegativePowerRow (α : ℝ) Q n).eval t *
          (affineNegativePowerRow ((α : ℝ) + 2) Q (n - 2)).eval t)
    (h₂ : ∀ (α : ℕ) (n : ℤ) (t : ℝ), 0 < α →
      0 ≤ 3 * ((α : ℝ) * ((α : ℝ) + 1)) ^ 2 *
          (affineNegativePowerRow ((α : ℝ) + 2) Q (n - 2)).eval t ^ 2 -
        4 * (α : ℝ) * ((α : ℝ) * ((α : ℝ) + 1) * ((α : ℝ) + 2)) *
          (affineNegativePowerRow ((α : ℝ) + 1) Q (n - 1)).eval t *
          (affineNegativePowerRow ((α : ℝ) + 3) Q (n - 3)).eval t +
        (α : ℝ) * ((α : ℝ) + 1) * ((α : ℝ) + 2) * ((α : ℝ) + 3) *
          (affineNegativePowerRow (α : ℝ) Q n).eval t *
          (affineNegativePowerRow ((α : ℝ) + 4) Q (n - 4)).eval t)
    (α n : ℕ) (hα : 0 < α) : (affineNegativePowerRow (α : ℝ) Q n).Splits := by
  induction n generalizing α with
  | zero =>
    rw [Nat.cast_zero, affineNegativePowerRow_zero _ Q hQ]
    exact Polynomial.Splits.C 1
  | succ n ih =>
    have hd : (Polynomial.derivative
        (affineNegativePowerRow (α : ℝ) Q ((n + 1 : ℕ) : ℤ))).Splits := by
      rw [derivative_affineNegativePowerRow _ Q hQ, Nat.cast_succ, add_sub_cancel_right]
      have := ih (α + 1) (Nat.succ_pos α)
      rw [Nat.cast_succ] at this
      exact (Polynomial.Splits.C _).mul this
    refine (splits_iff_splits_derivative_and_forms_nonneg _).mpr ⟨hd, fun t => ⟨?_, ?_⟩⟩
    · rw [eval_laguerreForm_affineNegativePowerRow _ Q hQ]
      exact h₁ α _ t hα
    · rw [eval_secondLaguerreForm_affineNegativePowerRow _ Q hQ]
      exact div_nonneg (h₂ α _ t hα) (by norm_num)

end RealRooted.BrandenLeite
