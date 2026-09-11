import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Order-numerator step

This coefficient operator is shared by OEIS order-numerator recurrences.  Its
strict and tight degree behaviour is intentionally separated in the
preservation layer.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The affine order-numerator step with ambient degree parameter `D`. -/
def orderNumeratorStep (c : ℝ) (D : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C c * p + X * (C ((D : ℝ) + 1 - c) * p + (1 - X) * p.derivative)

@[simp]
theorem orderNumeratorStep_coeff_zero (c : ℝ) (D : ℕ) (p : ℝ[X]) :
    (orderNumeratorStep c D p).coeff 0 = c * p.coeff 0 := by
  simp [orderNumeratorStep]

private theorem affineDerivativeStep_coeff_succ (c a : ℝ) (p : ℝ[X]) (k : ℕ) :
    (C c * p + X * (C a * p + (1 - X) * p.derivative)).coeff (k + 1) =
      (c + (k + 1 : ℕ)) * p.coeff (k + 1) + (a - k) * p.coeff k := by
  have heq : C c * p + X * (C a * p + (1 - X) * p.derivative) =
      C c * p + C a * (X * p) + X * p.derivative - X * (X * p.derivative) := by
    ring
  rw [heq]
  cases k with
  | zero => simp [coeff_derivative]; ring
  | succ k => simp [coeff_derivative]; ring

/-- The positive-degree coefficient recurrence for `orderNumeratorStep`. -/
theorem orderNumeratorStep_coeff_succ (c : ℝ) (D : ℕ) (p : ℝ[X]) (k : ℕ) :
    (orderNumeratorStep c D p).coeff (k + 1) =
      (c + (k + 1 : ℕ)) * p.coeff (k + 1) +
        ((D : ℝ) + 1 - c - k) * p.coeff k :=
  affineDerivativeStep_coeff_succ c ((D : ℝ) + 1 - c) p k

@[simp]
theorem orderNumeratorStep_add (c : ℝ) (D : ℕ) (p q : ℝ[X]) :
    orderNumeratorStep c D (p + q) = orderNumeratorStep c D p + orderNumeratorStep c D q := by
  simp [orderNumeratorStep, derivative_add]
  ring

@[simp]
theorem orderNumeratorStep_C_mul (c : ℝ) (D : ℕ) (a : ℝ) (p : ℝ[X]) :
    orderNumeratorStep c D (C a * p) = C a * orderNumeratorStep c D p := by
  simp [orderNumeratorStep]
  ring

@[simp]
theorem orderNumeratorStep_X_mul (c : ℝ) (D : ℕ) (p : ℝ[X]) :
    orderNumeratorStep c D (X * p) = X * orderNumeratorStep (c + 1) D p := by
  unfold orderNumeratorStep
  rw [derivative_mul, derivative_X]
  simp only [one_mul]
  norm_num [map_ofNat]
  ring

/-- In the strict parameter regime, the order-numerator step raises degree by
one. -/
theorem orderNumeratorStep_natDegree_strict
    {m D : ℕ} {p : ℝ[X]} (hm : 1 ≤ m) (hpdeg : p.natDegree = m)
    {c : ℝ} (hbound : (m : ℝ) < (D : ℝ) + 1 - c) :
    (orderNumeratorStep c D p).natDegree = m + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : k ≠ 0)
    rw [orderNumeratorStep_coeff_succ]
    have hj : m < j := by lia
    have hj0 : p.coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa [hpdeg] using hj)
    have hj1 : p.coeff (j + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa [hpdeg] using (show m < j + 1 by lia))
    rw [hj0, hj1]
    ring
  · rw [orderNumeratorStep_coeff_succ]
    have hnext : p.coeff (m + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simp [hpdeg])
    rw [hnext]
    have htop : p.coeff m ≠ 0 := by
      rw [← hpdeg, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (by
        intro hzero
        rw [hzero] at hpdeg
        simp at hpdeg
        lia)
    simp only [mul_zero, zero_add]
    exact mul_ne_zero (by linarith) htop

end RealRooted
