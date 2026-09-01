import RealRooted.ChudnovskySeymour
import RealRooted.HermiteBiehler
import RealRooted.MaWang

/-!
# Adjacent Euler insertion operators

This file develops the two adjacent Euler operators used in compatibility
proofs for derangement descent polynomials.  The common parametrization

`E(c, d) p = (c + (d + 1) X) p + (X - X^2) p'`

contains the positive-boundary operator at `c = 1` and the zero-boundary
operator at `c = 0`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Euler insertion operator with constant boundary weight `c` and degree
bound `d`. -/
def eulerInsertionStep (c : ℝ) (d : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C c * p + C ((d : ℝ) + 1) * (X * p) +
    X * p.derivative - X * (X * p.derivative)

theorem eulerInsertionStep_eq (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep c d p =
      (C c + C ((d : ℝ) + 1) * X) * p +
        (X - X ^ 2) * p.derivative := by
  simp [eulerInsertionStep]
  ring

@[simp] theorem eulerInsertionStep_zero (c : ℝ) (d : ℕ) :
    eulerInsertionStep c d 0 = 0 := by
  simp [eulerInsertionStep]

@[simp] theorem coeff_eulerInsertionStep_zero (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    (eulerInsertionStep c d p).coeff 0 = c * p.coeff 0 := by
  simp [eulerInsertionStep]

@[simp] theorem coeff_eulerInsertionStep_succ
    (c : ℝ) (d k : ℕ) (p : ℝ[X]) :
    (eulerInsertionStep c d p).coeff (k + 1) =
      (c + (k : ℝ) + 1) * p.coeff (k + 1) +
        ((d : ℝ) + 1 - k) * p.coeff k := by
  cases k with
  | zero =>
      simp only [eulerInsertionStep, coeff_sub, coeff_add, coeff_C_mul]
      simp [coeff_X_mul, coeff_derivative]
      ring
  | succ k =>
      simp only [eulerInsertionStep, coeff_sub, coeff_add, coeff_C_mul]
      simp [coeff_X_mul, coeff_derivative]
      ring

theorem eulerInsertionStep_add (c : ℝ) (d : ℕ) (p q : ℝ[X]) :
    eulerInsertionStep c d (p + q) =
      eulerInsertionStep c d p + eulerInsertionStep c d q := by
  simp [eulerInsertionStep, derivative_add]
  ring

theorem eulerInsertionStep_C_mul (c a : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep c d (C a * p) = C a * eulerInsertionStep c d p := by
  simp [eulerInsertionStep, derivative_mul]
  ring

theorem natDegree_eulerInsertionStep_le (c : ℝ) (d : ℕ) (p : ℝ[X]) :
    (eulerInsertionStep c d p).natDegree ≤ p.natDegree + 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  cases k with
  | zero => lia
  | succ k =>
      rw [coeff_eulerInsertionStep_succ]
      have hpk : p.coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      have hpks : p.coeff (k + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by lia)
      simp [hpk, hpks]

/-- Under the intended degree bound, an Euler insertion step raises degree by
one and retains a positive leading coefficient. -/
theorem eulerInsertionStep_degree_pos
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hp_pos : HasPosLeadingCoeff p) :
    (eulerInsertionStep c d p).natDegree = p.natDegree + 1 ∧
      HasPosLeadingCoeff (eulerInsertionStep c d p) := by
  have hfactor : 0 < (d : ℝ) + 1 - p.natDegree := by
    have hcast : (p.natDegree : ℝ) ≤ d := Nat.cast_le.mpr hpdeg
    linarith
  have hcoeff :
      0 < (eulerInsertionStep c d p).coeff (p.natDegree + 1) := by
    rw [coeff_eulerInsertionStep_succ]
    rw [coeff_eq_zero_of_natDegree_lt (by lia)]
    simp only [mul_zero, zero_add]
    change 0 < ((d : ℝ) + 1 - p.natDegree) * p.leadingCoeff
    exact mul_pos hfactor hp_pos
  have hdeg : (eulerInsertionStep c d p).natDegree = p.natDegree + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_eulerInsertionStep_le c d p) hcoeff.ne'
  refine ⟨hdeg, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, hdeg]
  exact hcoeff

/-- Nonnegative boundary and coefficient weights preserve coefficient
nonnegativity up to the declared degree bound. -/
theorem HasNonnegCoeffs.eulerInsertionStep
    {c : ℝ} {d : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hc : 0 ≤ c) (hpdeg : p.natDegree ≤ d) :
    HasNonnegCoeffs (eulerInsertionStep c d p) := by
  intro k
  cases k with
  | zero =>
      rw [coeff_eulerInsertionStep_zero]
      exact mul_nonneg hc (hp 0)
  | succ k =>
      rw [coeff_eulerInsertionStep_succ]
      by_cases hk : k ≤ d
      · have hweight : 0 ≤ (d : ℝ) + 1 - k := by
          have hcast : (k : ℝ) ≤ d := Nat.cast_le.mpr hk
          linarith
        exact add_nonneg
          (mul_nonneg (by positivity) (hp (k + 1)))
          (mul_nonneg hweight (hp k))
      · have hdk : d < k := Nat.lt_of_not_ge hk
        have hpk : p.coeff k = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg hdk)
        have hpks : p.coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpdeg (by lia))
        simp [hpk, hpks]

end RealRooted
