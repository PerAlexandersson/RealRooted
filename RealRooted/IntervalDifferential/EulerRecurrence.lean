/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerRecurrence
import Mathlib.Tactic

/-!
# Coefficients determined by an Euler differential equation

Adding the logarithmic kernels convolves the coefficient rows. We prove this
through the power-series product rule rather than rearranging triple sums.
-/

@[expose] public section

noncomputable section

open Finset

namespace PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The normalized coefficient row determined by an Euler kernel. -/
def eulerCoeff (K : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => (((n + 1 : ℕ) : ℚ)⁻¹) •
      ∑ i : Fin (n + 1), K (n + 1 - i.val) * eulerCoeff K i.val
termination_by n => n

@[simp] theorem eulerCoeff_zero (K : ℕ → R) : eulerCoeff K 0 = 1 := by rw [eulerCoeff]

/-- The denominator-cleared Euler recurrence. -/
theorem eulerCoeff_equation (K : ℕ → R) {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ) • eulerCoeff K n = ∑ i ∈ range n, K (n - i) * eulerCoeff K i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [eulerCoeff, smul_smul, mul_inv_cancel₀ (by positivity : ((m + 1 : ℕ) : ℚ) ≠ 0),
    one_smul, Fin.sum_univ_eq_sum_range (fun i => K (m + 1 - i) * eulerCoeff K i)]

/-- The Euler recurrence with its constant coefficient determines the whole row. -/
theorem eulerCoeff_unique (K a : ℕ → R) (h0 : a 0 = 1)
    (ha : ∀ (n : ℕ), n ≠ 0 → (n : ℚ) • a n = ∑ i ∈ range n, K (n - i) * a i) :
    a = eulerCoeff K := by
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · simp [hn, h0]
    · have he := ha n hn
      have ht := eulerCoeff_equation K hn
      have hh : ∑ i ∈ range n, K (n - i) * a i =
          ∑ i ∈ range n, K (n - i) * eulerCoeff K i := by
        exact sum_congr rfl (fun i hi => by rw [ih i (mem_range.mp hi)])
      rw [hh, ← ht] at he
      have hi := congrArg (fun x : R => (n : ℚ)⁻¹ • x) he
      simpa only [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn : (n : ℚ) ≠ 0),
        one_smul] using hi

/-- The coefficient row satisfies its formal Euler differential equation. -/
theorem mk_eulerCoeff_equation (K : ℕ → R) (hK : K 0 = 0) :
    X * derivative (mk (eulerCoeff K)) = mk K * mk (eulerCoeff K) := by
  ext n
  rw [coeff_X_mul_derivative, coeff_mk, mul_comm (mk K), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
    Nat.sub_self]
  simp only [coeff_mk, hK, mul_zero, add_zero]
  by_cases hn : n = 0
  · simp [hn]
  · have he := eulerCoeff_equation K hn
    simpa [Algebra.smul_def, mul_comm] using he

/-- The normalized solution of an Euler equation has the canonical coefficients. -/
theorem eq_mk_eulerCoeff (K : ℕ → R) (hK : K 0 = 0) (F : PowerSeries R)
    (h0 : constantCoeff F = 1) (hF : X * derivative F = mk K * F) :
    F = mk (eulerCoeff K) := by
  have he := eulerCoeff_unique K (fun n => coeff n F)
    (by simpa only [coeff_zero_eq_constantCoeff] using h0) (by
    intro n hn
    have hh := congrArg (coeff n) hF
    rw [coeff_X_mul_derivative, mul_comm (mk K), coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
      Nat.sub_self] at hh
    simp only [coeff_mk, hK, mul_zero, add_zero] at hh
    simpa [Algebra.smul_def, mul_comm] using hh)
  ext n
  simpa using congrFun he n

/-- Adding two Euler kernels convolves their normalized coefficient rows. -/
theorem eulerCoeff_add (K J : ℕ → R) (hK : K 0 = 0) (hJ : J 0 = 0) (n : ℕ) :
    eulerCoeff (K + J) n =
      ∑ i ∈ range (n + 1), eulerCoeff K i * eulerCoeff J (n - i) := by
  have hprod : mk (eulerCoeff (K + J)) = mk (eulerCoeff K) * mk (eulerCoeff J) := by
    symm
    apply eq_mk_eulerCoeff (K + J) (by simp [hK, hJ])
    · simp
    · have h1 := mk_eulerCoeff_equation K hK
      have h2 := mk_eulerCoeff_equation J hJ
      rw [derivative.leibniz]
      have ha : mk (K + J) = mk K + mk J := by ext; simp
      rw [ha]
      linear_combination mk (eulerCoeff J) * h1 + mk (eulerCoeff K) * h2
  have he := congrArg (coeff n) hprod
  simpa only [coeff_mk, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using he

end PowerSeries
