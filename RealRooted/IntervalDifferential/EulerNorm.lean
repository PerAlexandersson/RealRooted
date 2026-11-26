/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.EulerRecurrence
public import RealRooted.IntervalDifferential.CoefficientNorm
import Mathlib.Tactic

/-!
# Degree and norm bounds for polynomial Euler coefficients
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.IntervalDifferential

/-- A size-bounded Euler kernel produces size-bounded polynomial coefficients. -/
theorem natDegree_eulerCoeff_le (K : ℕ → ℚ[X])
    (hK : ∀ i, (K i).natDegree ≤ i) (n : ℕ) :
    (PowerSeries.eulerCoeff K n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [PowerSeries.eulerCoeff, smul_eq_C_mul]
      apply (natDegree_C_mul_le _ _).trans
      apply natDegree_sum_le_of_forall_le
      intro i _
      apply natDegree_mul_le.trans
      have h1 := hK (n + 1 - i.val)
      have h2 := ih i.val i.isLt
      lia

/-- The coefficient norm satisfies the scalar Euler convolution inequality. -/
theorem coefficientNorm_eulerCoeff_equation {r : ℚ} (hr : 0 ≤ r)
    (K : ℕ → ℚ[X]) {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ) * coefficientNorm r (PowerSeries.eulerCoeff K n) ≤
      ∑ i ∈ range n, coefficientNorm r (K (n - i)) *
        coefficientNorm r (PowerSeries.eulerCoeff K i) := by
  have he := congrArg (coefficientNorm r) (PowerSeries.eulerCoeff_equation K hn)
  rw [smul_eq_C_mul, coefficientNorm_C_mul, abs_of_nonneg (Nat.cast_nonneg n)] at he
  rw [he]
  exact (coefficientNorm_sum_le hr _ _).trans
    (sum_le_sum (fun i _ => coefficientNorm_mul_le hr _ _))

end RealRooted.IntervalDifferential
