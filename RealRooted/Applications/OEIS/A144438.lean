/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic
import RealRooted.DerivativeRecurrence.BandOne
import Mathlib.Tactic

/-!
# Degrees of the A144438 recurrence

Exact degrees and positive leading coefficients for sequences satisfying
the A144438 derivative-lag recurrence.
-/

public section

open Polynomial

namespace RealRooted.Applications.OEIS

/-- Rows of the A144438 recurrence have degree `n` and positive
leading coefficients, including the constant seed. -/
theorem a144438_natDegree {P : ℕ → ℝ[X]} (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) = (X - X ^ 2) * (P (n + 1)).derivative +
      (1 + C ((n : ℝ) + 2) * X) * P (n + 1) + X * P n) :
    ∀ n, (P n).natDegree = n ∧ 0 < (P n).leadingCoeff := by
  have hseed : (P 1).natDegree = 1 ∧ 0 < (P 1).leadingCoeff := by
    rw [h1]
    have hdeg : (1 + X : ℝ[X]).natDegree = 1 := by
      simpa only [C_1, add_comm] using (natDegree_X_add_C (1 : ℝ))
    exact ⟨hdeg, by rw [leadingCoeff, hdeg]; norm_num [coeff_add, coeff_one, coeff_X]⟩
  simpa using BandOne.eulerianLag_natDegree (D := 0) (lam := fun _ ↦ 1)
    (fun n ↦ by rw [hrec n]; simp; ring) (by simp [h0]) hseed

end RealRooted.Applications.OEIS
