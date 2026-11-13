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
# Degrees of the A046739 recurrence

Exact degrees and positive leading coefficients for sequences satisfying
the A046739 derivative-lag recurrence.
-/

public section

open Polynomial

namespace RealRooted.Applications.OEIS

/-- Rows of the A046739 recurrence have degree `n + 2` and positive
leading coefficients. -/
theorem a046739_natDegree {P : ℕ → ℝ[X]}
    (h0 : (P 0).natDegree = 2 ∧ 0 < (P 0).leadingCoeff)
    (h1 : (P 1).natDegree = 3 ∧ 0 < (P 1).leadingCoeff)
    (hrec : ∀ n, P (n + 2) = (X - X ^ 2) * (P (n + 1)).derivative +
      (1 + C ((n : ℝ) + 4) * X) * P (n + 1) + C ((n : ℝ) + 5) * X * P n) :
    ∀ n, (P n).natDegree = 2 + n ∧ 0 < (P n).leadingCoeff := by
  apply BandOne.eulerianLag_natDegree (D := 2) (lam := fun n ↦ (n : ℝ) + 5) ?_ h0 h1
  intro n
  rw [hrec n]
  push_cast
  ring

end RealRooted.Applications.OEIS
