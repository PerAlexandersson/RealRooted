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
# Degrees of the A008299 recurrence

Exact degrees and positive leading coefficients for sequences satisfying
the A008299 derivative-lag recurrence.
-/

public section

open Polynomial

namespace RealRooted.Applications.OEIS

/-- The A008299 recurrence with constant seeds has degree `floor(n/2)`
and positive leading coefficients. -/
theorem a008299_natDegree {P : ℕ → ℝ[X]} (h0 : P 0 = 1) (h1 : P 1 = 1)
    (hrec : ∀ n, P (n + 2) =
      X * (P (n + 1)).derivative + P (n + 1) + C ((n : ℝ) + 3) * X * P n) :
    ∀ n, (P n).natDegree = n / 2 ∧ 0 < (P n).leadingCoeff :=
  BandOne.eulerLag_natDegree (fun n ↦ by rw [hrec n]; ring)
    (by simp [h0]) (by simp [h1]) (fun n ↦ by positivity)

end RealRooted.Applications.OEIS
