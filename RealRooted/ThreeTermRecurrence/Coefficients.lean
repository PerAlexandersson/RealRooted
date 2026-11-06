module

public import RealRooted.Basic.Coefficients
import Mathlib.Tactic.Ring

/-!
# Coefficient positivity through weighted differences

For a three-term recurrence, track each row together with its difference from a
fixed polynomial multiple of the previous row. Nonnegative entries in this
transformed transition propagate coefficientwise nonnegativity even when the
original recurrence contains subtraction.
-/

public section

open Polynomial

namespace RealRooted

/-- Nonnegative rows and polynomial-weighted differences propagate through a
second-order recurrence whose transformed transition has nonnegative coefficients. -/
theorem hasNonnegCoeffs_and_sub_mul_of_threeTerm
    {P A B : ℕ → ℝ[X]} {R : ℝ[X]}
    (hrec : ∀ n, P (n + 2) = A n * P (n + 1) + B n * P n)
    (hR : HasNonnegCoeffs R)
    (hA : ∀ n, HasNonnegCoeffs (A n - R))
    (hB : ∀ n, HasNonnegCoeffs (R * (A n - R) + B n))
    (hzero : HasNonnegCoeffs (P 0))
    (hone : HasNonnegCoeffs (P 1 - R * P 0))
    (n : ℕ) : HasNonnegCoeffs (P n) ∧
      HasNonnegCoeffs (P (n + 1) - R * P n) := by
  induction n with
  | zero => exact ⟨hzero, hone⟩
  | succ n ih =>
    have hp : HasNonnegCoeffs (P (n + 1)) := by
      convert ih.2.add (hR.mul ih.1) using 1
      ring
    refine ⟨hp, ?_⟩
    have h := ((hA n).mul ih.2).add ((hB n).mul ih.1)
    convert h using 1
    rw [show n + 1 + 1 = n + 2 by lia, hrec n]
    ring

end RealRooted
