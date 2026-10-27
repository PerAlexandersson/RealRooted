module

public import RealRooted.DerivativeRecurrence.General
import RealRooted.Derivative.Algebra

/-!
# Nonnegative coefficients for general linear recurrences

This file supplies the coefficientwise induction used by row tactics for a
finite linear recurrence with arbitrary lags and iterated derivatives.
-/

public section

open Polynomial

namespace RealRooted.LinRec

/-- Every row of a finite linear recurrence has nonnegative coefficients when
the source lags are smaller than its offset, every multiplier has nonnegative
coefficients, and the initial rows have nonnegative coefficients. -/
theorem hasNonnegCoeffs
    {P : ℕ → ℝ[X]} {offset : ℕ} (terms : List (ℕ × ℕ × (ℕ → ℝ[X])))
    (hrec : ∀ n, P (n + offset) = rhs terms P n)
    (hlag : ∀ term ∈ terms, term.1 < offset)
    (hmult : ∀ term ∈ terms, ∀ n, HasNonnegCoeffs (term.2.2 n))
    (hbase : ∀ n, n < offset → HasNonnegCoeffs (P n)) :
    ∀ n, HasNonnegCoeffs (P n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < offset
      · exact hbase n hn
      · have hoff : offset ≤ n := Nat.le_of_not_gt hn
        let m := n - offset
        have hmn : m + offset = n := Nat.sub_add_cancel hoff
        rw [← hmn, hrec]
        unfold rhs
        apply hasNonnegCoeffs_sum
        intro q hq
        simp only [List.mem_map] at hq
        obtain ⟨term, hterm, rfl⟩ := hq
        apply (hmult term hterm m).mul
        apply HasNonnegCoeffs.iterate_derivative
        apply ih
        rw [← hmn]
        exact Nat.add_lt_add_left (hlag term hterm) m

end RealRooted.LinRec
