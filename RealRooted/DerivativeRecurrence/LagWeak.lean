import RealRooted.LiuWang.FiniteFamily

/-!
# Derivative--lag recurrences with common roots

This file packages the repeated-root-safe finite-family Liu--Wang step as a
sequence induction.  Unlike the strict negative-root route, it allows a root
at zero to persist through every row.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Adjacent rows of a derivative--lag recurrence strictly interlace when the
derivative and lag multipliers are nonpositive at every nonpositive real
number.  Common roots of adjacent rows are allowed. -/
theorem derivativeLag_strictInterl_of_nonnegCoeffs_of_step
    {P U V W : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 2) =
      U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n)
    (hstep : ∀ n, (P (n + 1)).natDegree = (P n).natDegree ∨
      (P (n + 1)).natDegree = (P n).natDegree + 1)
    (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hnn : ∀ n, HasNonnegCoeffs (P n))
    (hV : ∀ n x, x ≤ 0 → (V n).eval x ≤ 0)
    (hW : ∀ n x, x ≤ 0 → (W n).eval x ≤ 0)
    (hbase : StrictInterl (P 0) (P 1)) (n : ℕ) :
    StrictInterl (P n) (P (n + 1)) := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
      have hroot : ∀ r, (P (n + 1)).IsRoot r → r ≤ 0 := by
        intro r hr
        exact isRoot_nonpos_of_hasNonnegCoeffs
          (hnn (n + 1)) (hpos (n + 1)).ne_zero hr
      have hF_pos : HasPosLeadingCoeff
          (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n) := by
        rw [← hrec n]
        exact hpos (n + 2)
      have hdeg_lo : (P (n + 1)).natDegree ≤
          (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n).natDegree := by
        rw [← hrec n]
        rcases hstep (n + 1) with hsame | hsucc <;> lia
      have hdeg_hi :
          (U n * P (n + 1) + V n * (P (n + 1)).derivative + W n * P n).natDegree ≤
            (P (n + 1)).natDegree + 1 := by
        rw [← hrec n]
        rcases hstep (n + 1) with hsame | hsucc <;> lia
      have hnext := LiuWang.strictInterl_derivative_lag_of_eval_nonpos
        (hpos (n + 1)).ne_zero ih.2.1.2 (hpos (n + 1)) ih (hpos n) hF_pos
        hdeg_lo hdeg_hi (fun r hr ↦ hV n r (hroot r hr))
        (fun r hr ↦ hW n r (hroot r hr))
      rw [← hrec n] at hnext
      exact hnext

end RealRooted
