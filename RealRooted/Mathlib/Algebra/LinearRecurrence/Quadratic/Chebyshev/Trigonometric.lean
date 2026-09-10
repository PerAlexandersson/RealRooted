import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Trigonometric form of normalized quadratic recurrences

The formula is multiplied by `sin θ`, so it remains valid at the endpoint
angles without a nonvanishing assumption.
-/

namespace LinearRecurrence

open Polynomial

/-- A normalized real quadratic recurrence has the usual sine-multiplied
Chebyshev trigonometric form. -/
theorem isSolution_mul_sin_eq_cos {θ : ℝ} {E : ℕ → ℝ}
    (hE : (quadratic (2 * Real.cos θ) (-1)).IsSolution E) (k : ℕ) :
    E k * Real.sin θ = E 0 * Real.cos (k * θ) * Real.sin θ +
      (E 1 - E 0 * Real.cos θ) * Real.sin (k * θ) := by
  have hEq := congrFun (isSolution_eq_quadraticChebyshevSolution hE) k
  rw [hEq]
  unfold quadraticChebyshevSolution
  rw [Chebyshev.T_real_cos]
  calc
    (E 0 * Real.cos ((k : ℤ) * θ) +
        (E 1 - E 0 * Real.cos θ) * (Chebyshev.U ℝ ((k : ℤ) - 1)).eval (Real.cos θ)) *
        Real.sin θ
        = E 0 * Real.cos ((k : ℤ) * θ) * Real.sin θ +
          (E 1 - E 0 * Real.cos θ) *
            ((Chebyshev.U ℝ ((k : ℤ) - 1)).eval (Real.cos θ) * Real.sin θ) := by ring
    _ = E 0 * Real.cos (k * θ) * Real.sin θ +
          (E 1 - E 0 * Real.cos θ) * Real.sin (k * θ) := by
        rw [Chebyshev.U_real_cos]
        push_cast
        ring_nf

end LinearRecurrence
