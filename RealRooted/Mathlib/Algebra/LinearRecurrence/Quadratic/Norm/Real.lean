import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic.Norm
import Mathlib.Analysis.Complex.Basic

/-!
# Real quadratic recurrence norm bounds from complex roots

This transports a real quadratic solution to `ℂ` and applies the generic
complex-root norm bound.  Root existence remains a separate client concern.
-/

namespace LinearRecurrence

/-- A real quadratic solution obeys the complex-root norm bound after its
coefficients and values are transported to `ℂ`. -/
theorem quadratic_norm_bound_ofReal {p q : ℝ} {β₁ β₂ : ℂ} {lam : ℝ} {S : ℕ → ℝ}
    (hS : (quadratic p q).IsSolution S) (hsum : β₁ + β₂ = p)
    (hprod : β₁ * β₂ = -q) (h1 : ‖β₁‖ ≤ lam) (h2 : ‖β₂‖ ≤ lam)
    (hlam : 0 ≤ lam) (k : ℕ) :
    lam * ‖S k‖ ≤ lam ^ (k + 1) * ‖S 0‖ +
      (k : ℝ) * lam ^ k * (‖S 1‖ + lam * ‖S 0‖) := by
  have hSC : (quadratic (p : ℂ) (q : ℂ)).IsSolution fun n ↦ (S n : ℂ) := by
    refine quadratic_isSolution_iff _ _ _ |>.mpr ?_
    intro n
    exact_mod_cast quadratic_isSolution_iff p q S |>.mp hS n
  simpa using quadratic_norm_bound hSC hsum hprod h1 h2 hlam k

end LinearRecurrence
