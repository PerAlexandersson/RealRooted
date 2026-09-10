import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Norm bounds for powers multiplied by a fixed element

This Mathlib-shaped lemma avoids a `NormOneClass` assumption by retaining a
fixed right factor instead of bounding a bare power.
-/

variable {R : Type*} [SeminormedRing R]

/-- If `lam` bounds `‖β‖`, it controls `‖β^n * d‖` without requiring
`‖1‖ = 1`. -/
theorem norm_pow_mul_le (β d : R) {lam : ℝ} (hβ : ‖β‖ ≤ lam) (hlam : 0 ≤ lam)
    (n : ℕ) : ‖β ^ n * d‖ ≤ lam ^ n * ‖d‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      calc
        ‖(β * β ^ n) * d‖ = ‖β * (β ^ n * d)‖ := by rw [mul_assoc]
        _ ≤ ‖β‖ * ‖β ^ n * d‖ := norm_mul_le _ _
        _ ≤ lam * (lam ^ n * ‖d‖) := by gcongr
        _ = lam ^ (n + 1) * ‖d‖ := by ring
