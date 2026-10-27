/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Norm bounds for powers multiplied by a fixed element

This Mathlib-shaped lemma avoids a `NormOneClass` assumption by retaining a
fixed right factor instead of bounding a bare power.
-/

public section

variable {R : Type*} [SeminormedRing R]

namespace SeminormedRing

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

end SeminormedRing
