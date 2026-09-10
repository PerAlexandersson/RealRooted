import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic
import RealRooted.Mathlib.Analysis.Normed.Ring.Power
import Mathlib.Tactic.Linarith

/-!
# Norm bounds for quadratic recurrence solutions

The bounds use two supplied characteristic roots. Root existence and
specialized real or complex estimates remain separate clients.
-/

namespace LinearRecurrence

variable {R : Type*} [NormedCommRing R]

/-- One telescoped quadratic-recurrence step is bounded by a common
characteristic-root norm bound. -/
theorem quadratic_norm_step_bound {p q β₁ β₂ : R} {lam : ℝ} {S : ℕ → R}
    (hS : (quadratic p q).IsSolution S) (hsum : β₁ + β₂ = p)
    (hprod : β₁ * β₂ = -q) (h1 : ‖β₁‖ ≤ lam) (h2 : ‖β₂‖ ≤ lam)
    (hlam : 0 ≤ lam) (k : ℕ) :
    ‖S (k + 1)‖ ≤ lam * ‖S k‖ + lam ^ k * (‖S 1‖ + lam * ‖S 0‖) := by
  have hT := quadratic_telescope hS hsum hprod k
  have hD : ‖S 1 - β₁ * S 0‖ ≤ ‖S 1‖ + lam * ‖S 0‖ := by
    calc
      ‖S 1 - β₁ * S 0‖ ≤ ‖S 1‖ + ‖β₁ * S 0‖ := norm_sub_le _ _
      _ ≤ ‖S 1‖ + lam * ‖S 0‖ := by
        gcongr
        exact norm_mul_le_of_le h1 le_rfl
  have hE : S (k + 1) = β₁ * S k + β₂ ^ k * (S 1 - β₁ * S 0) := by
    rw [sub_eq_iff_eq_add] at hT
    simpa [add_comm] using hT
  rw [hE]
  calc
    ‖β₁ * S k + β₂ ^ k * (S 1 - β₁ * S 0)‖
        ≤ ‖β₁ * S k‖ + ‖β₂ ^ k * (S 1 - β₁ * S 0)‖ := norm_add_le _ _
    _ ≤ lam * ‖S k‖ + lam ^ k * ‖S 1 - β₁ * S 0‖ := by
      gcongr
      · exact norm_mul_le_of_le h1 le_rfl
      · exact norm_pow_mul_le β₂ _ h2 hlam k
    _ ≤ lam * ‖S k‖ + lam ^ k * (‖S 1‖ + lam * ‖S 0‖) := by gcongr

/-- A quadratic recurrence with bounded characteristic roots has at most a
linear factor times the corresponding geometric norm bound. -/
theorem quadratic_norm_bound {p q β₁ β₂ : R} {lam : ℝ} {S : ℕ → R}
    (hS : (quadratic p q).IsSolution S) (hsum : β₁ + β₂ = p)
    (hprod : β₁ * β₂ = -q) (h1 : ‖β₁‖ ≤ lam) (h2 : ‖β₂‖ ≤ lam)
    (hlam : 0 ≤ lam) (k : ℕ) :
    lam * ‖S k‖ ≤ lam ^ (k + 1) * ‖S 0‖ +
      (k : ℝ) * lam ^ k * (‖S 1‖ + lam * ‖S 0‖) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := quadratic_norm_step_bound hS hsum hprod h1 h2 hlam k
      have hmul := mul_le_mul_of_nonneg_left ih hlam
      have hs := mul_le_mul_of_nonneg_left hstep hlam
      have hmul' : lam * (lam * ‖S k‖)
          ≤ lam ^ (k + 2) * ‖S 0‖ +
            (k : ℝ) * lam ^ (k + 1) * (‖S 1‖ + lam * ‖S 0‖) := by
        calc
          lam * (lam * ‖S k‖)
              ≤ lam * (lam ^ (k + 1) * ‖S 0‖ +
                  (k : ℝ) * lam ^ k * (‖S 1‖ + lam * ‖S 0‖)) := hmul
          _ = lam ^ (k + 2) * ‖S 0‖ +
              (k : ℝ) * lam ^ (k + 1) * (‖S 1‖ + lam * ‖S 0‖) := by ring
      have hs' : lam * ‖S (k + 1)‖
          ≤ lam * (lam * ‖S k‖) + lam ^ (k + 1) * (‖S 1‖ + lam * ‖S 0‖) := by
        calc
          lam * ‖S (k + 1)‖
              ≤ lam * (lam * ‖S k‖ + lam ^ k * (‖S 1‖ + lam * ‖S 0‖)) := hs
          _ = lam * (lam * ‖S k‖) + lam ^ (k + 1) *
              (‖S 1‖ + lam * ‖S 0‖) := by ring
      norm_num
      nlinarith [hmul', hs']

end LinearRecurrence
