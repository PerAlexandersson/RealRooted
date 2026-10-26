module

public import RealRooted.CombinatorialExamples.WeightedRenewal
public import RealRooted.Tactic.RowInterlacing

/-!
# Fixed-delay row-tactic regressions

These examples exercise varying nonnegative weights, a scaled recurrence, the canonical
path-power family, and the rigid-renewal path-power identification.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Tactic.Examples.RowVariableDelay

/-- A delay-three recurrence with arbitrary varying weights, including zero weights. -/
def varyingDelayRows (w : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => varyingDelayRows w n + C (w (n + 1)) * X * varyingDelayRows w (n + 1 - 3)

example {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (n : ℕ) :
    HasNonnegCoeffs (varyingDelayRows w n) := by
  rr_row_nonneg_coeffs

example {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (n : ℕ) :
    (varyingDelayRows w n).Splits := by
  rr_row_splits

example {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {A B : ℕ}
    (hAB : A ≤ B) (hBA : B ≤ A + 3) :
    StrictInterl (varyingDelayRows w A) (varyingDelayRows w B) := by
  rr_row_window

/-- A scaled delay-two recurrence. -/
def scaledDelayRows (a b : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C (a (n + 1)) * scaledDelayRows a b n +
      C (b (n + 1)) * X * scaledDelayRows a b (n + 1 - 2)

example {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 ≤ b n) (n : ℕ) :
    HasNonnegCoeffs (scaledDelayRows a b n) := by
  rr_row_nonneg_coeffs

example {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 ≤ b n) (n : ℕ) :
    (scaledDelayRows a b n).Splits := by
  rr_row_splits

example {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 ≤ b n) {A B : ℕ}
    (hAB : A ≤ B) (hBA : B ≤ A + 2) :
    StrictInterl (scaledDelayRows a b A) (scaledDelayRows a b B) := by
  rr_row_strictInterl

/-! ## Canonical path-power models -/

example (k A s : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (hsk : s ≤ k) :
    StrictInterl (pathPowerCliquePolynomial k A) (pathPowerCliquePolynomial k (A + s)) := by
  rr_row_window

example (d ℓ n s : ℕ) (hd : 1 ≤ d) (hℓ : 1 ≤ ℓ) (hs : d * s ≤ d * ℓ + 1) :
    StrictInterl (rigidRenewalPolynomial d ℓ n)
      (rigidRenewalPolynomial d ℓ (n + s)) := by
  rw [rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ n hℓ,
    rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ (n + s) hℓ]
  by_cases hs0 : s = 0
  · subst s
    simp only [Nat.add_zero]
    rr_row_window
  have hdelay : 2 ≤ d * ℓ + 1 := by nlinarith
  have hstep : 1 ≤ d * s := Nat.mul_pos hd (Nat.pos_of_ne_zero hs0)
  have hpath : StrictInterl (pathPowerCliquePolynomial (d * ℓ + 1) (d * n))
      (pathPowerCliquePolynomial (d * ℓ + 1) (d * n + d * s)) := by
    rr_row_window
  simpa only [Nat.mul_add] using hpath

/-! ## Negative tests -/

/-- The same recurrence with a negative weight. -/
def negativeDelayRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => negativeDelayRows n + C (-1) * X * negativeDelayRows (n + 1 - 3)

example : True := by
  fail_if_success
    have _ (n : ℕ) : (negativeDelayRows n).Splits := by
      rr_row_splits
  trivial

example : True := by
  fail_if_success
    have _ : StrictInterl (varyingDelayRows (fun _ ↦ 1) 0)
        (varyingDelayRows (fun _ ↦ 1) 4) := by
      rr_row_window
  trivial

end RealRooted.Tactic.Examples.RowVariableDelay
