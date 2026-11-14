module

public import RealRooted.DerivativeRecurrence.HalfStepLag
import Mathlib.Data.Nat.Choose.Cast

/-!
# Associated Bell rows

Normalized associated Bell rows satisfy the seeded Euler recurrence with weight
`choose (q + 2 k - 1) (k - 1)`. For positive `k`, these weights are positive,
so the uniform half-step theorem gives PF rows, degree `m / k`, and directed
interlacing at every distance at most `k`.

Source: *Uniform half-step lag windows*
([source](https://github.com/PerAlexandersson/real-zero-preservers/tree/9cccd381)),
`weyl-operators/notes/uniform-half-step-lag-windows.md`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The associated Bell binomial weights are positive. -/
theorem associatedBell_weight_pos {k : ℕ} (q : ℕ) :
    0 < (((q + 2 * k - 1).choose (k - 1) : ℕ) : ℝ) := by
  exact_mod_cast Nat.choose_pos (show k - 1 ≤ q + 2 * k - 1 by lia)

/-- The normalized associated Bell recurrence is a seeded half-step recurrence. -/
theorem associatedBell_halfStepRows {A : ℕ → ℝ[X]} {k : ℕ} (hk : k ≠ 0)
    (hseed : ∀ m, m < k → A m = 1)
    (hstep : ∀ q, A (q + k) = thetaPlusOne (A (q + k - 1)) +
      C (((q + 2 * k - 1).choose (k - 1) : ℕ) : ℝ) * X * A q) :
    HalfStepRows A k (fun q ↦ (((q + 2 * k - 1).choose (k - 1) : ℕ) : ℝ)) := by
  exact ⟨hk, hseed, hstep, associatedBell_weight_pos⟩

/-- Associated Bell rows are PF, have degree `m / k` and positive leading coefficient,
and every `k + 1` consecutive rows form a directed interlacing clique. -/
theorem associatedBell_rows {A : ℕ → ℝ[X]} {k : ℕ} (hk : k ≠ 0)
    (hseed : ∀ m, m < k → A m = 1)
    (hstep : ∀ q, A (q + k) = thetaPlusOne (A (q + k - 1)) +
      C (((q + 2 * k - 1).choose (k - 1) : ℕ) : ℝ) * X * A q) (m : ℕ) :
    IsPFPolynomial (A m) ∧ (A m).natDegree = m / k ∧ HasPosLeadingCoeff (A m) ∧
      ∀ r, r ≤ k → StrictInterl (A m) (A (m + r)) := by
  have h := associatedBell_halfStepRows hk hseed hstep
  exact ⟨h.isPFPolynomial m, h.natDegree_eq_div m, h.hasPosLeadingCoeff m,
    fun _ hr ↦ h.strictInterl_add_of_le m hr⟩

/-- The quadratic weight in the lag-three associated Bell recurrence. -/
theorem associatedBell_weight_three (q : ℕ) :
    (((q + 5).choose 2 : ℕ) : ℝ) = ((q : ℝ) + 4) * ((q : ℝ) + 5) / 2 := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

/-- The cubic weight in the lag-four associated Bell recurrence. -/
theorem associatedBell_weight_four (q : ℕ) :
    (((q + 7).choose 3 : ℕ) : ℝ) =
      ((q : ℝ) + 5) * ((q : ℝ) + 6) * ((q : ℝ) + 7) / 6 := by
  have h := Nat.add_one_mul_choose_eq (q + 6) 2
  have hc : ((q : ℝ) + 7) * (((q + 6).choose 2 : ℕ) : ℝ) =
      (((q + 7).choose 3 : ℕ) : ℝ) * 3 := by exact_mod_cast h
  rw [Nat.cast_choose_two] at hc
  push_cast at hc
  linarith

example {A : ℕ → ℝ[X]} (hseed : ∀ m, m < 1 → A m = 1)
    (hstep : ∀ q, A (q + 1) = thetaPlusOne (A q) + X * A q) (m : ℕ) :
    IsPFPolynomial (A m) ∧ (A m).natDegree = m ∧ StrictInterl (A m) (A (m + 1)) := by
  have h := associatedBell_halfStepRows (k := 1) (by decide) hseed (by simpa using hstep)
  exact ⟨h.isPFPolynomial m, by simpa using h.natDegree_eq_div m,
    h.strictInterl_add_of_le m le_rfl⟩

example {A : ℕ → ℝ[X]} {k : ℕ} {c : ℕ → ℝ} (h : HalfStepRows A k c) :
    A k = 1 + C (c 0) * X := by
  simpa using h.halfStepSeq_two_mul_k

example {A : ℕ → ℝ[X]} {k : ℕ} {c : ℕ → ℝ} (h : HalfStepRows A k c) (m n : ℕ) :
    HalfStepWindow (halfStepSeq A) k n ∧ StrictInterl (A m) (A (m + k)) := by
  exact ⟨h.halfStepWindow n, h.strictInterl_add_of_le m le_rfl⟩

example {A : ℕ → ℝ[X]} {k : ℕ} {c : ℕ → ℝ} {q : ℕ} (hc : c q < 0) :
    ¬ HalfStepRows A k c := by
  intro h
  exact (not_lt_of_ge (h.pos q).le) hc

end RealRooted
