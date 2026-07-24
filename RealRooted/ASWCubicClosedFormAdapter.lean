import RealRooted.ASWCubicClosedForm
import RealRooted.ASWCubicCharacteristic

/-!
# Closed-form adapter for cubic ASW minors

This file proves uniqueness for the cubic recurrence and identifies the
shift-one contiguous Toeplitz minors with the conjugate-root closed form once
the three roots satisfy the Vieta equations.
-/

noncomputable section

namespace RealRooted

private lemma eq_of_cubic_recurrence
    (s1 s2 s3 : ℂ) (x y : ℕ → ℂ)
    (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2)
    (hx : ∀ n, x (n + 3) = s1 * x (n + 2) - s2 * x (n + 1) + s3 * x n)
    (hy : ∀ n, y (n + 3) = s1 * y (n + 2) - s2 * y (n + 1) + s3 * y n) :
    x = y := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · exact h0
      · exact h1
      · exact h2
      · rw [hx n, hy n, ih (n + 2) (by lia), ih (n + 1) (by lia), ih n (by lia)]

/-- A cubic recurrence with the complete-homogeneous initial values equals
the partial-fraction closed form for its real root and conjugate pair. -/
theorem eq_aswCubicClosedForm_of_recurrence
    (x : ℕ → ℂ) (r : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (h0 : x 0 = 1)
    (h1 : x 1 = (r : ℂ) + z + starRingEnd ℂ z)
    (h2 : x 2 = ((r : ℂ) + z + starRingEnd ℂ z) ^ 2 -
      ((r : ℂ) * z + (r : ℂ) * starRingEnd ℂ z + z * starRingEnd ℂ z))
    (hrec : ∀ n,
      x (n + 3) = ((r : ℂ) + z + starRingEnd ℂ z) * x (n + 2) -
        ((r : ℂ) * z + (r : ℂ) * starRingEnd ℂ z + z * starRingEnd ℂ z) *
          x (n + 1) + (r : ℂ) * z * starRingEnd ℂ z * x n) :
    x = aswCubicClosedForm r z := by
  apply eq_of_cubic_recurrence
    ((r : ℂ) + z + starRingEnd ℂ z)
    ((r : ℂ) * z + (r : ℂ) * starRingEnd ℂ z + z * starRingEnd ℂ z)
    ((r : ℂ) * z * starRingEnd ℂ z) x (aswCubicClosedForm r z)
  · rw [aswCubicClosedForm_zero r hz]
    exact h0
  · rw [aswCubicClosedForm_one r hz]
    exact h1
  · rw [aswCubicClosedForm_two r hz]
    exact h2
  · exact hrec
  · exact aswCubicClosedForm_recurrence r hz

/-- The shift-one cubic Toeplitz minors equal the conjugate-root closed form
when the three roots satisfy the Vieta equations for the recurrence. -/
theorem aswShiftedToeplitzMinor_one_eq_closedForm
    (u : ℕ → ℝ) (hu : ∀ j, 4 ≤ j → u j = 0)
    (r : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (hsum : (r : ℂ) + z + starRingEnd ℂ z = u 1)
    (hpairs : (r : ℂ) * z + (r : ℂ) * starRingEnd ℂ z +
      z * starRingEnd ℂ z = u 0 * u 2)
    (hprod : (r : ℂ) * z * starRingEnd ℂ z = u 0 ^ 2 * u 3) :
    (fun n ↦ (aswShiftedToeplitzMinor u 1 n : ℂ)) = aswCubicClosedForm r z := by
  apply eq_aswCubicClosedForm_of_recurrence _ r hz
  · simp
  · simpa using hsum.symm
  · rw [aswShiftedToeplitzMinor_one_two]
    push_cast
    rw [hsum, hpairs]
  · intro n
    have hrec := congrArg (↑Complex.ofReal)
      (aswShiftedToeplitzMinor_one_cubic_rec u hu n)
    push_cast at hrec
    rw [hsum, hpairs, hprod]
    exact hrec

end RealRooted

