module

public import RealRooted.ExponentialRows.ProductInsertion
import Mathlib.Tactic

/-!
# The sparse recurrence for quartic insertion rows

The standard insertion recurrence specializes to the four-lag recurrence in
the unpublished manuscript associated with RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

public section

open Polynomial Finset

namespace RealRooted.ExponentialRows

/-- The quartic insertion recurrence in its four-lag form, with nonnegative indices. -/
theorem insertionRow_quartic_add_four (a b c : ℝ) (n : ℕ) :
    let w := markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)
    insertionRow w (n + 4) = insertionRow w (n + 3) +
      C (2 * a * (n + 3)) * X * insertionRow w (n + 2) +
      C (3 * b * (n + 3) * (n + 2)) * X * insertionRow w (n + 1) +
      C (4 * c * (n + 3) * (n + 2) * (n + 1)) * X * insertionRow w n := by
  dsimp only
  let B : ℝ[X] := C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4
  let w := markedBlockWeights B
  change insertionRow w (n + 4) = _
  rw [show n + 4 = (n + 3) + 1 by lia, insertionRow_succ]
  rw [show n + 3 + 1 = 4 + n by lia, sum_range_add]
  have ht : ∑ k ∈ range n, C ((n + 3).choose (4 + k) : ℝ) *
      w (4 + k + 1) * insertionRow w (n + 3 - (4 + k)) = 0 := by
    apply sum_eq_zero
    intro k hk
    simp [w, B, markedBlockWeights, coeff_C_mul, coeff_X_pow,
      show 4 + k ≠ 1 by lia, show 4 + k ≠ 2 by lia, show 4 + k ≠ 3 by lia]
  rw [ht, add_zero]
  have h2 : 2 * ((n + 3).choose 2 : ℝ) = (n + 3 : ℝ) * (n + 2) := by
    have hh := congrArg (fun k : ℕ => (k : ℝ))
      (Nat.descFactorial_eq_factorial_mul_choose (n + 3) 2)
    norm_num [Nat.descFactorial_succ] at hh
    nlinarith [hh]
  have h3 : 6 * ((n + 3).choose 3 : ℝ) =
      (n + 3 : ℝ) * (n + 2) * (n + 1) := by
    have hh := congrArg (fun k : ℕ => (k : ℝ))
      (Nat.descFactorial_eq_factorial_mul_choose (n + 3) 3)
    norm_num [Nat.descFactorial_succ] at hh
    nlinarith [hh]
  norm_num [sum_range_succ, w, B, markedBlockWeights, coeff_C_mul, coeff_X_pow,
    show n + 3 - 1 = n + 2 by lia, show n + 3 - 2 = n + 1 by lia] at ⊢
  simp only [map_ofNat]
  have hp2 := congrArg C h2
  have hp3 := congrArg C h3
  simp only [map_mul, map_add, map_natCast, map_ofNat, map_one] at hp2 hp3
  linear_combination
    (3 * C b * X * insertionRow w (n + 1)) * hp2 +
    (4 * C c * X * insertionRow w n) * hp3

/-- The second standard quartic insertion row. -/
theorem insertionRow_quartic_two (a b c : ℝ) :
    insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) 2 =
      1 + C (2 * a) * X := by
  norm_num [map_ofNat, insertionRow_succ, sum_range_succ, markedBlockWeights, coeff_C_mul,
    coeff_X_pow]

/-- The third standard quartic insertion row. -/
theorem insertionRow_quartic_three (a b c : ℝ) :
    insertionRow (markedBlockWeights (C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) 3 =
      1 + C (6 * a + 6 * b) * X := by
  norm_num [map_ofNat, insertionRow_succ, sum_range_succ, markedBlockWeights, coeff_C_mul,
    coeff_X_pow]
  ring

end RealRooted.ExponentialRows
