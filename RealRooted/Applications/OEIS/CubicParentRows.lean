module

public import RealRooted.Graph.IndependencePolynomial.CubicParent
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# Three rows from the cubic parent

The downstream definitions of A184883, A114123, and A216182 are the three
normalizations below of the coefficients of

`1 / (1 + t - X t² + X t³)`.

A184883 is the even subsequence.  A114123 reverses each even coefficient
polynomial.  A216182 reverses the sign-corrected odd coefficient polynomial.
The real-rootedness statements follow from the general cubic-parent recurrence
theorems in `RealRooted.Graph.IndependencePolynomial.CubicParent`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.CubicParentRows

/-- The A184883 row polynomial, realized as the even cubic-parent coefficient. -/
def a184883 (n : ℕ) : ℝ[X] :=
  CubicParent.polynomial (2 * n)

/-- The A114123 row polynomial, with the recurrence used by the downstream row file. -/
def a114123 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 5 * X + X ^ 2
  | n + 3 =>
      (2 + X) * a114123 (n + 2) +
        (-1 + 2 * X) * a114123 (n + 1) + X * a114123 n

/-- The A216182 row polynomial, with the recurrence used by the downstream row file. -/
def a216182 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 + X
  | 2 => 5 + 7 * X + X ^ 2
  | n + 3 =>
      (2 + X) * a216182 (n + 2) +
        (-1 + 2 * X) * a216182 (n + 1) + X * a216182 n

/-- The A184883 model satisfies its downstream order-three recurrence. -/
theorem a184883_add_three (n : ℕ) :
    a184883 (n + 3) =
      (1 + 2 * X) * a184883 (n + 2) +
        (2 * X - X ^ 2) * a184883 (n + 1) + X ^ 2 * a184883 n := by
  unfold a184883
  simpa only [show 2 * (n + 3) = 2 * n + 6 by lia,
    show 2 * (n + 2) = 2 * n + 4 by lia,
    show 2 * (n + 1) = 2 * n + 2 by lia] using
      CubicParent.polynomial_add_six (2 * n)

/-- Reflecting A114123 at its row index gives A184883. -/
theorem reflect_a114123_eq_a184883 (n : ℕ) :
    reflect n (a114123 n) = a184883 n := by
  simpa only [a184883] using
    CubicParent.reflect_eq_even_of_recurrence a114123 rfl rfl rfl
      (fun k ↦ by rw [a114123]) n

/-- Reflecting A216182 at its row index gives the sign-corrected odd parent coefficient. -/
theorem reflect_a216182_eq_odd_parent (n : ℕ) :
    reflect n (a216182 n) = C (-1) * CubicParent.polynomial (2 * n + 1) := by
  exact CubicParent.reflect_eq_odd_of_recurrence a216182 rfl rfl rfl
    (fun k ↦ by rw [a216182]) n

/-- Every A184883 row polynomial splits over `ℝ`. -/
theorem a184883_splits (n : ℕ) : (a184883 n).Splits := by
  exact CubicParent.polynomial_splits (2 * n)

/-- Every A114123 row polynomial splits over `ℝ`. -/
theorem a114123_splits (n : ℕ) : (a114123 n).Splits := by
  exact CubicParent.splits_of_even_reflected_recurrence
    a114123 rfl rfl rfl (fun k ↦ by rw [a114123]) n

/-- Every A216182 row polynomial splits over `ℝ`. -/
theorem a216182_splits (n : ℕ) : (a216182 n).Splits := by
  exact CubicParent.splits_of_odd_reflected_recurrence
    a216182 rfl rfl rfl (fun k ↦ by rw [a216182]) n

end RealRooted.CubicParentRows
