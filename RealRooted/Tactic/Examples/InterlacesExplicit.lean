import RealRooted.Tactic.RowInterlacing

/-!
# Explicit interlacing examples

Regression tests for `rr_interlaces_explicit` (Euclidean certificates, including
common factors) and for `rr_row_interlaces` on two-step products
`P (n + 2) = q * P n`, drawn from `real-rooted-oeis-proofs`.
-/

open Polynomial

namespace RealRooted.Tactic.InterlacesExplicitExamples

example : Interlaces (1 + X : ℝ[X]) (1 + 3 * X + X ^ 2) := by rr_interlaces_explicit

/-- A common root at `0` is cancelled first. -/
example : Interlaces (3 * X + X ^ 2 : ℝ[X]) (3 * X + 6 * X ^ 2 + X ^ 3) := by
  rr_interlaces_explicit

/-- A common factor of degree three with rational roots. -/
example : Interlaces (1 + 5 * X + 8 * X ^ 2 + 4 * X ^ 3 : ℝ[X])
    ((1 + 2 * X ^ 2 + 3 * X) * (1 + 3 * X + 2 * X ^ 2)) := by
  rr_interlaces_explicit

noncomputable section

/-- A two-step product (A026374). -/
def A026374 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (1 + X ^ 2 + 3 * X) * A026374 n

theorem A026374_interlaces (n : ℕ) : Interlaces (A026374 n) (A026374 (n + 1)) := by
  rr_row_interlaces

/-- A two-step product with higher-degree base rows (A064861). -/
def A064861 : ℕ → ℝ[X]
  | 0 => 1 + 3 * X + 2 * X ^ 2
  | 1 => 1 + 5 * X + 8 * X ^ 2 + 4 * X ^ 3
  | n + 2 => (1 + 2 * X ^ 2 + 3 * X) * A064861 n

theorem A064861_interlaces (n : ℕ) : Interlaces (A064861 n) (A064861 (n + 1)) := by
  rr_row_interlaces

end

end RealRooted.Tactic.InterlacesExplicitExamples
