import RealRooted.Applications.OEIS.A286785
import RealRooted.Tactic.RowInterlacing

/-!
# Regression examples for Euler-type interlacing bridges

These examples cover the floor-half and rational `f`-transforms, a moving
endpoint window, canonical-model normalization, and rational reflection.
-/

open RealRooted Polynomial

noncomputable section

namespace FTransformInterlacingExamples

/-- The A186370 row recurrence, whose auxiliary transform has degree `n / 2`. -/
def a186370 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (C 1 * X + C (-1) * X ^ 3) * (a186370 n).derivative +
        (C 1 + C 1 * X + C (n : ℝ) * X ^ 2) * a186370 n

/-- The floor-half transform route supplies the explicit `X + 1` padding. -/
example (n : ℕ) : Interlaces (a186370 n) (a186370 (n + 1)) := by
  rr_row_interlaces

end FTransformInterlacingExamples

namespace EndpointWindowInterlacingExamples

/-- A factored presentation of the A357613 recurrence. -/
def a357613 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      let D : ℝ := 2 * ((n : ℝ) + 1) * (2 * n + 1)
      let A := C (D⁻¹) *
        (-X * (X + 1) *
          (C ((n : ℝ) + 1) * X + C (9 * (n : ℝ) + 6)))
      let B := C (D⁻¹) *
        (C ((n : ℝ) * (n + 1)) * X ^ 2 +
          C (24 * (n : ℝ) ^ 2 + 22 * (n : ℝ) + 4) * X +
          C (27 * (n : ℝ) ^ 2 + 27 * (n : ℝ) + 6))
      A * (a357613 n).derivative + B * a357613 n

/-- The exact probe fits `(-9 + 3 / (n + 1), -1)` and the symbolic
certificate proves both endpoint evaluations. -/
example (n : ℕ) : Interlaces (a357613 n) (a357613 (n + 1)) := by
  rr_row_interlaces

end EndpointWindowInterlacingExamples

namespace ModelBridgeInterlacingExamples

/-- The normalized form of the A286785 harness recurrence. -/
def a286785 : ℕ → ℝ[X]
  | 0 => 14 + 14 * X + 2 * X ^ 2
  | n + 1 =>
      let S : ℝ := 2 * (n + 5) * (2 * n + 9)
      let A := C ((n + 3) / S) + C ((7 * n + 33) / S) * X -
        C ((8 * n + 36) / S) * X ^ 2
      let B := C (3 * (5 * (n : ℝ) ^ 2 + 42 * n + 89) / S) +
        C (6 * (n + 3) * (2 * n + 9) / S) * X
      A * (a286785 n).derivative + B * a286785 n

/-- Exact rows identify the recurrence with `A286785.rowPoly (n + 2)`. -/
example (n : ℕ) : Interlaces (a286785 n) (a286785 (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (a286785 n).Splits := by
  rr_row_splits

end ModelBridgeInterlacingExamples

namespace RationalTransformInterlacingExamples

/-- A denominator-cleared presentation of the A104978 harness recurrence. -/
def a104978 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      let D : ℝ := (n + 1) * (2 * n + 3)
      let A := C ((n : ℝ) / (2 * D)) + C ((5 * n + 3) / D) * X +
        C ((9 * (n : ℝ) + 6) / (2 * D)) * X ^ 2
      let B := C ((14 * (n : ℝ) ^ 2 + 19 * n + 6) / (2 * D)) +
        C ((18 * (n : ℝ) ^ 2 + 21 * n + 6) / (2 * D)) * X
      A * (a104978 n).derivative + B * a104978 n

/-- The common positive denominator is fitted and then cleared in the proof. -/
example (n : ℕ) : Interlaces (a104978 n) (a104978 (n + 1)) := by
  rr_row_interlaces

/-- The reflected A108426 harness recurrence. -/
def a108426 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      let D : ℝ := (n + 1) * (2 * n + 3)
      let A := -C ((9 * n + 6) / (2 * D)) * X -
        C ((5 * n + 3) / D) * X ^ 2 - C ((n : ℝ) / (2 * D)) * X ^ 3
      let B := C ((27 * (n : ℝ) ^ 2 + 27 * n + 6) / (2 * D)) +
        C ((24 * (n : ℝ) ^ 2 + 25 * n + 6) / (2 * D)) * X +
        C ((n : ℝ) ^ 2 / (2 * D)) * X ^ 2
      A * (a108426 n).derivative + B * a108426 n

/-- Reflection transfers the rational f-transform interlacing certificate. -/
example (n : ℕ) : Interlaces (a108426 n) (a108426 (n + 1)) := by
  rr_row_interlaces

end RationalTransformInterlacingExamples
