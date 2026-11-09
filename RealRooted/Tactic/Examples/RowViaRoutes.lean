module

public import RealRooted.Basic
import RealRooted.Tactic.RowInterlacing

/-!
# Forcing each selectable row route with `via`

Every route of `rr_row_splits`, `rr_row_interlaces` and `rr_row_strictInterl` that is selectable
through the `(via := route)` hint has an example here that proves a small family with that route
alone, so that a regression breaking the route fails the build even when another route would
still prove the goal without the hint (`RealRooted/Tactic/ROUTES.md`).

Not covered, because `via` is not accepted by these front ends: the `recurrence` route of the
degree tactics (`rr_row_natDegree` selects only `cone` and `cancel`) and the `threeTerm`,
`secondOrder` and `derivativeMult` routes of `rr_row_nonneg_coeffs`, which takes no hints.
The former `rationalReverse` route was removed: it never elaborated its auxiliary theorem
(`Term.exprToSyntax` holes are unassigned in a fresh command context), and its only example had
passed through a hidden `sorryAx`.
-/

@[expose] public section

open Polynomial RealRooted

namespace RealRooted.Tactic.Examples.RowViaRoutes

noncomputable section

/-! ### `rr_row_splits` -/

/-- Rows `(1 + X) * P n`: their interlacing is proved once and reused by `reuse`. -/
def reuseRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * reuseRows n

theorem reuseRows_interlaces (n : ℕ) : Interlaces (reuseRows n) (reuseRows (n + 1)) := by
  rr_row_interlaces

example (n : ℕ) : (reuseRows n).Splits := by
  rr_row_splits (via := reuse)

example (n : ℕ) : StrictInterl (reuseRows n) (reuseRows (n + 1)) := by
  rr_row_strictInterl (via := reuse)

example (h : ∀ n, StrictInterl (reuseRows n) (reuseRows (n + 1))) (n : ℕ) :
    (reuseRows n).Splits := by
  rr_row_splits (via := reuse)

/-- `reuse` only closes goals about a sequence with a statement in scope. -/
def reuseOtherRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (2 + X) * reuseOtherRows n

example : True := by
  fail_if_success
    have : ∀ n, (reuseOtherRows n).Splits := by
      rr_row_splits (via := reuse)
  trivial

/-- A fixed split factor times `(X * P n)'` (A094262). -/
def derivativeXMulRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X + X ^ 3 + 2 * X ^ 2) * (derivativeXMulRows n).derivative +
      (1 + X ^ 2 + 2 * X) * derivativeXMulRows n

example (n : ℕ) : (derivativeXMulRows n).Splits := by
  rr_row_splits (via := derivativeXMul)

/-- A two-lag row whose recurrence has the fixed factor `1 + 2 X + X ^ 2` (A090452). -/
def factorPowerRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X + 2 * X ^ 2
  | n + 2 =>
      (C (1 / (4 + (n : ℝ)) * (5 + 2 * (n : ℝ))) +
          C (1 / (4 + (n : ℝ)) * (15 + 6 * (n : ℝ))) * X +
          C (1 / (4 + (n : ℝ)) * (10 + 4 * (n : ℝ))) * X ^ 2) * factorPowerRows (n + 1) +
        (C (1 / (4 + (n : ℝ)) * (-1 - (n : ℝ))) +
          C (1 / (4 + (n : ℝ)) * (-2 - 2 * (n : ℝ))) * X +
          C (1 / (4 + (n : ℝ)) * (-1 - (n : ℝ))) * X ^ 2) * factorPowerRows n

example (n : ℕ) : (factorPowerRows n).Splits := by
  rr_row_splits (via := factorPower)

/-- A product after three exceptional rows (A147644). -/
def delayedProductRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 2 * X + X ^ 2
  | 3 => 1 + 5 * X + 5 * X ^ 2 + X ^ 3
  | n + 4 => (1 + X) * delayedProductRows (n + 3)

example (n : ℕ) : (delayedProductRows n).Splits := by
  rr_row_splits (via := delayedProduct)

/-- A path-power subsequence with lag two (A277627). -/
def pathPowerRows : ℕ → ℝ[X]
  | 0 => X
  | 1 => X ^ 2
  | 2 => X ^ 3
  | n + 3 => X * pathPowerRows (n + 2) + X ^ 2 * pathPowerRows n

example (n : ℕ) : (pathPowerRows n).Splits := by
  rr_row_splits (via := pathPower)

/-- Orbit sums of the Haglund--Zhang threshold matrix with rows `(1, 1), (2, 1), (3, 1)` on the
input `[1, 0, 0]` (A120987). -/
def thresholdOrbitRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 * X
  | 2 => 3 * X + 6 * X ^ 2
  | n + 3 => (3 * X) * thresholdOrbitRows (n + 2) +
      ((-3 * X ^ 2) + 3 * X) * thresholdOrbitRows (n + 1) +
      (X + X ^ 3 + -2 * X ^ 2) * thresholdOrbitRows n

example (n : ℕ) : (thresholdOrbitRows n).Splits := by
  rr_row_splits (via := thresholdOrbit)

/-- A derivative recurrence of degree `n / 2`, with nonnegative rows (A008303). -/
def halfDegreeRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (2 * X - 2 * X ^ 2) * (halfDegreeRows n).derivative +
      (2 + C (n : ℝ) * X) * halfDegreeRows n

example (n : ℕ) : (halfDegreeRows n).Splits := by
  rr_row_splits (via := degreePattern)

/-- Order three with a positive feedback window through the lag `3 X` (A317496). -/
def lagFeedbackRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => 1 * lagFeedbackRows (n + 2) + 3 * X * lagFeedbackRows n

example (n : ℕ) : (lagFeedbackRows n).Splits := by
  rr_row_splits (via := lagFeedback)

/-- Alternating runs: the rows are `f`-polynomial images of half-growth rows (A186370). -/
def alternatingRunsRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X - X ^ 3) * (alternatingRunsRows n).derivative +
      (1 + X + C (n : ℝ) * X ^ 2) * alternatingRunsRows n

example (n : ℕ) : (alternatingRunsRows n).Splits := by
  rr_row_splits (via := fTransform)

/-! ### `rr_row_interlaces` -/

/-- Central factorial numbers: the reversed rows satisfy an Euler step (A008957). -/
def reversedRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C 1 * X ^ 3 * (reversedRows n).derivative.derivative +
      C (-1 - 2 * (n : ℝ)) * X ^ 2 * (reversedRows n).derivative +
      (C 1 + C (((n : ℝ) + 1) ^ 2) * X) * reversedRows n

example (n : ℕ) : Interlaces (reversedRows n) (reversedRows (n + 1)) := by
  rr_row_interlaces (via := reversed)

example (n : ℕ) : (reversedRows n).Splits := by
  rr_row_splits (via := reversed)

/-- Order three with a characteristic polynomial that factors into parity products (A092879). -/
def parityProductRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + 1
  | 2 => 2 * X ^ 2 + 3 * X + 1
  | n + 3 => (X + 1) * parityProductRows (n + 2) + (X + X ^ 2) * parityProductRows (n + 1) -
      X ^ 3 * parityProductRows n

example (n : ℕ) : Interlaces (parityProductRows n) (parityProductRows (n + 1)) := by
  rr_row_interlaces (via := parityProduct)

example (n : ℕ) : (parityProductRows n).Splits := by
  rr_row_splits (via := parityProduct)

/-- Roots in the window `[-1, 0]`: `X * (X + 1)` is nonpositive only there (A019538). -/
def endpointWindowRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X + X ^ 2) * (endpointWindowRows n).derivative +
      (1 + 2 * X) * endpointWindowRows n

example (n : ℕ) : Interlaces (endpointWindowRows n) (endpointWindowRows (n + 1)) := by
  rr_row_interlaces (via := endpointWindow)

example (n : ℕ) : Interlaces (endpointWindowRows n) (endpointWindowRows (n + 1)) := by
  rr_row_interlaces (via := window)

/-- A357613 in its downstream form, with the rational coefficients written as products with
`1 / (-7 / 3 - 5 / 3 * n + 2 / 3 * (2 + n) ^ 2)`.  The top terms of the recurrence cancel, and
the auxiliary degree and leading-coefficient theorems of the `endpointWindow` route took about
`390000` heartbeats when they were proved by the two separate degree tactics, which exceeds the
default limit.  The route now proves both by one cancellation certificate, so the plain call
below stays within the default budget. -/
def endpointWindowRationalRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
    ((C ((1 / ((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((2 + (n : ℝ))) ^ (2)))) *
          (-1 + ((-3 / 2) * (n : ℝ)))) * X +
      C ((1 / ((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((2 + (n : ℝ))) ^ (2)))) *
          ((-7 / 6) + ((-5 / 3) * (n : ℝ)))) * X ^ 2 +
      C ((1 / ((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((2 + (n : ℝ))) ^ (2)))) *
          ((-1 / 6) + ((-1 / 6) * (n : ℝ)))) * X ^ 3)) *
        (endpointWindowRationalRows n).derivative +
    ((C ((1 / ((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((2 + (n : ℝ))) ^ (2)))) *
          (-17 + ((-27 / 2) * (n : ℝ)) + ((9 / 2) * ((2 + (n : ℝ))) ^ (2)))) +
      C ((1 / ((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((2 + (n : ℝ))) ^ (2)))) *
          ((-46 / 3) + (4 * ((2 + (n : ℝ))) ^ (2)) + ((-37 / 3) * (n : ℝ)))) * X +
      C ((1 / ((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((2 + (n : ℝ))) ^ (2)))) *
          ((-2 / 3) + ((-1 / 2) * (n : ℝ)) + ((1 / 6) * ((2 + (n : ℝ))) ^ (2)))) * X ^ 2)) *
      endpointWindowRationalRows n

example (n : ℕ) :
    Interlaces (endpointWindowRationalRows n) (endpointWindowRationalRows (n + 1)) := by
  rr_row_interlaces

/-- Multipliers that are powers of the single linear factor `X`:
`P (n + 2) = X P (n + 1) + X ^ 2 P n` (A127647). -/
def powerFormRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * powerFormRows (n + 1) + X ^ 2 * powerFormRows n

example (n : ℕ) : Interlaces (powerFormRows n) (powerFormRows (n + 1)) := by
  rr_row_interlaces (via := powerForm)

/-- Central factorial numbers: a second-order Euler step with `κ = a = b = 1` (A036969). -/
def eulerStepRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (eulerStepRows n).derivative.derivative +
      (3 * X) * (eulerStepRows n).derivative + (1 + X) * eulerStepRows n

example (n : ℕ) : Interlaces (eulerStepRows n) (eulerStepRows (n + 1)) := by
  rr_row_interlaces (via := eulerStep)

/-- Eulerian numbers: `A = X (1 - X)` has a negative coefficient, but the sign conditions hold
globally (A008292). -/
def signRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X + C (-1) * X ^ 2) * (signRows n).derivative +
      (C 1 + C (1 + (n : ℝ)) * X) * signRows n

example (n : ℕ) : Interlaces (signRows n) (signRows (n + 1)) := by
  rr_row_interlaces (via := sign)

/-- Roots in `(-∞, -1]` beyond which the multiplier `A = X + 1` has a fixed sign (A137597). -/
def degreeWindowRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * (degreeWindowRows n).derivative + (2 + X) * degreeWindowRows n

example (n : ℕ) : Interlaces (degreeWindowRows n) (degreeWindowRows (n + 1)) := by
  rr_row_interlaces (via := degreeWindow)

/-- Roots in `(-∞, 0]` while the lag `X - X ^ 2` is positive beyond `1`: the leading
coefficients control the window (A098158). -/
def ratioWindowRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * ratioWindowRows (n + 1) + (X + -1 * X ^ 2) * ratioWindowRows n

example (n : ℕ) : Interlaces (ratioWindowRows n) (ratioWindowRows (n + 1)) := by
  rr_row_interlaces (via := ratioWindow)

/-- Chebyshev-like rows: the lag `-(1 + X)` is negative beyond the window `[-1, 0]`, and the
ratio barrier `ρ = 1` keeps the rows positive there (A056242). -/
def barrierWindowRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | n + 2 => (2 + 2 * X) * barrierWindowRows (n + 1) + (-1 - X) * barrierWindowRows n

example (n : ℕ) : Interlaces (barrierWindowRows n) (barrierWindowRows (n + 1)) := by
  rr_row_interlaces (via := barrierWindow)

/-- The roots stay in `[L n, 0]` with `L n = -(8 n + 21) / (9 n + 24)` decreasing (A370258). -/
def movingWindowRows : ℕ → ℝ[X]
  | 0 => 1 + 10 * X + 15 * X ^ 2
  | n + 1 =>
      (C ((21 / 2 + 4 * (n : ℝ)) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X +
          C ((12 + 9 / 2 * (n : ℝ)) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X ^ 2) *
        (movingWindowRows n).derivative +
      (C 1 + C ((24 + 9 * (2 + (n : ℝ)) ^ 2 + 21 / 2 * n) /
          (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X) * movingWindowRows n

example (n : ℕ) : Interlaces (movingWindowRows n) (movingWindowRows (n + 1)) := by
  rr_row_interlaces (via := movingWindow)

/-- The roots stay below the moving rational bound `-(n + 3) / (8 n + 21)` (A110608). -/
def movingUpperRows : ℕ → ℝ[X]
  | 0 => 6 + 8 * X + X ^ 2
  | n + 1 =>
      (C ((3 / 2 + (n : ℝ) / 2) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) +
          C ((9 + 7 / 2 * (n : ℝ)) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X +
          C ((-21 / 2 - 4 * (n : ℝ)) / (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X ^ 2) *
        (movingUpperRows n).derivative +
      (C ((18 + 8 * (n : ℝ) + 15 / 2 * (2 + (n : ℝ)) ^ 2) /
            (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) +
          C ((12 + 6 * (2 + (n : ℝ)) ^ 2 + 11 / 2 * n) /
            (7 + 2 * (2 + (n : ℝ)) ^ 2 + 3 * n)) * X) * movingUpperRows n

example (n : ℕ) : Interlaces (movingUpperRows n) (movingUpperRows (n + 1)) := by
  rr_row_interlaces (via := movingUpper)

/-- Alternating runs again: the transformed auxiliary rows interlace (A008970). -/
def alternatingRunsInterlacesRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X + C (-1) * X ^ 3) * (alternatingRunsInterlacesRows n).derivative +
      (C 1 + C 2 * X + C (n : ℝ) * X ^ 2) * alternatingRunsInterlacesRows n

example (n : ℕ) :
    Interlaces (alternatingRunsInterlacesRows n) (alternatingRunsInterlacesRows (n + 1)) := by
  rr_row_interlaces (via := fTransform)

/-- A first-order recurrence whose f-transformed auxiliary rows the nested interlacing search
cannot handle (A104978).  The route must fail visibly: an error inside its auxiliary command once
became a hidden `sorryAx` under asynchronous elaboration. -/
def fTransformFailingRows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      ((C (((1 / 2) * (n : ℝ) * (1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))))) +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) * (3 + (5 * (n : ℝ))))) *
          X +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (3 + ((9 / 2) * (n : ℝ))))) * X ^ 2)) * (fTransformFailingRows n).derivative +
      ((C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (-25 + (7 * ((2 + (n : ℝ))) ^ (2)) + ((-37 / 2) * (n : ℝ))))) +
        C (((1 / ((-5 + (-3 * (n : ℝ)) + (2 * ((2 + (n : ℝ))) ^ (2))))) *
          (-33 + (9 * ((2 + (n : ℝ))) ^ (2)) + ((-51 / 2) * (n : ℝ))))) * X)) *
        fTransformFailingRows n

example : True := by
  fail_if_success
    have : ∀ n, Interlaces (fTransformFailingRows n) (fTransformFailingRows (n + 1)) := by
      rr_row_interlaces (via := fTransform)
  trivial

/-! ### `rr_row_strictInterl` -/

example (n : ℕ) : StrictInterl (halfDegreeRows n) (halfDegreeRows (n + 1)) := by
  rr_row_strictInterl (via := degreePattern)

/-- Rows with constant multipliers `b ≤ 0` (A056241): strict interlacing by projecting
`Interlaces`. -/
def strictFallbackRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (2 + 2 * X) * strictFallbackRows (n + 1) +
      (-1 + -1 * X + -1 * X ^ 2) * strictFallbackRows n

example (n : ℕ) : StrictInterl (strictFallbackRows n) (strictFallbackRows (n + 1)) := by
  rr_row_strictInterl (via := interlaces)

end

end RealRooted.Tactic.Examples.RowViaRoutes
