import RealRooted.Tactic.RowInterlacing

/-!
# Three-term recurrence examples

Regression tests for `rr_row_natDegree`, `rr_row_ne_zero`,
`rr_row_leadingCoeff_pos`, `rr_row_interlaces`, `rr_row_nonneg_coeffs`,
`rr_row_eval_zero_pos` and `rr_row_splits` on OEIS rows defined by
`P (n + 2) = a n * P (n + 1) + b n * P n` or `P (n + 1) = A n * (P n)' + B n * P n`,
drawn from `real-rooted-oeis-proofs`: the pilot rows, three-term recurrences with offset
three, summands in other orders, and the certificates and hints of `rr_row_interlaces?`.
-/

open Polynomial

namespace RealRooted.Tactic.RowInterlacingExamples

noncomputable section

/-- `b ≤ 0` everywhere, leading coefficients constant (`ρ = 1`) (A056241). -/
def A056241 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (2 + 2 * X) * A056241 (n + 1) + (-1 + -1 * X + -1 * X ^ 2) * A056241 n

theorem A056241_natDegree (n : ℕ) : (A056241 n).natDegree = n := by rr_row_natDegree
theorem A056241_ne_zero (n : ℕ) : A056241 n ≠ 0 := by rr_row_ne_zero
theorem A056241_leadingCoeff_pos (n : ℕ) : 0 < (A056241 n).leadingCoeff := by
  rr_row_leadingCoeff_pos
theorem A056241_interlaces (n : ℕ) : Interlaces (A056241 n) (A056241 (n + 1)) := by
  rr_row_interlaces

/-- Delannoy rows: `b = X ≤ 0` only on `(-∞, 0]`, rows with nonnegative
coefficients (A008288). -/
def A008288 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (1 + X) * A008288 (n + 1) + X * A008288 n

theorem A008288_natDegree (n : ℕ) : (A008288 n).natDegree = n := by rr_row_natDegree
theorem A008288_interlaces (n : ℕ) : Interlaces (A008288 n) (A008288 (n + 1)) := by
  rr_row_interlaces

/-- Narayana rows: rational `n`-dependent coefficients (A001263). -/
def A001263 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (C (1 / (4 + (n : ℝ)) * (5 + 2 * (n : ℝ))) + C (1 / (4 + (n : ℝ)) * (5 + 2 * (n : ℝ))) * X) *
          A001263 (n + 1) +
        (C (1 / (4 + (n : ℝ)) * (-1 + -1 * (n : ℝ))) +
          C (1 / (4 + (n : ℝ)) * (2 + 2 * (n : ℝ))) * X +
          C (1 / (4 + (n : ℝ)) * (-1 + -1 * (n : ℝ))) * X ^ 2) * A001263 n

theorem A001263_natDegree (n : ℕ) : (A001263 n).natDegree = n := by rr_row_natDegree
theorem A001263_interlaces (n : ℕ) : Interlaces (A001263 n) (A001263 (n + 1)) := by
  rr_row_interlaces

/-- Negative denominators `-2 - n` (A008459). -/
def A008459 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 =>
      (C (1 / (-2 + -1 * (n : ℝ)) * (-3 + -2 * (n : ℝ))) +
          C (1 / (-2 + -1 * (n : ℝ)) * (-3 + -2 * (n : ℝ))) * X) * A008459 (n + 1) +
        (C (1 / (-2 + -1 * (n : ℝ)) * (1 + (n : ℝ))) +
          C (1 / (-2 + -1 * (n : ℝ)) * (-2 + -2 * (n : ℝ))) * X +
          C (1 / (-2 + -1 * (n : ℝ)) * (1 + (n : ℝ))) * X ^ 2) * A008459 n

theorem A008459_natDegree (n : ℕ) : (A008459 n).natDegree = n := by rr_row_natDegree
theorem A008459_ne_zero (n : ℕ) : A008459 n ≠ 0 := by rr_row_ne_zero

/-- Stirling numbers of the second kind: a derivative recurrence with
nonnegative `A`, `B` (A008277). -/
def A008277 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * (A008277 n).derivative + (1 + X) * A008277 n

theorem A008277_interlaces (n : ℕ) : Interlaces (A008277 n) (A008277 (n + 1)) := by
  rr_row_interlaces

/-- Eulerian numbers: `A = X (1 - X)` has a negative coefficient, so nonnegativity of
the rows comes from the multiplier bound `n + 1 - j ≥ 0` (A008292). -/
def A008292 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X + C (-1) * X ^ 2) * (A008292 n).derivative +
      (C 1 + C (1 + (n : ℝ)) * X) * A008292 n

theorem A008292_interlaces (n : ℕ) : Interlaces (A008292 n) (A008292 (n + 1)) := by
  rr_row_interlaces

/-- A real-rooted quadratic base row: no base interlacing is needed (A075499). -/
def A075499 : ℕ → ℝ[X]
  | 0 => 16 + 12 * X + X ^ 2
  | n + 1 => (4 * X) * (A075499 n).derivative + (4 + X) * A075499 n

theorem A075499_natDegree (n : ℕ) : (A075499 n).natDegree = n + 2 := by rr_row_natDegree
theorem A075499_interlaces (n : ℕ) : Interlaces (A075499 n) (A075499 (n + 1)) := by
  rr_row_interlaces

/-- Root window `[-1, 0]`: `A = X (X + 1)` is nonpositive only there (A019538). -/
def A019538 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X + X ^ 2) * (A019538 n).derivative + (1 + 2 * X) * A019538 n

theorem A019538_interlaces (n : ℕ) : Interlaces (A019538 n) (A019538 (n + 1)) := by
  rr_row_interlaces

/-- Root window `(-∞, -1]`: `A = X + 1` (A137597). -/
def A137597 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * (A137597 n).derivative + (2 + X) * A137597 n

theorem A137597_interlaces (n : ℕ) : Interlaces (A137597 n) (A137597 (n + 1)) := by
  rr_row_interlaces

/-- A three-term recurrence with root window `[-1, 0]`: `b = X (X + 1)` (A111006). -/
def A111006 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * A111006 (n + 1) + (X + X ^ 2) * A111006 n

theorem A111006_interlaces (n : ℕ) : Interlaces (A111006 n) (A111006 (n + 1)) := by
  rr_row_interlaces

/-! ### Nonnegative coefficients, constant terms and splitting of the pilot rows -/

theorem A056241_splits (n : ℕ) : (A056241 n).Splits := by rr_row_splits

theorem A008288_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (A008288 n) := by
  rr_row_nonneg_coeffs
theorem A008288_eval_zero_pos (n : ℕ) : 0 < (A008288 n).eval 0 := by rr_row_eval_zero_pos
theorem A008288_splits (n : ℕ) : (A008288 n).Splits := by rr_row_splits

theorem A001263_splits (n : ℕ) : (A001263 n).Splits := by rr_row_splits

theorem A008459_interlaces (n : ℕ) : Interlaces (A008459 n) (A008459 (n + 1)) := by
  rr_row_interlaces
theorem A008459_splits (n : ℕ) : (A008459 n).Splits := by rr_row_splits

theorem A008277_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (A008277 n) := by
  rr_row_nonneg_coeffs
theorem A008277_eval_zero_pos (n : ℕ) : 0 < (A008277 n).eval 0 := by rr_row_eval_zero_pos
theorem A008277_splits (n : ℕ) : (A008277 n).Splits := by rr_row_splits

/-- Nonnegativity from the multiplier bound (`RealRooted.derivRec_hasNonnegCoeffs_of_mult`). -/
theorem A008292_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (A008292 n) := by
  rr_row_nonneg_coeffs
theorem A008292_eval_zero_pos (n : ℕ) : 0 < (A008292 n).eval 0 := by rr_row_eval_zero_pos
theorem A008292_splits (n : ℕ) : (A008292 n).Splits := by rr_row_splits

/-- `A n = 1 + X` does not vanish at `0`: the constant terms need the nonnegative
coefficients of the derivatives. -/
theorem A137597_eval_zero_pos (n : ℕ) : 0 < (A137597 n).eval 0 := by rr_row_eval_zero_pos
theorem A137597_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (A137597 n) := by
  rr_row_nonneg_coeffs

theorem A111006_splits (n : ℕ) : (A111006 n).Splits := by rr_row_splits

/-! ### Certificates and hints -/

/-- The certificate printed by `rr_row_interlaces?` for `A019538_interlaces`. -/
example (n : ℕ) : Interlaces (A019538 n) (A019538 (n + 1)) := by
  apply RealRooted.derivRec_interlaces_of_roots_mem_Icc (P := A019538) (D₀ := 0)
    (L := (-1 : ℝ)) (U := (0 : ℝ)) fun _ => rfl <;> rr_row_side

example (n : ℕ) : Interlaces (A019538 n) (A019538 (n + 1)) := by
  rr_row_interlaces (window := [-1, 0])

example (n : ℕ) : Interlaces (A137597 n) (A137597 (n + 1)) := by
  rr_row_interlaces (upper := -1)

example (n : ℕ) : Interlaces (A008292 n) (A008292 (n + 1)) := by
  rr_row_interlaces (thm := RealRooted.derivRec_interlaces_of_nonnegCoeffs) (degree := 0)

#guard_msgs (drop info) in
example (n : ℕ) : Interlaces (A111006 n) (A111006 (n + 1)) := by rr_row_interlaces?

/-! ### Offset three: explicit rows `0, 1, 2` -/

/-- `b = -X ^ 2 ≤ 0` (A084534). -/
def A084534 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | 2 => 1 + 4 * X + 2 * X ^ 2
  | n + 3 => ((1 + (2 * X))) * A084534 (n + 2) + ((-1 * (X) ^ (2))) * A084534 (n + 1)

theorem A084534_interlaces (n : ℕ) : Interlaces (A084534 n) (A084534 (n + 1)) := by
  rr_row_interlaces
theorem A084534_eval_zero_pos (n : ℕ) : 0 < (A084534 n).eval 0 := by rr_row_eval_zero_pos
theorem A084534_splits (n : ℕ) : (A084534 n).Splits := by rr_row_splits

/-- Rows with nonnegative coefficients and `b = X` (A102413). -/
def A102413 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + X ^ 2
  | n + 3 => ((1 + X)) * A102413 (n + 2) + (X) * A102413 (n + 1)

theorem A102413_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (A102413 n) := by
  rr_row_nonneg_coeffs
theorem A102413_interlaces (n : ℕ) : Interlaces (A102413 n) (A102413 (n + 1)) := by
  rr_row_interlaces
theorem A102413_eval_zero_pos (n : ℕ) : 0 < (A102413 n).eval 0 := by rr_row_eval_zero_pos
theorem A102413_splits (n : ℕ) : (A102413 n).Splits := by rr_row_splits

/-- `b = -(1 + X) ^ 2` (A103450). -/
def A103450 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 3 * X + X ^ 2
  | n + 3 => ((2 + (2 * X))) * A103450 (n + 2) +
      ((-1 + (-1 * (X) ^ (2)) + (-2 * X))) * A103450 (n + 1)

theorem A103450_interlaces (n : ℕ) : Interlaces (A103450 n) (A103450 (n + 1)) := by
  rr_row_interlaces

/-- The certificate printed by `rr_row_interlaces?` for `A103450_interlaces`. -/
example (n : ℕ) : Interlaces (A103450 n) (A103450 (n + 1)) := by
  rcases n with _ | n
  · rr_row_side
  apply RealRooted.threeTerm_interlaces_of_eval_nonpos (P := fun m => A103450 (m + 1)) (D₀ := 1)
    fun _ => rfl <;> rr_row_side

#guard_msgs (drop info) in
example (n : ℕ) : Interlaces (A103450 n) (A103450 (n + 1)) := by rr_row_interlaces?

/-! ### Summands in other orders -/

/-- The recurrence of A008288 with the summands and factors swapped. -/
def swappedLag : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => X * swappedLag n + swappedLag (n + 1) * (1 + X)

theorem swappedLag_interlaces (n : ℕ) : Interlaces (swappedLag n) (swappedLag (n + 1)) := by
  rr_row_interlaces
theorem swappedLag_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (swappedLag n) := by
  rr_row_nonneg_coeffs

/-- The recurrence of A056241 with a subtracted summand. -/
def subtractedLag : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (2 + 2 * X) * subtractedLag (n + 1) - (1 + X + X ^ 2) * subtractedLag n

theorem subtractedLag_interlaces (n : ℕ) :
    Interlaces (subtractedLag n) (subtractedLag (n + 1)) := by
  rr_row_interlaces

/-- The recurrence of A008277 with the derivative summand last. -/
def swappedDeriv : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * swappedDeriv n + X * (swappedDeriv n).derivative

theorem swappedDeriv_interlaces (n : ℕ) :
    Interlaces (swappedDeriv n) (swappedDeriv (n + 1)) := by
  rr_row_interlaces
theorem swappedDeriv_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (swappedDeriv n) := by
  rr_row_nonneg_coeffs
theorem swappedDeriv_eval_zero_pos (n : ℕ) : 0 < (swappedDeriv n).eval 0 := by
  rr_row_eval_zero_pos
theorem swappedDeriv_splits (n : ℕ) : (swappedDeriv n).Splits := by rr_row_splits

/-- A product with the factor on the right. -/
def swappedProduct : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => swappedProduct n * (2 + X)

theorem swappedProduct_interlaces (n : ℕ) :
    Interlaces (swappedProduct n) (swappedProduct (n + 1)) := by
  rr_row_interlaces
theorem swappedProduct_splits (n : ℕ) : (swappedProduct n).Splits := by rr_row_splits
theorem swappedProduct_hasNonnegCoeffs (n : ℕ) : HasNonnegCoeffs (swappedProduct n) := by
  rr_row_nonneg_coeffs
theorem swappedProduct_eval_zero_pos (n : ℕ) : 0 < (swappedProduct n).eval 0 := by
  rr_row_eval_zero_pos

/-- Roots in `(-∞, 0]` while the lag `X - X ^ 2` is positive beyond `1`: the leading
coefficients control the window (`RealRooted.threeTerm_interlaces_of_roots_le_of_ratio`)
(A098158). -/
def A098158 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * A098158 (n + 1) + (X + -1 * X ^ 2) * A098158 n

theorem A098158_interlaces (n : ℕ) : Interlaces (A098158 n) (A098158 (n + 1)) := by
  rr_row_interlaces

/-! ### Products, half growth with a common lag root, derivative lags -/

/-- A derivative-lag recurrence `P (n + 2) = U P (n + 1) + V P' (n + 1) + W P n` with
`V ≤ 0`, `W < 0` on the negative axis (A144436). -/
def A144436 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (C 1 * X + C (-1) * X ^ 2) * (A144436 (n + 1)).derivative +
      (C 1 + C (2 + (n : ℝ)) * X) * A144436 (n + 1) + (C 4 * X) * A144436 n

theorem A144436_splits (n : ℕ) : (A144436 n).Splits := by rr_row_splits

/-- A derivative-lag recurrence with half growth (A008299). -/
def A008299 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => (C 1 * X) * (A008299 (n + 1)).derivative + C 1 * A008299 (n + 1) +
      (C (3 + (n : ℝ)) * X) * A008299 n

theorem A008299_splits (n : ℕ) : (A008299 n).Splits := by rr_row_splits

/-- Half growth whose lags `(n + 1) (X - 1)` share the root `1`
(`RealRooted.eval_mul_eval_nonneg_of_natDegree_le_one`) (A136394). -/
def A136394 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => C (2 + (n : ℝ)) * A136394 (n + 1) + (C (-1 + -1 * (n : ℝ)) + C (1 + (n : ℝ)) * X) *
      A136394 n

theorem A136394_splits (n : ℕ) : (A136394 n).Splits := by rr_row_splits

/-- A product with a real-rooted quadratic factor (A272866). -/
def A272866 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X ^ 2 + 3 * X) * A272866 n

theorem A272866_splits (n : ℕ) : (A272866 n).Splits := by rr_row_splits

/-- A product with a cubic first row (A122431). -/
def A122431 : ℕ → ℝ[X]
  | 0 => 1 + 3 * X + 3 * X ^ 2 + X ^ 3
  | n + 1 => X * A122431 n

theorem A122431_splits (n : ℕ) : (A122431 n).Splits := by rr_row_splits

/-- Half growth whose lag coefficients are quadratic in `n` (A306364). -/
def A306364 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3
  | n + 2 => C (5 + 2 * (n : ℝ)) * A306364 (n + 1) +
      (C (6 + -1 * (3 + (n : ℝ)) ^ 2 + 2 * (n : ℝ)) +
        C (-6 + (3 + (n : ℝ)) ^ 2 + -2 * (n : ℝ)) * X) * A306364 n

theorem A306364_splits (n : ℕ) : (A306364 n).Splits := by rr_row_splits

/-- A two-step product `P (n + 2) = (1 + 2 X) P n` (A188440). -/
def A188440 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => (1 + 2 * X) * A188440 n

theorem A188440_splits (n : ℕ) : (A188440 n).Splits := by rr_row_splits

/-- A two-step product with a double root `q = X ^ 2` (A133080). -/
def A133080 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => X ^ 2 * A133080 n

theorem A133080_splits (n : ℕ) : (A133080 n).Splits := by rr_row_splits

/-- A product read off `P (n + 3) = X * P (n + 2)` (A167194). -/
def A167194 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + X
  | 2 => 1 + 2 * X + X ^ 2
  | n + 3 => X * A167194 (n + 2)

theorem A167194_splits (n : ℕ) : (A167194 n).Splits := by rr_row_splits

/-- Half growth after the zero row `P 0 = 0` (A180047). -/
def A180047 : ℕ → ℝ[X]
  | 0 => 0
  | 1 => X
  | n + 2 => C (2 + (n : ℝ)) * A180047 (n + 1) + (C 1 * X) * A180047 n

theorem A180047_splits (n : ℕ) : (A180047 n).Splits := by rr_row_splits

/-! ### General Euler steps

Second-order recurrences `P (n + 1) = κX² (P n)'' + (κ(a + b + 1)X + vX²) (P n)' +
(κab + (u₀ + s n) X) P n` with no eigen-ODE, through
`RealRooted.EulerBidiagonal.interlaces_of_generalStep_rec`. -/

/-- Central factorial numbers: `κ = a = b = 1`, `v = 0` (A036969). -/
def A036969 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (A036969 n).derivative.derivative + (3 * X) * (A036969 n).derivative +
      (1 + X) * A036969 n

theorem A036969_interlaces (n : ℕ) : Interlaces (A036969 n) (A036969 (n + 1)) := by
  rr_row_interlaces
theorem A036969_splits (n : ℕ) : (A036969 n).Splits := by rr_row_splits

/-- `κ = 4`, `a = b = 1 / 2` (A160562). -/
def A160562 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (4 * X ^ 2) * (A160562 n).derivative.derivative + (8 * X) * (A160562 n).derivative +
      (1 + X) * A160562 n

theorem A160562_splits (n : ℕ) : (A160562 n).Splits := by rr_row_splits

/-- `κ = 2`, `a = 1 / 2`, `b = 1`, `v = -2` and `u n = 1 + 2n` (A166961). -/
def A166961 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 2 * X ^ 2) * (A166961 n).derivative.derivative +
      (C 5 * X + C (-2) * X ^ 2) * (A166961 n).derivative +
      (C 1 + C (1 + 2 * (n : ℝ)) * X) * A166961 n

theorem A166961_interlaces (n : ℕ) : Interlaces (A166961 n) (A166961 (n + 1)) := by
  rr_row_interlaces

#guard_msgs (drop info) in
example (n : ℕ) : Interlaces (A166961 n) (A166961 (n + 1)) := by
  rr_row_interlaces?

/-! ### Hinted calls of `rr_row_splits` -/

/--
info: Try these:
  [apply] rr_row_splits (via := nextRow) (thm := RealRooted.derivRec_interlaces_of_roots_mem_Icc)
        (degree := 0) (drop := 0) (window := [-1, 0])
-/
#guard_msgs in
example (n : ℕ) : (A019538 n).Splits := by
  rr_row_splits?

/--
info: Try these:
  [apply] rr_row_splits (drop := 1) (half := 1)
-/
#guard_msgs in
example (n : ℕ) : (A008299 n).Splits := by
  rr_row_splits?

example (n : ℕ) : (A008299 n).Splits := by rr_row_splits (drop := 1) (half := 1)
example (n : ℕ) : (A180047 n).Splits := by rr_row_splits (via := halfGrowth) (drop := 1)
example (n : ℕ) : (A008292 n).Splits := by rr_row_splits (via := prevRow)
example (n : ℕ) : (A133080 n).Splits := by rr_row_splits (via := twoStep)
example (n : ℕ) : (A167194 n).Splits := by rr_row_splits (via := shiftedProduct)
example (n : ℕ) : (swappedProduct n).Splits := by rr_row_splits (via := linearFactors)
example (n : ℕ) : (swappedProduct n).Splits := by rr_row_splits (via := splitFactors)

/--
error: rr_row_splits: unknown route foo; the routes are closedForm, lowerOrder, subseq,
linearFactors, splitFactors, twoStep, shiftedProduct, nextRow, prevRow, halfGrowth,
degreePattern
-/
#guard_msgs (whitespace := normalized) in
example (n : ℕ) : (A008292 n).Splits := by rr_row_splits (via := foo)

end

end RealRooted.Tactic.RowInterlacingExamples
