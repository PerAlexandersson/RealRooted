import RealRooted.Tactic.RowInterlacing

/-!
# General recurrences and half growth

Regression tests for the fallback of the degree tactics to general linear recurrences
(`RealRooted.LinRec`: any order, mixed derivatives, top coefficients of either sign) and
for `rr_row_splits` / `rr_row_interlaces` on half growth
(`RealRooted.threeTermHalf_ne_zero_and_splits`), dropped rows, degree-bounded root windows,
two-step products, derivative-lag recurrences, residue subsequences, closed forms,
derivative products, order-three recurrences through three-term ones and degrees with
cancelling top terms, on OEIS rows drawn from `real-rooted-oeis-proofs`.
-/

open Polynomial

namespace RealRooted.Tactic.RowGeneralExamples

noncomputable section

/-- An order-three recurrence whose top coefficients satisfy `c = c - 3 c + 3 c`
(A030524). -/
def A030524 : ℕ → ℝ[X]
  | 0 => 30 + 12 * X + X ^ 2
  | 1 => 135 + 96 * X + 18 * X ^ 2 + X ^ 3
  | 2 => 567 + 630 * X + 198 * X ^ 2 + 24 * X ^ 3 + X ^ 4
  | n + 3 => (9 + X) * A030524 (n + 2) + (-27 + -3 * X) * A030524 (n + 1) +
      (27 + 3 * X) * A030524 n

theorem A030524_natDegree (n : ℕ) : (A030524 n).natDegree = n + 2 := by rr_row_natDegree

/-- A second-order recurrence with derivatives of both earlier rows (A307419). -/
def A307419 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (C 1 * X) * (A307419 (n + 1)).derivative +
      (C (-1 + -1 * (n : ℝ)) * X) * (A307419 n).derivative +
      (C (2 + 2 * (n : ℝ)) + C 1 * X) * A307419 (n + 1) +
      C (9 + -1 * (3 + (n : ℝ)) ^ 2 + 5 * (n : ℝ)) * A307419 n

theorem A307419_natDegree (n : ℕ) : (A307419 n).natDegree = n := by rr_row_natDegree

/-- Half growth with a lag `X - 1` of constant sign product (A034839). -/
def A034839 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * A034839 (n + 1) + (-1 + X) * A034839 n

theorem A034839_splits (n : ℕ) : (A034839 n).Splits := by rr_row_splits

/-- Half growth with `n`-dependent coefficients (A008306). -/
def A008306 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2
  | n + 2 => C (3 + (n : ℝ)) * A008306 (n + 1) + (C (3 + (n : ℝ)) * X) * A008306 n

theorem A008306_splits (n : ℕ) : (A008306 n).Splits := by rr_row_splits

/-- The multiplier vanishes at `n = 0`: the first two rows are constant, and the rows
interlace from row `1` on (A055356). -/
def A055356 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X) * (A055356 n).derivative + (C 1 + C (n : ℝ) * X) * A055356 n

theorem A055356_interlaces (n : ℕ) : Interlaces (A055356 (n + 1)) (A055356 (n + 2)) := by
  rr_row_interlaces
theorem A055356_splits (n : ℕ) : (A055356 n).Splits := by rr_row_splits

/-- As above, with `A n = X - X ^ 2` changing sign (A163936). -/
def A163936 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X + C (-1) * X ^ 2) * (A163936 n).derivative +
      (C (1 + (n : ℝ)) + C (n : ℝ) * X) * A163936 n

theorem A163936_splits (n : ℕ) : (A163936 n).Splits := by rr_row_splits

/-- `A n = -X (1 + X)` is negative beyond the root window `(-∞, -1]`; the degree bound
`B (x + 1) + min A 0 * deg > 0` replaces `A ≥ 0` there (A090582). -/
def A090582 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C (-1) * X + C (-1) * X ^ 2) * (A090582 n).derivative +
      (C (2 + (n : ℝ)) + C (1 + (n : ℝ)) * X) * A090582 n

theorem A090582_interlaces (n : ℕ) : Interlaces (A090582 n) (A090582 (n + 1)) := by
  rr_row_interlaces

/-- Two equal-degree rows dropped before linear growth: degree `n - 1` (A271697). -/
def A271697 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 => (C 1 * X + C (-1) * X ^ 2) * (A271697 (n + 1)).derivative +
      (C (1 + (n : ℝ)) * X) * A271697 (n + 1) + (C (1 + (n : ℝ)) * X) * A271697 n

theorem A271697_natDegree (n : ℕ) : (A271697 n).natDegree = n - 1 := by rr_row_natDegree

/-- A negative multiplier with Fibonacci top coefficients, by a ratio invariant (A046741). -/
def A046741 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + 2 * X ^ 2
  | n + 3 => (1 + 2 * X) * A046741 (n + 2) + X * A046741 (n + 1) + (-1 * X ^ 3) * A046741 n

theorem A046741_natDegree (n : ℕ) : (A046741 n).natDegree = n := by rr_row_natDegree
theorem A046741_leadingCoeff_pos (n : ℕ) : 0 < (A046741 n).leadingCoeff := by
  rr_row_leadingCoeff_pos

/-- Top coefficients `n + 1`, with derivatives of both earlier rows (A065826). -/
def A065826 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | n + 2 => (C 1 * X + C (-1) * X ^ 2) * (A065826 (n + 1)).derivative +
      (C (-3 + -1 * (n : ℝ)) * X ^ 2 + C (3 + (n : ℝ)) * X ^ 3) * (A065826 n).derivative +
      (C 1 + C (4 + 2 * (n : ℝ)) * X) * A065826 (n + 1) +
      (C (6 + -1 * (3 + (n : ℝ)) ^ 2 + 2 * (n : ℝ)) * X ^ 2) * A065826 n

theorem A065826_natDegree (n : ℕ) : (A065826 n).natDegree = n := by rr_row_natDegree

/-- Periodic growth: the degree rises every third step (A102547). -/
def A102547 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => 1 * A102547 (n + 2) + X * A102547 n

theorem A102547_natDegree (n : ℕ) : (A102547 n).natDegree = n / 3 := by rr_row_natDegree

/-- Periodic growth with period four and a lag of changing sign (A118884). -/
def A118884 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | n + 4 => 2 * A118884 (n + 3) + (-1 + X) * A118884 n

theorem A118884_natDegree (n : ℕ) : (A118884 n).natDegree = n / 4 := by rr_row_natDegree

/-- Only every other row is new: the even and odd rows are product sequences with the
quadratic factor `1 + 3 X + X ^ 2` (A026386). -/
def A026386 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 2 * X + X ^ 2
  | n + 3 => (1 + X ^ 2 + 3 * X) * A026386 (n + 1)

theorem A026386_splits (n : ℕ) : (A026386 n).Splits := by rr_row_splits

/-- A derivative recurrence of lag two, split along the residues of `n` mod two (A321434). -/
def A321434 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (X + X ^ 2) * (A321434 n).derivative + X * A321434 n

theorem A321434_splits (n : ℕ) : (A321434 n).Splits := by rr_row_splits

/-- A three-term recurrence of lag two whose residue classes interlace (A171608). -/
def A171608 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2
  | 2 => 2 * X
  | 3 => 3 * X
  | n + 4 => (2 * X) * A171608 (n + 2) + (-1 * X ^ 2) * A171608 n

theorem A171608_splits (n : ℕ) : (A171608 n).Splits := by rr_row_splits

/-- Every row is a linear residual times powers of the factors of the recurrence coefficients;
the numeric probe finds the factors and their exponents (A124860). -/
def A124860 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => (1 + X) * A124860 (n + 1) + (2 + 2 * X ^ 2 + 4 * X) * A124860 n

theorem A124860_splits (n : ℕ) : (A124860 n).Splits := by rr_row_splits

/-- Three zero rows before a first-order derivative recurrence: only the rows from `3` on
interlace (A172108). -/
def A172108 : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1 + 3 * X + 3 * X ^ 2 + X ^ 3
  | n + 4 => (X + X ^ 2) * (A172108 (n + 3)).derivative + (1 + 2 * X) * A172108 (n + 3)

theorem A172108_splits (n : ℕ) : (A172108 n).Splits := by rr_row_splits

/-- A product with the derivative, `P (n + 1) = A * (P n)'` (A142071). -/
def A142071 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (X + X ^ 2) * (A142071 (n + 1)).derivative

theorem A142071_splits (n : ℕ) : (A142071 n).Splits := by rr_row_splits

/-- An order-three recurrence that factors through the three-term recurrence
`(n + 2) (n + 4) P (n + 2) = (X + 1) (n + 3) (2 n + 5) P (n + 1) - (X - 1) ^ 2 (n + 2) (n + 3) P n`,
found numerically and certified through its remainder (A132812). -/
def A132812 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2 + 2 * X
  | 2 => 3 + 9 * X + 3 * X ^ 2
  | n + 3 =>
      (C (3 * ((n : ℝ) + 4) / ((n : ℝ) + 5)) + C (3 * ((n : ℝ) + 4) / ((n : ℝ) + 5)) * X) *
        A132812 (n + 2) +
      (C (-(3 * (n : ℝ) + 9) / ((n : ℝ) + 5)) + C (-(2 * (n : ℝ) + 2) / ((n : ℝ) + 5)) * X +
        C (-(3 * (n : ℝ) + 9) / ((n : ℝ) + 5)) * X ^ 2) * A132812 (n + 1) +
      (C (((n : ℝ) + 2) / ((n : ℝ) + 5)) - C (((n : ℝ) + 2) / ((n : ℝ) + 5)) * X -
        C (((n : ℝ) + 2) / ((n : ℝ) + 5)) * X ^ 2 + C (((n : ℝ) + 2) / ((n : ℝ) + 5)) * X ^ 3) *
        A132812 n

theorem A132812_interlaces (n : ℕ) : Interlaces (A132812 n) (A132812 (n + 1)) := by
  rr_row_interlaces
theorem A132812_splits (n : ℕ) : (A132812 n).Splits := by rr_row_splits

/-- The top terms cancel at every step: `X ^ (d + 2)` has coefficient `(n - d) · lc = 0`, and
the degree `n` comes from the next coefficient (A008970). -/
def A008970 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X - X ^ 3) * (A008970 n).derivative + (1 + 2 * X + C (n : ℝ) * X ^ 2) * A008970 n

theorem A008970_natDegree (n : ℕ) : (A008970 n).natDegree = n := by rr_row_natDegree

/-- The top terms cancel at every other step: half growth (A008303). -/
def A008303 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (2 * X - 2 * X ^ 2) * (A008303 n).derivative + (2 + C (n : ℝ) * X) * A008303 n

theorem A008303_natDegree (n : ℕ) : (A008303 n).natDegree = n / 2 := by rr_row_natDegree

end

end RealRooted.Tactic.RowGeneralExamples
