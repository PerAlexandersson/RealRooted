module

public import RealRooted.Tactic.RowInterlacing
public import RealRooted.Tactic.Examples.RowFixtures
public import Mathlib.RingTheory.Polynomial.Chebyshev

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

@[expose] public section

open Polynomial
open RealRooted.Tactic.RowFixtures

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

theorem A118884_natDegree (n : ℕ) : (A118884 n).natDegree = n / 4 := by rr_row_natDegree

/-- Only every other row is new: the even and odd rows are product sequences with the
quadratic factor `1 + 3 X + X ^ 2` (A026386). -/
def A026386 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 2 * X + X ^ 2
  | n + 3 => (1 + X ^ 2 + 3 * X) * A026386 (n + 1)

theorem A026386_splits (n : ℕ) : (A026386 n).Splits := by rr_row_splits
theorem A026386_interlaces (n : ℕ) : Interlaces (A026386 n) (A026386 (n + 1)) := by
  rr_row_interlaces

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

/-- The rows of degree `n / 2` split: from the first row of positive degree on, consecutive
rows strictly interlace
(`RealRooted.derivativeRecurrence_splits_of_degree_pattern_of_nonnegCoeffs`). -/
theorem A008303_splits (n : ℕ) : (A008303 n).Splits := by rr_row_splits

/-- Half growth of a three-term recurrence whose multipliers are rational in `n` (A008556). -/
def A008556 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2
  | n + 2 => C ((1 / (-2 + -1 * (n : ℝ))) * (-6 + -4 * (n : ℝ))) * A008556 (n + 1) +
      (C ((1 / (-2 + -1 * (n : ℝ))) * (-4 + -4 * (n : ℝ))) * X) * A008556 n

theorem A008556_splits (n : ℕ) : (A008556 n).Splits := by rr_row_splits

/-! ### Two-step products with zero rows

Degrees by parity (`RealRooted.twoStepProduct_natDegree`). -/

/-- The odd rows vanish (A003982). -/
def A003982 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 => X * A003982 n

theorem A003982_natDegree (n : ℕ) :
    (A003982 n).natDegree = if n % 2 = 1 then 0 else n / 2 := by
  rr_row_natDegree

/-- Positivity holds on the nonzero (even) rows, despite the zero odd rows. -/
theorem A003982_hasPosLeadingCoeff (n : ℕ) (h : A003982 n ≠ 0) :
    HasPosLeadingCoeff (A003982 n) := by
  rr_row_leadingCoeff_pos

#guard_msgs (drop info) in
example (n : ℕ) (h : A003982 n ≠ 0) : HasPosLeadingCoeff (A003982 n) := by
  rr_row_leadingCoeff_pos? (via := twoStep)

-- A proposition binder is an implication, not a universally quantified row index.
example : A003982 0 ≠ 0 → 0 < (A003982 0).leadingCoeff := by rr_row_side
example : A003982 1 ≠ 0 → 0 < (A003982 1).leadingCoeff := by rr_row_side

/-- A constant factor: the rows alternate between `1` and `1 + X`. -/
def alternatingParityRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => 1 * alternatingParityRows n

/-- A266178 has alternating degrees, but every leading coefficient is positive. -/
theorem alternatingParityRows_hasPosLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (alternatingParityRows n) := by
  rr_row_leadingCoeff_pos

-- Quantification over a finite index type remains a row certificate, not an implication.
example (n : ℕ) : ∀ i : Fin (n + 1), 0 < (alternatingParityRows i).leadingCoeff := by
  rr_row_side

theorem alternatingParityRows_natDegree (n : ℕ) :
    (alternatingParityRows n).natDegree = if n % 2 = 1 then 1 else 0 := by
  rr_row_natDegree

/-! ### Hinted calls of `rr_row_splits` -/

example (n : ℕ) : (A026386 n).Splits := by rr_row_splits (via := closedForm)
example (n : ℕ) : (A321434 n).Splits := by rr_row_splits (via := subseq)
example (n : ℕ) : (A132812 n).Splits := by rr_row_splits (via := lowerOrder)
example (n : ℕ) : (A034839 n).Splits := by rr_row_splits (via := halfGrowth) (drop := 0)

/-- A product tail with two vanishing initial rows (OEIS A185778). -/
def A185778 : ℕ → ℝ[X]
  | 0 => 2 * X
  | 1 => 0
  | 2 => 0
  | 3 => X ^ 2 + X ^ 3
  | n + 4 => (1 + X) * A185778 (n + 3)

/-- Nonzero rows have positive leaders despite the exceptional initial window. -/
theorem A185778_leadingCoeff_pos (n : ℕ) (h : A185778 n ≠ 0) :
    HasPosLeadingCoeff (A185778 n) := by
  rr_row_leadingCoeff_pos

example : True := by
  fail_if_success
    have : HasPosLeadingCoeff (A185778 1) := by rr_row_leadingCoeff_pos
  trivial

/-- An unrelated product tail tests rational base coefficients and negative lower terms. -/
def rationalBaseRows : ℕ → ℝ[X]
  | 0 => C (7 / 3) * X ^ 5 - X ^ 2
  | 1 => X ^ 2 + X ^ 3
  | n + 2 => (1 + X) * rationalBaseRows (n + 1)

example : HasPosLeadingCoeff (rationalBaseRows 0) := by
  rr_row_side

example (n : ℕ) : 0 < (rationalBaseRows n).leadingCoeff := by
  rr_row_leadingCoeff_pos


-- Algebraic closure uses arbitrary polynomials, including negative lower coefficients.
example (p q : ℝ[X]) (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q) :
    HasPosLeadingCoeff (p + q) := by
  rr_row_leadingCoeff_pos (via := algebra)

example (p : ℝ[X]) (hp : HasPosLeadingCoeff p) (a : ℝ) :
    HasPosLeadingCoeff ((X - C a) * p + X * p.derivative) := by
  rr_row_leadingCoeff_pos

-- No nonzero derivative hypothesis: constant p is allowed.
example : HasPosLeadingCoeff ((X - C 7) * 1 + X * (1 : ℝ[X]).derivative) := by
  rr_row_leadingCoeff_pos

example (n : ℕ) (a : ℕ → ℝ) :
    HasPosLeadingCoeff (∏ i ∈ Finset.range n, (X - C (a i))) := by
  rr_row_leadingCoeff_pos

example (n : ℕ) : HasPosLeadingCoeff (rationalBaseRows n +
    X * (rationalBaseRows n).derivative) := by
  rr_row_leadingCoeff_pos

example (p : ℝ[X]) (hp : HasPosLeadingCoeff p) (n : ℕ) :
    HasPosLeadingCoeff (p ^ n) := by
  rr_row_leadingCoeff_pos

example : True := by
  fail_if_success
    have : HasPosLeadingCoeff (0 : ℝ[X]) := by rr_row_leadingCoeff_pos
  fail_if_success
    have : HasPosLeadingCoeff ((-X : ℝ[X]) * X) := by rr_row_leadingCoeff_pos
  trivial


/-- A nonrecursive shift should expose the existing recurrence without a model lookup. -/
def shiftedRationalBaseRows (n : ℕ) : ℝ[X] := rationalBaseRows (n + 2)

example (n : ℕ) : HasPosLeadingCoeff (shiftedRationalBaseRows n) := by
  rr_row_leadingCoeff_pos

example (s : Finset ℕ) (a : ℕ → ℕ)
    (h : (∑ i ∈ s, monomial i (a i : ℝ)) ≠ 0) :
    HasPosLeadingCoeff (∑ i ∈ s, monomial i (a i : ℝ)) := by
  rr_row_leadingCoeff_pos

example : True := by
  fail_if_success
    have : HasPosLeadingCoeff (∑ i ∈ (∅ : Finset ℕ), monomial i (1 : ℝ)) := by
      rr_row_leadingCoeff_pos
  trivial


example (s : Finset ℕ) (a : ℕ → ℕ) :
    0 ≤ (∑ i ∈ s, monomial i (a i : ℝ)).leadingCoeff := by
  rr_row_leadingCoeff_nonneg


/-- The two derivative lags of A219836 need compensation from their own row terms. -/
def pairedDerivativeRows : ℕ → ℝ[X]
  | 0 => 0
  | 1 => X
  | n + 2 => (X - X ^ 2) * (pairedDerivativeRows (n + 1)).derivative +
      (X ^ 2 - X ^ 3) * (pairedDerivativeRows n).derivative +
      (1 + C (1 + (n : ℝ)) * X) * pairedDerivativeRows (n + 1) +
      (X + C (1 + (n : ℝ)) * X ^ 2) * pairedDerivativeRows n

example (n : ℕ) (hn : pairedDerivativeRows n ≠ 0) :
    HasPosLeadingCoeff (pairedDerivativeRows n) := by rr_row_leadingCoeff_pos

#guard_msgs (drop info) in
example (n : ℕ) (hn : pairedDerivativeRows n ≠ 0) :
    HasPosLeadingCoeff (pairedDerivativeRows n) := by
  rr_row_leadingCoeff_pos? (via := coefficients)

example : True := by
  fail_if_success
    have : HasPosLeadingCoeff (pairedDerivativeRows 0) := by
      rr_row_leadingCoeff_pos (via := coefficients)
  trivial

/-- A fixed parameter controls both compensating multipliers. -/
def parametricPairedRows (a : ℝ) : ℕ → ℝ[X]
  | 0 => 0
  | 1 => X
  | n + 2 => (X - X ^ 2) * (parametricPairedRows a (n + 1)).derivative +
      (X ^ 2 - X ^ 3) * (parametricPairedRows a n).derivative +
      (1 + C (a + (n : ℝ)) * X) * parametricPairedRows a (n + 1) +
      (X + C (a + (n : ℝ)) * X ^ 2) * parametricPairedRows a n

example (a : ℝ) (ha : 1 ≤ a) (n : ℕ) (hn : parametricPairedRows a n ≠ 0) :
    HasPosLeadingCoeff (parametricPairedRows a n) := by
  rr_row_leadingCoeff_pos (via := coefficients)


/-- Three lags, a zero initial row, and repeated derivative summands at one lag. -/
def threeLagPairedRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 0
  | n + 3 => X * threeLagPairedRows (n + 2) + X * threeLagPairedRows (n + 1) +
      X ^ 2 * (threeLagPairedRows (n + 1)).derivative +
      (X - X ^ 2) * (threeLagPairedRows (n + 1)).derivative + threeLagPairedRows n

example (n : ℕ) (hn : threeLagPairedRows n ≠ 0) :
    HasPosLeadingCoeff (threeLagPairedRows n) := by
  rr_row_leadingCoeff_pos (via := coefficients)

example : True := by
  fail_if_success
    have : HasPosLeadingCoeff (parametricPairedRows 0 2) := by
      rr_row_leadingCoeff_pos (via := coefficients)
  trivial


-- Nonzero derivatives supply the missing degree condition, including nested derivatives.
example (p : ℝ[X]) (hp : HasPosLeadingCoeff p) (hd : p.derivative ≠ 0) :
    HasPosLeadingCoeff p.derivative := by
  rr_row_leadingCoeff_pos (via := algebra)

example (p : ℝ[X]) (hp : HasPosLeadingCoeff p) (hd : p.derivative.derivative ≠ 0) :
    HasPosLeadingCoeff p.derivative.derivative := by
  rr_row_leadingCoeff_pos

example (n : ℕ) (hd : (rationalBaseRows n).derivative.derivative ≠ 0) :
    HasPosLeadingCoeff (rationalBaseRows n).derivative.derivative := by
  rr_row_leadingCoeff_pos

example : True := by
  fail_if_success
    have : HasPosLeadingCoeff (1 : ℝ[X]).derivative := by rr_row_leadingCoeff_pos
  trivial

#guard_msgs (drop info) in
example (p : ℝ[X]) (hp : HasPosLeadingCoeff p) (hd : p.derivative ≠ 0) :
    HasPosLeadingCoeff p.derivative := by
  rr_row_leadingCoeff_pos? (via := algebra)

-- Replay the certificate printed by the question-mark variant.
example (p : ℝ[X]) (hp : HasPosLeadingCoeff p) (hd : p.derivative ≠ 0) :
    HasPosLeadingCoeff p.derivative := by
  change 0 < (derivative p : Polynomial ℝ).leadingCoeff
  have hd : (p : ℝ[X]).derivative ≠ 0 := by assumption
  have hp : (p : ℝ[X]) ≠ 0 := by
    intro h
    exact hd (by simp [h])
  exact RealRooted.HasPosLeadingCoeff.derivative
    (by rr_row_leadingCoeff_pos) (Polynomial.derivative_ne_zero.mp hd)

/-- A third-order recurrence whose stable degree law begins after two rows (A144090). -/
def A144090 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 2
  | 2 => 3 + 6 * X + 3 * X ^ 2
  | n + 3 =>
      (C (-1) * X ^ 2) * (A144090 (n + 2)).derivative +
        (X ^ 2 - C 2 * X ^ 3) * (A144090 (n + 1)).derivative +
        (C 2 + C (4 + 2 * (n : ℝ)) * X) * A144090 (n + 2) +
        (C (-1) + C (-2 * (n : ℝ)) * X + C (7 + 4 * (n : ℝ)) * X ^ 2) *
          A144090 (n + 1) +
        (C (-2 - (n : ℝ)) * X ^ 2 + C (2 + (n : ℝ)) * X ^ 3) * A144090 n

example (n : ℕ) : HasPosLeadingCoeff (A144090 n) := by rr_row_leadingCoeff_pos

namespace ExplicitLeadingTests

/-- A product recurrence with a signed explicit initial row. -/
def signedRows : ℕ → ℝ[X]
  | 0 => X ^ 2 - X - 1
  | n + 1 => (X - C (n : ℝ)) * signedRows n

example (n : ℕ) : HasPosLeadingCoeff (signedRows n) := by
  rr_row_leadingCoeff_pos


example : HasPosLeadingCoeff (X ^ 2 - X - 1 : ℝ[X]) := by rr_row_leadingCoeff_pos

example : HasPosLeadingCoeff (X ^ 3 - X ^ 3 + X ^ 2 - X - 1 : ℝ[X]) := by
  rr_row_leadingCoeff_pos

example : HasPosLeadingCoeff (C (7 / 3) * X ^ 5 - X ^ 2 : ℝ[X]) := by
  rr_row_leadingCoeff_pos

example (p : ℝ[X]) (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (p * (X ^ 2 - X - 1)) := by rr_row_leadingCoeff_pos

example : 0 ≤ (X ^ 2 - X - 1 : ℝ[X]).leadingCoeff := by rr_row_leadingCoeff_nonneg

example : True := by
  fail_if_success
    have : HasPosLeadingCoeff (X ^ 3 - X ^ 3 : ℝ[X]) := by rr_row_leadingCoeff_pos
  fail_if_success
    have : HasPosLeadingCoeff (-X ^ 2 + X + 1 : ℝ[X]) := by rr_row_leadingCoeff_pos
  trivial

#guard_msgs (drop info) in
example : HasPosLeadingCoeff (X ^ 2 - X - 1 : ℝ[X]) := by
  rr_row_leadingCoeff_pos? (via := algebra)

end ExplicitLeadingTests

namespace GenericCaseTests

/-- Arbitrary real linear factors with an exceptional zero initial row. -/
def pieceRows (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 0
  | n + 1 => (X - C a) * (X + C b) ^ n

theorem pieceRows_pos (a b : ℝ) (n : ℕ) (hn : pieceRows a b n ≠ 0) :
    HasPosLeadingCoeff (pieceRows a b n) := by rr_row_leadingCoeff_pos

/-- A conditional choice of two arbitrary polynomials. -/
def choiceRows (p q : ℝ[X]) (b : Bool) : ℝ[X] := if b then p else q

theorem choiceRows_pos (p q : ℝ[X]) (hp : HasPosLeadingCoeff p)
    (hq : HasPosLeadingCoeff q) (b : Bool) :
    HasPosLeadingCoeff (choiceRows p q b) := by rr_row_leadingCoeff_pos

/-- A piecewise scalar formula with a nonnegative parameter. -/
def pieceCoeff (a : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => a
  | n + 1, k + 1 => a * Nat.choose n k / ((k : ℝ) + 1)

/-- Rows assembled from the piecewise scalar formula. -/
def sumRows (a : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), monomial k (pieceCoeff a n k)

theorem sumRows_pos (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : sumRows a n ≠ 0) :
    HasPosLeadingCoeff (sumRows a n) := by rr_row_leadingCoeff_pos

example : True := by
  fail_if_success
    have : HasPosLeadingCoeff (choiceRows X (-X) false) := by rr_row_leadingCoeff_pos
  fail_if_success
    have : HasPosLeadingCoeff (pieceRows 2 3 0) := by rr_row_leadingCoeff_pos
  trivial

example (p q : ℝ[X]) (hp : 0 ≤ p.leadingCoeff) (hq : 0 ≤ q.leadingCoeff)
    (b : Bool) : 0 ≤ (choiceRows p q b).leadingCoeff := by
  rr_row_leadingCoeff_nonneg

#guard_msgs (drop info) in
example (a b : ℝ) (n : ℕ) (hn : pieceRows a b n ≠ 0) :
    HasPosLeadingCoeff (pieceRows a b n) := by
  rr_row_leadingCoeff_pos? (via := algebra)

#guard_msgs (drop info) in
example (p q : ℝ[X]) (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (b : Bool) : HasPosLeadingCoeff (choiceRows p q b) := by
  rr_row_leadingCoeff_pos? (via := algebra)

end GenericCaseTests

namespace CoefficientClosureTests

/-- A finite-lag differential recurrence used under coefficientwise operations. -/
def rows : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X + 1) * rows n + X * (rows n).derivative

example (n : ℕ) (hn : rows (n + 1) ≠ 0) :
    HasPosLeadingCoeff ((fun k => rows (k + 1)) n) := by
  rr_row_leadingCoeff_pos (via := coefficients)

/-- A coefficient-weighted finite sum with a positive denominator. -/
def weightedRows (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k ((rows n).coeff k * (Nat.choose (n + 1) k : ℝ) / ((k : ℝ) + 1))

example (n : ℕ) (hn : weightedRows n ≠ 0) :
    HasPosLeadingCoeff (weightedRows n) := by
  rr_row_leadingCoeff_pos (via := coefficients)

example (p q : ℝ[X]) (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hn : hadamardProduct p q ≠ 0) : HasPosLeadingCoeff (hadamardProduct p q) := by
  rr_row_leadingCoeff_pos (via := coefficients)

example (n : ℕ) (hn : schurSzegoComp n (rows n) (rows n) ≠ 0) :
    HasPosLeadingCoeff (schurSzegoComp n (rows n) (rows n)) := by
  rr_row_leadingCoeff_pos (via := coefficients)

example (p : ℝ[X]) (hp : HasNonnegCoeffs p) (n : ℕ)
    (hn : hadamardProduct p (rows n) ≠ 0) :
    HasPosLeadingCoeff (hadamardProduct p (rows n)) := by
  rr_row_leadingCoeff_pos

example (n : ℕ) (hn : (rows n).reverse ≠ 0) :
    HasPosLeadingCoeff (rows n).reverse := by
  rr_row_leadingCoeff_pos (via := coefficients)

example (n : ℕ) (hn : (rows n).derivative ≠ 0) :
    HasPosLeadingCoeff (rows n).derivative := by
  rr_row_leadingCoeff_pos (via := coefficients)

#guard_msgs (drop info) in
example (p q : ℝ[X]) (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hn : hadamardProduct p q ≠ 0) : HasPosLeadingCoeff (hadamardProduct p q) := by
  rr_row_leadingCoeff_pos? (via := coefficients)

example : True := by
  fail_if_success
    have : HasPosLeadingCoeff (hadamardProduct X (-X)) := by
      rr_row_leadingCoeff_pos (via := coefficients)
  fail_if_success
    have : HasPosLeadingCoeff (hadamardProduct X 1) := by
      rr_row_leadingCoeff_pos (via := coefficients)
  trivial

/-- A negative constant lag is controlled by ordinary differences. -/
def differenceRows (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (1 + a) + C b * X
  | n + 2 => (2 + C b * X) * differenceRows a b (n + 1) - differenceRows a b n

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    HasNonnegCoeffs (differenceRows a b n) := by
  rr_row_coefficient_closure 16

/-- Polynomial-weighted differences cancel a negative quadratic lag. -/
def polynomialDifferenceRows (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (C (1 + a) * X) * polynomialDifferenceRows a b (n + 1) +
      (C b * X - C a * X ^ 2) * polynomialDifferenceRows a b n

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    HasNonnegCoeffs (polynomialDifferenceRows a b n) := by
  rr_row_coefficient_closure 16

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ)
    (hn : hadamardProduct (rows n) (polynomialDifferenceRows a b n) ≠ 0) :
    HasPosLeadingCoeff (hadamardProduct (rows n) (polynomialDifferenceRows a b n)) := by
  rr_row_leadingCoeff_pos

example (n : ℕ) : HasNonnegCoeffs (differenceRows 2 1 n) := by
  rr_row_coefficient_closure 16

/-- Rational index-dependent multipliers use the same polynomial difference invariant. -/
def rationalDifferenceRows (c b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => (C ((c + 1 + 2 * n) / (c + n)) * X) *
      rationalDifferenceRows c b (n + 1) +
      (C (b * (n + 1) / (c + n)) * X - C ((n + 1) / (c + n)) * X ^ 2) *
        rationalDifferenceRows c b n

example (c b : ℝ) (hc : 0 < c) (hb : 0 ≤ b) (n : ℕ) :
    HasNonnegCoeffs (rationalDifferenceRows c b n) := by
  rr_row_coefficient_closure 16

end CoefficientClosureTests

namespace OperationLeadingTests

-- Imported simp lemmas can discharge leaders without a recurrence-parser extension.
example (n : ℕ) : HasPosLeadingCoeff (Polynomial.Chebyshev.U ℝ (n : ℤ)) := by
  rr_row_leadingCoeff_pos

example (n : ℕ) : HasPosLeadingCoeff (Polynomial.Chebyshev.T ℝ (n : ℤ)) := by
  rr_row_leadingCoeff_pos

example (n : ℕ) : n = n := by
  fail_if_success
    have h : HasPosLeadingCoeff (-Polynomial.Chebyshev.U ℝ (n : ℤ)) := by
      rr_row_leadingCoeff_pos
  rfl

example (a b c : ℝ) (ha : 0 < a) :
    0 < (C a * X ^ 3 - C b * X + C c).leadingCoeff := by
  rr_row_leadingCoeff_pos

example (a b : ℝ) : a = a ∧ b = b := by
  fail_if_success
    have h : 0 < (C (a - b) * X + 1).leadingCoeff := by
      rr_row_leadingCoeff_pos
  exact ⟨rfl, rfl⟩

example (p : ℝ[X]) (hp : p.Monic) : HasPosLeadingCoeff p := by
  rr_row_leadingCoeff_pos

/-- Products with arbitrary moving roots need only a positive initial scalar. -/
def movingRootProducts (a : ℝ) (r : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => C a
  | n + 1 => (X - C (r n)) * movingRootProducts a r n

example (a : ℝ) (r : ℕ → ℝ) (ha : 0 < a) (n : ℕ) :
    HasPosLeadingCoeff (movingRootProducts a r n) := by
  rr_row_leadingCoeff_pos

/-- Natural-number expressions retain their casts in the product certificate. -/
def naturalRootProducts (a : ℝ) (r : ℕ → ℕ) : ℕ → ℝ[X]
  | 0 => C a
  | n + 1 => (X - C (((r n) ^ 2 : ℕ) : ℝ)) * naturalRootProducts a r n

example (a : ℝ) (r : ℕ → ℕ) (ha : 0 < a) (n : ℕ) :
    HasPosLeadingCoeff (naturalRootProducts a r n) := by
  rr_row_leadingCoeff_pos

/-- Index-dependent factor degrees test positivity independently of affine degree laws. -/
def nonlinearDegreeProducts (r : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X ^ (n + 1) - C (r n)) * nonlinearDegreeProducts r n

example (r : ℕ → ℝ) (n : ℕ) :
    HasPosLeadingCoeff (nonlinearDegreeProducts r n) := by
  rr_row_leadingCoeff_pos

example (p q : ℝ[X]) (hp : 0 < p.leadingCoeff) (hq : 0 < q.leadingCoeff)
    (hd : q.natDegree ≠ 0) : 0 < (p.comp q).leadingCoeff := by
  rr_row_leadingCoeff_pos

example (p : ℝ[X]) (hp : 0 < p.leadingCoeff) (a : ℝ) :
    0 < (p.comp (X - C a)).leadingCoeff := by
  rr_row_leadingCoeff_pos

example (p : ℝ[X]) (hp : 0 < p.leadingCoeff) (a b : ℝ) (ha : 0 < a) :
    0 < (p.comp (C a * X - C b)).leadingCoeff := by
  rr_row_leadingCoeff_pos

example (p : ℝ[X]) (hp : HasNonnegCoeffs p) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) (n : ℕ) :
    HasNonnegCoeffs (gammaTransform n (diagonalOperator g p)) := by
  rr_row_coefficient_closure 16

example (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (n : ℕ)
    (hn : gammaTransform n (diagonalOperator g (CoefficientClosureTests.rows n)) ≠ 0) :
    HasPosLeadingCoeff
      (gammaTransform n (diagonalOperator g (CoefficientClosureTests.rows n))) := by
  rr_row_leadingCoeff_pos

end OperationLeadingTests


end

end RealRooted.Tactic.RowGeneralExamples
