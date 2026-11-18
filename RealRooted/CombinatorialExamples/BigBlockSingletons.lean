module

public import RealRooted.DerivativeRecurrence.EulerLag
public import RealRooted.MultiplierSequence
import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.MultiplierSequence.ProperPosition

/-!
# Singleton-or-large block polynomials

We define the ordered-large-block rows by the insertion recurrence, with the
constant row `1` below the threshold. Dividing coefficient `r` by `r!` gives
the unordered rows. For every threshold at least two, both families are PF
and consecutive rows interlace in the oriented sense.

These are the recurrence-defined families from *Big blocks in set partitions*,
Section "The singleton layer", Theorem `thm:singletonLargeMain`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.BigBlockSingletons

/-- The ordered-large-block lift, specified by its insertion recurrence.
The threshold-zero convention is the constant sequence `1`. -/
def orderedRow (k : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      if h : k ≠ 0 ∧ k ≤ n + 1 then
        thetaPlusOne (orderedRow k n) +
          C ((n.choose (k - 1) : ℕ) : ℝ) * X * thetaPlusOne (orderedRow k (n + 1 - k))
      else 1
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_self _
  · exact Nat.sub_lt (by positivity) (Nat.pos_of_ne_zero h.1)

/-- The unordered row, obtained by dividing coefficient `r` by `r!`. -/
def row (k n : ℕ) : ℝ[X] :=
  diagonalOperator (fun r ↦ (r.factorial : ℝ)⁻¹) (orderedRow k n)

/-- The empty ground set has one ordered partition. -/
@[simp] theorem orderedRow_zero (k : ℕ) : orderedRow k 0 = 1 := by
  rw [orderedRow]

/-- Before the first large block can occur, the only partition consists of singletons. -/
theorem orderedRow_eq_one_of_lt {k n : ℕ} (hn : n < k) : orderedRow k n = 1 := by
  cases n with
  | zero => exact orderedRow_zero k
  | succ n =>
    rw [orderedRow]
    split_ifs with h
    · exact False.elim ((not_le_of_gt hn) h.2)
    · rfl

/-- The ordered insertion recurrence at and above the threshold. -/
theorem orderedRow_add (k q : ℕ) (hk : k ≠ 0) :
    orderedRow k (q + k) = thetaPlusOne (orderedRow k (q + k - 1)) +
      C (((q + k - 1).choose (k - 1) : ℕ) : ℝ) * X * thetaPlusOne (orderedRow k q) := by
  obtain ⟨n, hn⟩ : ∃ n, q + k = n + 1 := ⟨q + k - 1, by lia⟩
  rw [hn, orderedRow]
  split_ifs with h
  · simp only [Nat.add_sub_cancel, show n + 1 - k = q by lia]
  · exact False.elim (h ⟨hk, by lia⟩)

/-- Binomial insertion weights are positive throughout the recurrence. -/
theorem weight_pos (k q : ℕ) :
    0 < (((q + k - 1).choose (k - 1) : ℕ) : ℝ) := by
  exact_mod_cast Nat.choose_pos (show k - 1 ≤ q + k - 1 by lia)

/-- The ordered singleton-or-large rows satisfy the general Euler-lag interface. -/
theorem orderedRow_eulerLagRows {k : ℕ} (hk : 2 ≤ k) :
    EulerLagRows (orderedRow k) k
      (fun q ↦ (((q + k - 1).choose (k - 1) : ℕ) : ℝ)) := by
  exact ⟨hk, fun _ hn ↦ orderedRow_eq_one_of_lt hn,
    fun q ↦ orderedRow_add k q (by lia), weight_pos k⟩

/-- Every ordered singleton-or-large row is a PF polynomial. -/
theorem orderedRow_isPFPolynomial {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    IsPFPolynomial (orderedRow k n) :=
  (orderedRow_eulerLagRows hk).isPFPolynomial n

/-- Every ordered row is nonzero and splits over the reals. -/
theorem orderedRow_ne_zero_and_splits {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    orderedRow k n ≠ 0 ∧ (orderedRow k n).Splits :=
  (orderedRow_eulerLagRows hk).ne_zero_and_splits n

/-- Consecutive ordered rows interlace in the manuscript's direction. -/
theorem orderedRow_strictInterl_succ {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    StrictInterl (orderedRow k n) (orderedRow k (n + 1)) :=
  (orderedRow_eulerLagRows hk).strictInterl_add_of_lt n (by lia)

/-- Every unordered singleton-or-large row is a PF polynomial. -/
theorem row_isPFPolynomial {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : IsPFPolynomial (row k n) :=
  isPFMultiplierSequence_inv_factorial.diagonalOperator_isPF (orderedRow_isPFPolynomial hk n)

/-- Consecutive unordered rows interlace in the manuscript's direction. -/
theorem row_strictInterl_succ {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    StrictInterl (row k n) (row k (n + 1)) := by
  exact isMultiplierSequence_inv_factorial.strictInterl_diagonalOperator_of_pos
    (fun r ↦ by positivity) (orderedRow_strictInterl_succ hk n)

/-- Every unordered row is nonzero and splits over the reals. -/
theorem row_ne_zero_and_splits {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    row k n ≠ 0 ∧ (row k n).Splits :=
  (row_strictInterl_succ hk n).1

/-- Coefficient `r` of the unordered row is coefficient `r` of the ordered row divided by `r!`. -/
theorem coeff_row (k n r : ℕ) :
    (row k n).coeff r = (orderedRow k n).coeff r / (r.factorial : ℝ) := by
  simp [row, div_eq_mul_inv, mul_comm]

/-- Ordering the `r` large blocks multiplies coefficient `r` by `r!`. -/
theorem coeff_orderedRow (k n r : ℕ) :
    (orderedRow k n).coeff r = (r.factorial : ℝ) * (row k n).coeff r := by
  rw [coeff_row]
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The ordered coefficient insertion recurrence, with `r + 1` ordered large blocks. -/
theorem coeff_orderedRow_add_succ (k q r : ℕ) (hk : k ≠ 0) :
    (orderedRow k (q + k)).coeff (r + 1) =
      ((r : ℝ) + 2) * (orderedRow k (q + k - 1)).coeff (r + 1) +
        (((q + k - 1).choose (k - 1) : ℕ) : ℝ) *
          ((r : ℝ) + 1) * (orderedRow k q).coeff r := by
  rw [orderedRow_add k q hk, coeff_add, mul_assoc (C _) X, coeff_C_mul,
    coeff_X_mul, coeff_thetaPlusOne, coeff_thetaPlusOne]
  push_cast
  ring

/-- The unordered coefficient insertion recurrence. A newly formed large block
contributes once, while insertion into an existing block contributes `r + 1` times. -/
theorem coeff_row_add_succ (k q r : ℕ) (hk : k ≠ 0) :
    (row k (q + k)).coeff (r + 1) =
      ((r : ℝ) + 2) * (row k (q + k - 1)).coeff (r + 1) +
        (((q + k - 1).choose (k - 1) : ℕ) : ℝ) * (row k q).coeff r := by
  rw [coeff_row, coeff_orderedRow_add_succ k q r hk, coeff_row, coeff_row]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  have hs : (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The all-singleton partition gives constant coefficient one in every ordered row. -/
@[simp] theorem coeff_orderedRow_zero (k n : ℕ) : (orderedRow k n).coeff 0 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [orderedRow]
      split_ifs with h
      · simp [ih n (by lia)]
      · simp

/-- The all-singleton partition gives constant coefficient one in every unordered row. -/
@[simp] theorem coeff_row_zero (k n : ℕ) : (row k n).coeff 0 = 1 := by
  simp [coeff_row]

/-- The unordered insertion recurrence follows from the ordered recurrence and factorial
normalization. This states the polynomial identity for every positive threshold. -/
theorem row_add (k q : ℕ) (hk : k ≠ 0) :
    row k (q + k) = thetaPlusOne (row k (q + k - 1)) +
      C (((q + k - 1).choose (k - 1) : ℕ) : ℝ) * X * row k q := by
  ext r
  cases r with
  | zero => simp
  | succ r =>
    rw [coeff_add, mul_assoc (C _) X, coeff_C_mul, coeff_X_mul,
      coeff_thetaPlusOne, coeff_row_add_succ k q r hk]
    push_cast
    ring

/-- Both singleton-or-large families are PF, and their consecutive rows interlace. -/
theorem rows {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    IsPFPolynomial (orderedRow k n) ∧ IsPFPolynomial (row k n) ∧
      StrictInterl (orderedRow k n) (orderedRow k (n + 1)) ∧
      StrictInterl (row k n) (row k (n + 1)) :=
  ⟨orderedRow_isPFPolynomial hk n, row_isPFPolynomial hk n,
    orderedRow_strictInterl_succ hk n, row_strictInterl_succ hk n⟩

end RealRooted.BigBlockSingletons
