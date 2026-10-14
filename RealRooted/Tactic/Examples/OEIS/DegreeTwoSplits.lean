import RealRooted.Tactic.RowInterlacing
import RealRooted.PoweredEulerian
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness

/-!
# Degree-jump-two regression examples

These examples exercise the differentiated-`X` route and the powered Eulerian model.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.Tactic.DegreeTwoExamples

/-- The recurrence from A094262. -/
def derivativeXMulRow : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (X + X ^ 3 + 2 * X ^ 2) * (derivativeXMulRow n).derivative +
      (1 + X ^ 2 + 2 * X) * derivativeXMulRow n

/-- The differentiated-`X` route closes the A094262 recurrence. -/
theorem derivativeXMulRow_splits (n : ℕ) : (derivativeXMulRow n).Splits := by
  rr_row_splits

/-- The recurrence from A101842. -/
def firstPoweredEulerianRow : ℕ → ℝ[X]
  | 0 => 1 + X
  | n + 1 => (C 1 * X + C (-1) * X ^ 3) *
      (firstPoweredEulerianRow n).derivative +
        (C 1 + C 1 * X + C (2 + 2 * (n : ℝ)) * X ^ 2) *
          firstPoweredEulerianRow n

/-- The first Eulerian-lift recurrence equals `poweredEulerian 1`. -/
theorem firstPoweredEulerianRow_eq (n : ℕ) :
    firstPoweredEulerianRow n = RealRooted.poweredEulerian 1 n := by
  induction n with
  | zero =>
      simp [firstPoweredEulerianRow, RealRooted.poweredEulerian,
        RealRooted.generalizedEulerian]
  | succ n ih =>
      rw [firstPoweredEulerianRow, ih, RealRooted.poweredEulerian_succ]
      push_cast
      norm_num [Polynomial.C_ofNat]
      ring

/-- The A101842 recurrence is split in every row. -/
theorem firstPoweredEulerianRow_splits (n : ℕ) : (firstPoweredEulerianRow n).Splits := by
  rw [firstPoweredEulerianRow_eq]
  exact RealRooted.poweredEulerian_splits 1 n

/-- Split-row transfer for the A101842 derivative presentation. -/
@[rr_row_model]
theorem firstPoweredEulerianRow_splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1 + X)
    (_hone : P 1 = 1 + 3 * X + 3 * X ^ 2 + X ^ 3)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (C 1 * X + C (-1) * X ^ 3) * (P n).derivative +
        (C 1 + C 1 * X + C (2 + 2 * (n : ℝ)) * X ^ 2) * P n)
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_one_recurrence
    (fun n p => (C 1 * X + C (-1) * X ^ 3) * p.derivative +
      (C 1 + C 1 * X + C (2 + 2 * (n : ℝ)) * X ^ 2) * p)
    (hzero.trans (show (1 + X : ℝ[X]) = firstPoweredEulerianRow 0 by rfl))
    hrec (fun _ => rfl)
  rw [heq n]
  exact firstPoweredEulerianRow_splits n

/-- The recurrence from A165891. -/
def secondPoweredEulerianRow : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (C 1 * X + C (-1) * X ^ 3) *
      (secondPoweredEulerianRow n).derivative +
        (C 1 + C 2 * X + C (1 + 2 * (n : ℝ)) * X ^ 2) *
          secondPoweredEulerianRow n

/-- The second Eulerian-lift recurrence equals `poweredEulerian 0`. -/
theorem secondPoweredEulerianRow_eq (n : ℕ) :
    secondPoweredEulerianRow n = RealRooted.poweredEulerian 0 n := by
  induction n with
  | zero =>
      simp [secondPoweredEulerianRow, RealRooted.poweredEulerian,
        RealRooted.generalizedEulerian]
  | succ n ih =>
      rw [secondPoweredEulerianRow, ih, RealRooted.poweredEulerian_succ]
      push_cast
      norm_num [Polynomial.C_ofNat]
      ring

/-- The A165891 recurrence is split in every row. -/
theorem secondPoweredEulerianRow_splits (n : ℕ) : (secondPoweredEulerianRow n).Splits := by
  rw [secondPoweredEulerianRow_eq]
  exact RealRooted.poweredEulerian_splits 0 n

/-- Split-row transfer for the A165891 derivative presentation. -/
@[rr_row_model]
theorem secondPoweredEulerianRow_splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (_hone : P 1 = 1 + 2 * X + X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (C 1 * X + C (-1) * X ^ 3) * (P n).derivative +
        (C 1 + C 2 * X + C (1 + 2 * (n : ℝ)) * X ^ 2) * P n)
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_one_recurrence
    (fun n p => (C 1 * X + C (-1) * X ^ 3) * p.derivative +
      (C 1 + C 2 * X + C (1 + 2 * (n : ℝ)) * X ^ 2) * p)
    (hzero.trans (show (1 : ℝ[X]) = secondPoweredEulerianRow 0 by rfl))
    hrec (fun _ => rfl)
  rw [heq n]
  exact secondPoweredEulerianRow_splits n

/-- The differential step used by the alternating monomial family. -/
def alternatingMonomialStep (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (C 1 * X ^ 2 + C 2 * X ^ 3) * p.derivative +
    (C (1 - 2 * (n : ℝ)) * X + C (1 - 4 * (n : ℝ)) * X ^ 2) * p

/-- The two-step monomial model for the recurrence from A266326. -/
def alternatingMonomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X + X ^ 2
  | n + 2 => X ^ 4 * alternatingMonomial n

private theorem alternatingMonomial_add_two (n : ℕ) :
    alternatingMonomial (n + 2) = X ^ 4 * alternatingMonomial n := by
  rfl

private theorem alternatingMonomialStep_mul_X_pow_four (n : ℕ) (p : ℝ[X]) :
    alternatingMonomialStep (n + 2) (X ^ 4 * p) =
      X ^ 4 * alternatingMonomialStep n p := by
  simp only [alternatingMonomialStep, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X, mul_one]
  push_cast
  norm_num [Polynomial.C_ofNat]
  ring

private theorem alternatingMonomial_succ (n : ℕ) :
    alternatingMonomial (n + 1) = alternatingMonomialStep n (alternatingMonomial n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [alternatingMonomial, alternatingMonomialStep]
  | one =>
      simp only [alternatingMonomial, alternatingMonomialStep,
        Polynomial.derivative_add, Polynomial.derivative_X,
        Polynomial.derivative_pow, mul_one]
      norm_num [Polynomial.C_ofNat]
      ring
  | more n ih _ =>
      rw [show n + 2 + 1 = (n + 1) + 2 by lia]
      rw [alternatingMonomial_add_two, ih]
      rw [← alternatingMonomialStep_mul_X_pow_four]
      rw [← alternatingMonomial_add_two]

private theorem alternatingMonomial_splits (n : ℕ) :
    (alternatingMonomial n).Splits := by
  induction n using Nat.twoStepInduction with
  | zero => simp [alternatingMonomial]
  | one =>
      rw [alternatingMonomial]
      rw [show (X : ℝ[X]) + X ^ 2 = X * (X + C 1) by
        norm_num [Polynomial.C_ofNat]
        ring]
      exact Polynomial.Splits.X.mul (Polynomial.Splits.X_add_C (1 : ℝ))
  | more n ih _ =>
      rw [alternatingMonomial_add_two]
      exact (Polynomial.Splits.X_pow 4).mul ih

/-- The recurrence from A266326. -/
def alternatingMonomialRow : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => alternatingMonomialStep n (alternatingMonomialRow n)

/-- The A266326 recurrence equals the alternating two-step monomial model. -/
theorem alternatingMonomialRow_eq (n : ℕ) :
    alternatingMonomialRow n = alternatingMonomial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [alternatingMonomialRow, alternatingMonomial_succ, ih]

/-- The A266326 recurrence is split in every row. -/
theorem alternatingMonomialRow_splits (n : ℕ) : (alternatingMonomialRow n).Splits := by
  rw [alternatingMonomialRow_eq]
  exact alternatingMonomial_splits n

/-- Split-row transfer for the A266326 derivative presentation. -/
@[rr_row_model]
theorem alternatingMonomialRow_splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (_hone : P 1 = X + X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (C 1 * X ^ 2 + C 2 * X ^ 3) * (P n).derivative +
        (C (1 - 2 * (n : ℝ)) * X + C (1 - 4 * (n : ℝ)) * X ^ 2) * P n)
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_one_recurrence alternatingMonomialStep
    (hzero.trans (show (1 : ℝ[X]) = alternatingMonomialRow 0 by rfl))
    hrec (fun _ => rfl)
  rw [heq n]
  exact alternatingMonomialRow_splits n

/-- Product of the consecutive linear factors `X + 1, ..., X + m`. -/
def consecutiveLinearProduct (m : ℕ) : ℝ[X] :=
  (Finset.range m).prod fun k => X + C ((k + 1 : ℕ) : ℝ)

private theorem consecutiveLinearProduct_add_two (m : ℕ) :
    consecutiveLinearProduct (m + 2) =
      consecutiveLinearProduct m * (X + C ((m + 1 : ℕ) : ℝ)) *
        (X + C ((m + 2 : ℕ) : ℝ)) := by
  simp only [consecutiveLinearProduct, show m + 2 = (m + 1) + 1 by lia,
    Finset.prod_range_succ]

/-- The product model `(X + n) ∏_{k=1}^{2n} (X + k)`. -/
def centeredConsecutiveProduct (n : ℕ) : ℝ[X] :=
  (X + C (n : ℝ)) * consecutiveLinearProduct (2 * n)

/-- The first multiplier in the three-term recurrence for `centeredConsecutiveProduct`. -/
def centeredConsecutiveFirst (n : ℕ) : ℝ[X] :=
  C (-12 - 6 * (n : ℝ) + 4 * (3 + (n : ℝ)) ^ 2) +
    C (4 + 3 * (n : ℝ)) * X + X ^ 2

/-- The second multiplier in the three-term recurrence for `centeredConsecutiveProduct`. -/
def centeredConsecutiveSecond (n : ℕ) : ℝ[X] :=
  C (68 - 8 * (3 + (n : ℝ)) ^ 2 + 36 * (n : ℝ)) +
    C (20 - 14 * (3 + (n : ℝ)) ^ 2 - 6 * (n : ℝ) +
      4 * (3 + (n : ℝ)) ^ 3) * X +
    C (-26 - 5 * (n : ℝ) + 4 * (3 + (n : ℝ)) ^ 2) * X ^ 2 +
    C (4 + (n : ℝ)) * X ^ 3

private theorem centeredConsecutiveProduct_rec (n : ℕ) :
    centeredConsecutiveProduct (n + 2) =
      centeredConsecutiveFirst n * centeredConsecutiveProduct (n + 1) +
        centeredConsecutiveSecond n * centeredConsecutiveProduct n := by
  rw [centeredConsecutiveProduct, centeredConsecutiveProduct, centeredConsecutiveProduct]
  rw [show 2 * (n + 2) = (2 * n + 2) + 2 by lia,
    consecutiveLinearProduct_add_two]
  rw [consecutiveLinearProduct_add_two]
  rw [show 2 * (n + 1) = 2 * n + 2 by lia, consecutiveLinearProduct_add_two]
  simp only [centeredConsecutiveFirst, centeredConsecutiveSecond]
  push_cast
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat]
  ring

private theorem centeredConsecutiveProduct_splits (n : ℕ) :
    (centeredConsecutiveProduct n).Splits := by
  unfold centeredConsecutiveProduct consecutiveLinearProduct
  exact (Polynomial.Splits.X_add_C (n : ℝ)).mul
    (Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_add_C ((k + 1 : ℕ) : ℝ))

/-- The recurrence from A268647. -/
def centeredConsecutiveProductRow : ℕ → ℝ[X]
  | 0 => X
  | 1 => 2 + 5 * X + 4 * X ^ 2 + X ^ 3
  | n + 2 => centeredConsecutiveFirst n * centeredConsecutiveProductRow (n + 1) +
      centeredConsecutiveSecond n * centeredConsecutiveProductRow n

/-- The A268647 recurrence equals the consecutive-linear-factor product. -/
theorem centeredConsecutiveProductRow_eq (n : ℕ) :
    centeredConsecutiveProductRow n = centeredConsecutiveProduct n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [centeredConsecutiveProductRow, centeredConsecutiveProduct,
      consecutiveLinearProduct]
  | one =>
      simp only [centeredConsecutiveProductRow, centeredConsecutiveProduct,
        consecutiveLinearProduct, Finset.prod_range_succ, Finset.prod_range_zero]
      norm_num [Polynomial.C_ofNat]
      ring
  | more n ih ih_succ =>
      rw [centeredConsecutiveProductRow, ih, ih_succ, centeredConsecutiveProduct_rec]

/-- The A268647 recurrence is split in every row. -/
theorem centeredConsecutiveProductRow_splits (n : ℕ) :
    (centeredConsecutiveProductRow n).Splits := by
  rw [centeredConsecutiveProductRow_eq]
  exact centeredConsecutiveProduct_splits n

/-- Split-row transfer for the lag-two A268647 presentation. -/
@[rr_row_model]
theorem centeredConsecutiveProductRow_splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = X)
    (hone : P 1 = 2 + 5 * X + 4 * X ^ 2 + X ^ 3)
    (hrec : ∀ n : ℕ,
      P (n + 2) =
        (C (-12 + -6 * (n : ℝ) + 4 * (3 + (n : ℝ)) ^ 2) +
          C (4 + 3 * (n : ℝ)) * X + C 1 * X ^ 2) * P (n + 1) +
        (C (68 + -8 * (3 + (n : ℝ)) ^ 2 + 36 * (n : ℝ)) +
          C (20 + -14 * (3 + (n : ℝ)) ^ 2 + -6 * (n : ℝ) +
            4 * (3 + (n : ℝ)) ^ 3) * X +
          C (-26 + -5 * (n : ℝ) + 4 * (3 + (n : ℝ)) ^ 2) * X ^ 2 +
          C (4 + (n : ℝ)) * X ^ 3) * P n)
    (n : ℕ) :
    (P n).Splits := by
  let update : ℕ → ℝ[X] → ℝ[X] → ℝ[X] := fun n p q =>
    (C (-12 + -6 * (n : ℝ) + 4 * (3 + (n : ℝ)) ^ 2) +
        C (4 + 3 * (n : ℝ)) * X + C 1 * X ^ 2) * p +
      (C (68 + -8 * (3 + (n : ℝ)) ^ 2 + 36 * (n : ℝ)) +
        C (20 + -14 * (3 + (n : ℝ)) ^ 2 + -6 * (n : ℝ) +
          4 * (3 + (n : ℝ)) ^ 3) * X +
        C (-26 + -5 * (n : ℝ) + 4 * (3 + (n : ℝ)) ^ 2) * X ^ 2 +
        C (4 + (n : ℝ)) * X ^ 3) * q
  have heq := sequence_eq_of_same_lag_two_recurrence update
    (hzero.trans (show X = centeredConsecutiveProductRow 0 by rfl))
    (hone.trans
      (show (2 + 5 * X + 4 * X ^ 2 + X ^ 3 : ℝ[X]) =
        centeredConsecutiveProductRow 1 by rfl))
    hrec (fun m => by
      simp only [update, map_one]
      rw [centeredConsecutiveProductRow]
      unfold centeredConsecutiveFirst centeredConsecutiveSecond
      ring)
  rw [heq n]
  exact centeredConsecutiveProductRow_splits n

/-- A recurrence deliberately rejected by the differentiated-`X` probe. -/
def nonmatchingRow : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (nonmatchingRow n).derivative + nonmatchingRow n

example : True := by
  have : (nonmatchingRow 2).Splits := by
    fail_if_success rr_row_derivative_X_mul_splits
    simp [nonmatchingRow]
  trivial

end RealRooted.Tactic.DegreeTwoExamples
