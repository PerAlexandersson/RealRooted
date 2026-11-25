module

public import RealRooted.MaWang
import RealRooted.Linear
import RealRooted.NarayanaTransformation.Recurrences.Identities
import RealRooted.NarayanaTransformation.Recurrences.Interlacing
public import RealRooted.CombinatorialExamples.CoefficientHelpers
public import RealRooted.Tactic.WagnerX
public import Mathlib.Tactic
import RealRooted.Tactic.Row.Frontend
import RealRooted.Tactic.Recurrence.Degree
import RealRooted.Tactic.Recurrence.LinRec
import RealRooted.DerivativeRecurrence.RowDegree
import RealRooted.Tactic.WagnerX.Frontend
import RealRooted.NarayanaTransformation.Rectangular.Preservation
public import RealRooted.NarayanaTransformation.Coefficients
import RealRooted.MaWang.Weak.Endpoint
import RealRooted.Mathlib.Data.Nat.Cast.Basic

/-!
# Narayana Polynomials

Liu--Wang/Sturm-sequence package for Narayana polynomials, proved through the
quotient sequence obtained by removing the common `X` factor.  Degree, monicity,
nonnegativity and interlacing are inherited from the generalized Narayana model
`narayanaQuot (n + 1) = narayanaPolynomial 1 n`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The linear coefficient block in the normalized Narayana recurrence. -/
def narayanaCoeffA (n : Nat) : ℝ[X] :=
  C (((2 * n + 3 : ℝ) / (n + 3 : ℝ))) * (1 + X)

/-- The quadratic coefficient block in the normalized Narayana recurrence. -/
def narayanaCoeffB (n : Nat) : ℝ[X] :=
  C ((-(n : ℝ)) / (n + 3 : ℝ)) * (1 - X) ^ 2

/-- The quadratic coefficient block in the Narayana recurrence is
nonpositive on every real input. -/
theorem narayanaCoeffB_eval_nonpos (n : Nat) (r : ℝ) :
    (narayanaCoeffB n).eval r ≤ 0 := by
  have hcoef_nonpos : (((-(n : ℝ)) / (n + 3 : ℝ)) : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by simp) (by positivity)
  have hsquare_nonneg : 0 ≤ (1 - r) ^ 2 := sq_nonneg _
  simpa [narayanaCoeffB, eval_mul, eval_sub, eval_one, eval_X] using
    mul_nonpos_of_nonpos_of_nonneg hcoef_nonpos hsquare_nonneg

/-- The quotient Narayana sequence `Q_n = P_n / X`, defined recursively from

`(n+3) Q_{n+2} = (2n+3) (1 + X) Q_{n+1} - n (1 - X)^2 Q_n`

with `Q_1 = 1`. -/
def narayanaQuot : Nat → ℝ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => narayanaCoeffA n * narayanaQuot (n + 1) + narayanaCoeffB n * narayanaQuot n

/-- The original Narayana sequence `P_n = X * Q_n`. -/
def narayana (n : Nat) : ℝ[X] :=
  X * narayanaQuot n

@[simp] lemma narayanaQuot_zero : narayanaQuot 0 = 0 := rfl

@[simp] lemma narayanaQuot_one : narayanaQuot 1 = 1 := rfl

@[simp] lemma narayanaQuot_succ_succ (n : Nat) :
    narayanaQuot (n + 2) =
      narayanaCoeffA n * narayanaQuot (n + 1) + narayanaCoeffB n * narayanaQuot n := by
  simp [narayanaQuot]

@[simp] lemma narayana_zero : narayana 0 = 0 := by simp [narayana]

@[simp] lemma narayana_one : narayana 1 = X := by simp [narayana]

lemma narayanaQuot_two : narayanaQuot 2 = 1 + X := by
  simp [narayanaQuot, narayanaCoeffA, narayanaCoeffB]

lemma narayana_two : narayana 2 = X + X ^ 2 := by
  rw [narayana, narayanaQuot_two]
  ring

lemma narayana_succ_succ (n : Nat) :
    narayana (n + 2) =
      narayanaCoeffA n * narayana (n + 1) + narayanaCoeffB n * narayana n := by
  rw [narayana, narayana, narayana, narayanaQuot_succ_succ]
  ring

/-- The `m = 1` generalized Narayana polynomials satisfy the normalized
recurrence of the quotient Narayana sequence. -/
theorem narayanaPolynomial_one_succ_succ (n : ℕ) :
    narayanaPolynomial 1 (n + 2) =
      narayanaCoeffA (n + 1) * narayanaPolynomial 1 (n + 1) +
        narayanaCoeffB (n + 1) * narayanaPolynomial 1 n := by
  apply Polynomial.funext
  intro x
  have hrec := congrArg (eval x) (narayanaPolynomial_pure_rec 1 n)
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_one, eval_X, eval_pow] at hrec
  simp only [narayanaCoeffA, narayanaCoeffB, eval_add, eval_mul, eval_C, eval_one,
    eval_X, eval_sub, eval_pow]
  push_cast
  field_simp
  linear_combination hrec

/-- The quotient Narayana sequence is the `m = 1` generalized Narayana
sequence: `Q_{n+1} = sum_k (1 / (n + 1)) C(n+1, k) C(n+1, k+1) X^k`. -/
theorem narayanaQuot_succ_eq_narayanaPolynomial_one (n : ℕ) :
    narayanaQuot (n + 1) = narayanaPolynomial 1 n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => rw [narayanaQuot_two, narayanaPolynomial_one, C_1, add_comm]
  | more n ih ih_succ =>
      change narayanaQuot (n + 1 + 2) = narayanaPolynomial 1 (n + 2)
      rw [narayanaQuot_succ_succ (n + 1), narayanaPolynomial_one_succ_succ n, ih_succ, ih]

lemma natDegree_narayanaQuot (n : Nat) (hn : 1 ≤ n) :
    (narayanaQuot n).natDegree = n - 1 := by
  cases n with
  | zero => lia
  | succ n => rw [narayanaQuot_succ_eq_narayanaPolynomial_one, natDegree_narayanaPolynomial]; rfl

lemma leadingCoeff_narayanaQuot (n : Nat) (hn : 1 ≤ n) :
    (narayanaQuot n).leadingCoeff = 1 := by
  cases n with
  | zero => lia
  | succ n =>
      rw [narayanaQuot_succ_eq_narayanaPolynomial_one, leadingCoeff_narayanaPolynomial]

lemma narayanaQuot_posLeadingCoeff (n : Nat) (hn : 1 ≤ n) :
    HasPosLeadingCoeff (narayanaQuot n) := by rr_row_leadingCoeff_pos

lemma narayanaQuot_ne_zero (n : Nat) (hn : 1 ≤ n) :
    narayanaQuot n ≠ 0 := by rr_row_ne_zero

lemma natDegree_narayana (n : Nat) (hn : 1 ≤ n) :
    (narayana n).natDegree = n := by
  unfold narayana
  have hmul_ne : X.leadingCoeff * (narayanaQuot n).leadingCoeff ≠ 0 := by
    simp [leadingCoeff_narayanaQuot n hn]
  rw [natDegree_mul' hmul_ne, natDegree_X, natDegree_narayanaQuot n hn]
  lia

lemma narayanaQuot_one_two_interlaces :
    Interlaces (narayanaQuot 1) (narayanaQuot 2) := by
  rw [narayanaQuot_one, narayanaQuot_two]
  simpa [add_comm] using
    interlaces_one_linear (p := X + C (1 : ℝ))
      (Polynomial.natDegree_X_add_C (x := (1 : ℝ)))

/-- The quotient Narayana sequence has nonnegative coefficients, via the
coefficient model. -/
theorem narayanaQuot_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (narayanaQuot n) := by
  cases n with
  | zero => simp [HasNonnegCoeffs]
  | succ n =>
      rw [narayanaQuot_succ_eq_narayanaPolynomial_one]
      exact hasNonnegCoeffs_narayanaPolynomial 1 n

/-- Oriented interlacing for the quotient Narayana sequence, inherited from
consecutive generalized Narayana polynomials. -/
theorem strictInterl_narayanaQuot_succ (n : ℕ) (hn : n ≠ 0) :
    StrictInterl (narayanaQuot n) (narayanaQuot (n + 1)) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
      rw [narayanaQuot_succ_eq_narayanaPolynomial_one,
        narayanaQuot_succ_eq_narayanaPolynomial_one]
      cases n with
      | zero =>
          simpa only [Nat.zero_add, narayanaPolynomial_zero_right, narayanaPolynomial_one] using
            (interlaces_one_linear (p := X + C (1 : ℝ)) (by simp)).toStrictInterl
      | succ n => exact strictInterl_narayanaPolynomial_succ 1 n

theorem interlaces_narayanaQuot_succ (n : ℕ) (hn : n ≠ 0) :
    Interlaces (narayanaQuot n) (narayanaQuot (n + 1)) :=
  (strictInterl_narayanaQuot_succ n hn).toInterlaces <| by
    rw [natDegree_narayanaQuot (n + 1) (by lia), natDegree_narayanaQuot n (by lia)]
    lia

/-- Real-rootedness of the quotient Narayana sequence. -/
theorem isRealRooted_narayanaQuot (n : ℕ) (hn : n ≠ 0) :
    narayanaQuot n ≠ 0 ∧ (narayanaQuot n).Splits :=
  (strictInterl_narayanaQuot_succ n hn).1

/-- Interlacing for the original Narayana sequence. This is the quotient
result with the common `X` factor reattached on both sides. -/
theorem interlaces_narayana_succ (n : ℕ) (hn : n ≠ 0) :
    Interlaces (narayana n) (narayana (n + 1)) := by
  have hstrictInterl : StrictInterl (narayana n) (narayana (n + 1)) := by
    unfold narayana
    rr_strict_interl_mul_X_both using proper := strictInterl_narayanaQuot_succ n hn
  exact hstrictInterl.toInterlaces (by
    rw [natDegree_narayana (n + 1) (by lia), natDegree_narayana n (by lia)])

/-- Real-rootedness of the original Narayana sequence. -/
theorem isRealRooted_narayana (n : ℕ) (hn : n ≠ 0) :
    narayana n ≠ 0 ∧ (narayana n).Splits :=
  (interlaces_narayana_succ n hn).2.1

/-- The descending prefix `[P_{n+1}, P_n, ..., P_1]` of the original Narayana
sequence. -/
def narayanaPrefix : Nat → List ℝ[X]
  | 0 => [narayana 1]
  | n + 1 => narayana (n + 2) :: narayanaPrefix n

@[simp] lemma narayanaPrefix_zero : narayanaPrefix 0 = [narayana 1] := rfl

@[simp] lemma narayanaPrefix_succ (n : Nat) :
    narayanaPrefix (n + 1) = narayana (n + 2) :: narayanaPrefix n := rfl

/-- Sturm-sequence package for the original Narayana polynomials. -/
theorem isSturmSeq_narayanaPrefix (n : Nat) : IsSturmSeq (narayanaPrefix n) := by
  induction n with
  | zero =>
      simp [narayanaPrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [narayanaPrefix, IsSturmSeq] using interlaces_narayana_succ 1 (by lia)
      | succ n =>
          simpa [narayanaPrefix, IsSturmSeq] using
            And.intro (interlaces_narayana_succ (n + 2) (by lia)) ih

end RealRooted
