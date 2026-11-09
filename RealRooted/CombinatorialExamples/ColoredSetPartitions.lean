module

import RealRooted.Tactic.RowInterlacing
public import RealRooted.CombinatorialExamples.Common
public import RealRooted.MaWang
public import Mathlib.Tactic
import RealRooted.MaWang.Weak.Endpoint
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.Algebra
import RealRooted.Linear
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Colored Set-Partition Polynomials

Real-rootedness and Sturm-sequence facts for the colored set-partition
recurrence, including the type `B` specialization.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The linear coefficient block in the colored set-partition recurrence. -/
def coloredSetPartitionsCoeffA (c : Nat) : ℝ[X] :=
  X + C (c : ℝ)

/-- The derivative coefficient block in the colored set-partition recurrence. -/
def coloredSetPartitionsCoeffB (m : Nat) : ℝ[X] :=
  C (m : ℝ) * X

/-- The generic colored set-partition family satisfying
`T_{n+1}(X) = (X + c) T_n(X) + m X T'_n(X)` with `T_0(X) = 1`. -/
def coloredSetPartitions (c m : Nat) : Nat → ℝ[X]
  | 0 => 1
  | n + 1 =>
      coloredSetPartitionsCoeffA c * coloredSetPartitions c m n +
        coloredSetPartitionsCoeffB m * (coloredSetPartitions c m n).derivative

@[simp] lemma coloredSetPartitions_zero (c m : Nat) :
    coloredSetPartitions c m 0 = 1 := rfl

lemma coloredSetPartitions_succ (c m n : Nat) :
    coloredSetPartitions c m (n + 1) =
      coloredSetPartitionsCoeffA c * coloredSetPartitions c m n +
        coloredSetPartitionsCoeffB m * (coloredSetPartitions c m n).derivative := rfl

lemma coloredSetPartitions_one (c m : Nat) :
    coloredSetPartitions c m 1 = X + C (c : ℝ) := by
  simp [coloredSetPartitions, coloredSetPartitionsCoeffA, coloredSetPartitionsCoeffB]

lemma coeff_coloredSetPartitionsCoeffA_mul (c k : Nat) (p : ℝ[X]) :
    coeff (coloredSetPartitionsCoeffA c * p) (k + 1) =
      coeff p k + (c : ℝ) * coeff p (k + 1) := by
  rw [coloredSetPartitionsCoeffA, add_mul, coeff_add, coeff_X_mul, coeff_C_mul]

lemma coeff_coloredSetPartitionsCoeffB_mul_derivative (m k : Nat) (p : ℝ[X]) :
    coeff (coloredSetPartitionsCoeffB m * p.derivative) (k + 1) =
      ((m : ℝ) * (k + 1 : ℝ)) * coeff p (k + 1) := by
  simp [coloredSetPartitionsCoeffB, mul_assoc, coeff_derivative, mul_comm]

lemma coeff_coloredSetPartitions_succ (c m n k : Nat) :
    coeff (coloredSetPartitions c m (n + 1)) (k + 1) =
      coeff (coloredSetPartitions c m n) k +
        ((c : ℝ) + (m : ℝ) * (k + 1 : ℝ)) * coeff (coloredSetPartitions c m n) (k + 1) := by
  rw [coloredSetPartitions_succ, coeff_add, coeff_coloredSetPartitionsCoeffA_mul,
    coeff_coloredSetPartitionsCoeffB_mul_derivative]
  ring

lemma coeff_coloredSetPartitions_top_and_above :
    ∀ c m n : Nat,
      coeff (coloredSetPartitions c m n) n = 1 ∧
        ∀ k > n, coeff (coloredSetPartitions c m n) k = 0
  | c, m, 0 => by
      grind [coloredSetPartitions_zero, coeff_one]
  | c, m, n + 1 => by
      rcases coeff_coloredSetPartitions_top_and_above c m n with ⟨htop, habove⟩
      constructor
      · rw [show n + 1 = n + 0 + 1 by lia, coeff_coloredSetPartitions_succ]
        simp [htop, habove (n + 1) (by lia)]
      · rintro (_ | j) hk
        · lia
        · rw [show j + 1 = j + 0 + 1 by lia, coeff_coloredSetPartitions_succ]
          simp [habove j (by lia), habove (j + 1) (by lia)]

lemma natDegree_coloredSetPartitions (c m n : Nat) :
    (coloredSetPartitions c m n).natDegree = n := by
  rr_row_natDegree

lemma monic_coloredSetPartitions (c m n : Nat) :
    (coloredSetPartitions c m n).Monic := by
  rcases coeff_coloredSetPartitions_top_and_above c m n with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_coloredSetPartitions]
  lia

lemma coloredSetPartitions_ne_zero (c m n : Nat) :
    coloredSetPartitions c m n ≠ 0 :=
  (monic_coloredSetPartitions c m n).ne_zero

lemma coloredSetPartitions_posLeadingCoeff (c m n : Nat) :
    HasPosLeadingCoeff (coloredSetPartitions c m n) :=
  hasPosLeadingCoeff_of_monic (monic_coloredSetPartitions c m n)

lemma coloredSetPartitions_nonnegCoeffs :
    ∀ c m n : Nat, HasNonnegCoeffs (coloredSetPartitions c m n) := by
  intros
  rr_row_nonneg_coeffs

lemma roots_nonpos_coloredSetPartitions_of_isRealRooted {c m n : Nat} :
    ∀ r ∈ (coloredSetPartitions c m n).roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (coloredSetPartitions_nonnegCoeffs c m n)

lemma interlaces_coloredSetPartitions_zero_one (c m : Nat) :
    Interlaces (coloredSetPartitions c m 0) (coloredSetPartitions c m 1) := by
  rr_row_interlaces

lemma eval_coloredSetPartitionsCoeffB_nonpos_of_nonpos (m : Nat) {r : ℝ} (hr : r ≤ 0) :
    (coloredSetPartitionsCoeffB m).eval r ≤ 0 := by
  simpa only [coloredSetPartitionsCoeffB, eval_mul, eval_C, eval_X] using
    mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ (m : ℝ)) hr

/-- Consecutive colored set-partition polynomials satisfy `StrictInterl`, hence form a
Sturm sequence. -/
theorem strictInterl_coloredSetPartitions_succ (c m : Nat) :
    ∀ n : Nat, StrictInterl (coloredSetPartitions c m n) (coloredSetPartitions c m (n + 1)) := by
  intros
  rr_row_strictInterl

lemma strictInterl_coloredSetPartitions_one_two (c m : Nat) :
    StrictInterl (coloredSetPartitions c m 1) (coloredSetPartitions c m 2) :=
  strictInterl_coloredSetPartitions_succ c m 1

theorem interlaces_coloredSetPartitions_succ (c m n : Nat) :
    Interlaces (coloredSetPartitions c m n) (coloredSetPartitions c m (n + 1)) :=
  (strictInterl_coloredSetPartitions_succ c m n).toInterlaces
    (by simp [natDegree_coloredSetPartitions])

theorem isRealRooted_coloredSetPartitions (c m : Nat) :
    ∀ n : Nat, ((coloredSetPartitions c m n) ≠ 0 ∧ (coloredSetPartitions c m n).Splits)
  | 0 => by simp
  | n + 1 => (strictInterl_coloredSetPartitions_succ c m n).2.1

/-- The descending prefix `[T_n, T_{n-1}, ..., T_0]` of the colored
set-partition sequence. -/
def coloredSetPartitionsPrefix (c m : Nat) : Nat → List ℝ[X]
  | 0 => [coloredSetPartitions c m 0]
  | n + 1 => coloredSetPartitions c m (n + 1) :: coloredSetPartitionsPrefix c m n

@[simp] lemma coloredSetPartitionsPrefix_zero (c m : Nat) :
    coloredSetPartitionsPrefix c m 0 = [coloredSetPartitions c m 0] := rfl

@[simp] lemma coloredSetPartitionsPrefix_succ (c m n : Nat) :
    coloredSetPartitionsPrefix c m (n + 1) =
      coloredSetPartitions c m (n + 1) :: coloredSetPartitionsPrefix c m n := rfl

theorem isSturmSeq_coloredSetPartitionsPrefix (c m : Nat) :
    ∀ n : Nat, IsSturmSeq (coloredSetPartitionsPrefix c m n) := by
  intro n
  induction n with
  | zero =>
      simp [coloredSetPartitionsPrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [coloredSetPartitionsPrefix, IsSturmSeq] using
            interlaces_coloredSetPartitions_zero_one c m
      | succ k =>
          simpa [coloredSetPartitionsPrefix, IsSturmSeq] using
            And.intro (interlaces_coloredSetPartitions_succ c m (k + 1)) ih

/-- The type `B` set-partition family is the first nontrivial colored
specialization. -/
abbrev typeBSetPartitions : Nat → ℝ[X] :=
  coloredSetPartitions 1 2

theorem interlaces_typeBSetPartitions_succ (n : Nat) :
    Interlaces (typeBSetPartitions n) (typeBSetPartitions (n + 1)) :=
  interlaces_coloredSetPartitions_succ 1 2 n

theorem isRealRooted_typeBSetPartitions (n : Nat) :
    ((typeBSetPartitions n) ≠ 0 ∧ (typeBSetPartitions n).Splits) :=
  isRealRooted_coloredSetPartitions 1 2 n

end RealRooted
