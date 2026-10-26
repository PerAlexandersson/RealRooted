module

public import RealRooted.CombinatorialExamples.Common
public import RealRooted.DerivativeRecurrence.QuadraticInterlacing
public import RealRooted.GeneralizedEulerian
public import Mathlib.Tactic
import RealRooted.Tactic.RowInterlacing

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# Type B Eulerian Polynomials

Real-rootedness and Sturm-sequence facts for the type `B` Eulerian recurrence.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The linear coefficient block in the type `B` Eulerian recurrence. -/
def typeBEulerianCoeffA (n : Nat) : ℝ[X] :=
  1 + C (2 * n + 1 : ℝ) * X

/-- The derivative coefficient block in the type `B` Eulerian recurrence. -/
def typeBEulerianCoeffB : ℝ[X] :=
  C (2 : ℝ) * X * (1 - X)

/-- Type `B` Eulerian polynomials, defined recursively from
`P_{n+1} = (1 + (2n+1)X) P_n + 2X(1-X) P'_n` with `P_0 = 1`. -/
def typeBEulerian : Nat → ℝ[X]
  | 0 => 1
  | n + 1 =>
      typeBEulerianCoeffA n * typeBEulerian n +
        typeBEulerianCoeffB * (typeBEulerian n).derivative

@[simp] lemma typeBEulerian_zero : typeBEulerian 0 = 1 := rfl

lemma typeBEulerian_succ (n : Nat) :
    typeBEulerian (n + 1) =
      typeBEulerianCoeffA n * typeBEulerian n +
        typeBEulerianCoeffB * (typeBEulerian n).derivative := rfl

lemma typeBEulerian_one : typeBEulerian 1 = 1 + X := by
  simp [typeBEulerian, typeBEulerianCoeffA, typeBEulerianCoeffB]

lemma coeff_typeBEulerianCoeffA_mul (n m : Nat) (p : ℝ[X]) :
    coeff (typeBEulerianCoeffA n * p) (m + 1) =
      coeff p (m + 1) + (2 * n + 1 : ℝ) * coeff p m := by
  simp [typeBEulerianCoeffA, add_mul, coeff_add, mul_assoc]

lemma coeff_typeBEulerianCoeffB_mul_derivative (m : Nat) (p : ℝ[X]) :
    coeff (typeBEulerianCoeffB * p.derivative) (m + 1) =
      (2 * (m + 1) : ℝ) * coeff p (m + 1) - (2 * m : ℝ) * coeff p m := by
  rw [show typeBEulerianCoeffB * p.derivative =
    C (2 : ℝ) * X * p.derivative - C (2 : ℝ) * X * X * p.derivative by
      rw [typeBEulerianCoeffB]; ring, coeff_sub]
  rcases m with _ | m
  · simp [coeff_derivative, mul_assoc]
  · simp [coeff_derivative, mul_assoc]
    ring

lemma coeff_typeBEulerian_succ (n m : Nat) :
    coeff (typeBEulerian (n + 1)) (m + 1) =
      ((2 * n + 1 : ℝ) - 2 * m) * coeff (typeBEulerian n) m +
      (2 * m + 3 : ℝ) * coeff (typeBEulerian n) (m + 1) := by
  rw [typeBEulerian_succ, coeff_add, coeff_typeBEulerianCoeffA_mul,
    coeff_typeBEulerianCoeffB_mul_derivative]
  ring

lemma coeff_typeBEulerian_zero :
    ∀ n : Nat, coeff (typeBEulerian n) 0 = 1
  | 0 => by
      simp [typeBEulerian_zero]
  | n + 1 => by
      rw [typeBEulerian_succ, coeff_add, typeBEulerianCoeffA]
      simp [typeBEulerianCoeffB, coeff_typeBEulerian_zero n]

lemma coeff_typeBEulerian_top_and_above :
    ∀ n : Nat, coeff (typeBEulerian n) n = 1 ∧ ∀ m > n, coeff (typeBEulerian n) m = 0
  | 0 => by
      grind [typeBEulerian_zero, coeff_one]
  | n + 1 => by
      rcases coeff_typeBEulerian_top_and_above n with ⟨htop, habove⟩
      constructor
      · rw [show n + 1 = n + 0 + 1 by lia, coeff_typeBEulerian_succ]
        simp [htop, habove (n + 1) (by lia)]
      · rintro (_ | k) hm
        · lia
        · rw [show k + 1 = k + 0 + 1 by lia, coeff_typeBEulerian_succ]
          simp [habove k (by lia), habove (k + 1) (by lia)]

lemma natDegree_typeBEulerian (n : Nat) :
    (typeBEulerian n).natDegree = n := by
  rr_row_natDegree

lemma monic_typeBEulerian (n : Nat) :
    (typeBEulerian n).Monic := by
  rcases coeff_typeBEulerian_top_and_above n with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_typeBEulerian]
  lia

lemma typeBEulerian_ne_zero (n : Nat) :
    typeBEulerian n ≠ 0 := by
  rr_row_ne_zero

lemma typeBEulerian_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (typeBEulerian n) :=
  hasPosLeadingCoeff_of_monic (monic_typeBEulerian n)

lemma typeBEulerian_nonnegCoeffs : ∀ n : Nat, HasNonnegCoeffs (typeBEulerian n) := by
  rr_row_nonneg_coeffs

lemma roots_nonpos_typeBEulerian_of_isRealRooted {n : Nat} :
    ∀ r ∈ (typeBEulerian n).roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (typeBEulerian_nonnegCoeffs n)

lemma interlaces_typeBEulerian_zero_one :
    Interlaces (typeBEulerian 0) (typeBEulerian 1) :=
  by simpa [typeBEulerian_zero, typeBEulerian_one, add_comm] using
    interlaces_one_linear (p := X + C (1 : ℝ))
      (Polynomial.natDegree_X_add_C (x := (1 : ℝ)))

lemma interlaces_derivative_typeBEulerian :
    ∀ n : Nat, 1 ≤ n → (typeBEulerian n).Splits →
      Interlaces (typeBEulerian n).derivative (typeBEulerian n)
  | 0, hn, _ => by
      lia
  | 1, _, _ => by
      simpa [typeBEulerian_one, add_comm] using
        interlaces_one_linear (p := X + C (1 : ℝ))
          (Polynomial.natDegree_X_add_C (x := (1 : ℝ)))
  | n + 2, _, hrr =>
      derivative_interlaces_of_natDegree_ne_zero hrr (by simp [natDegree_typeBEulerian])

lemma eval_typeBEulerianCoeffB_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    typeBEulerianCoeffB.eval r ≤ 0 := by
  simp [typeBEulerianCoeffB]
  nlinarith

theorem strictInterl_typeBEulerian_succ :
    ∀ n : Nat, StrictInterl (typeBEulerian n) (typeBEulerian (n + 1)) := by
  intro n
  exact (show Interlaces (typeBEulerian n) (typeBEulerian (n + 1)) by
    rr_row_interlaces).toStrictInterl

theorem interlaces_typeBEulerian_succ (n : Nat) :
    Interlaces (typeBEulerian n) (typeBEulerian (n + 1)) := by
  rr_row_interlaces

theorem isRealRooted_typeBEulerian :
    ∀ n : Nat, ((typeBEulerian n) ≠ 0 ∧ (typeBEulerian n).Splits)
  | 0 => by simp
  | n + 1 => (strictInterl_typeBEulerian_succ n).2.1

/-- The descending prefix `[P_n, P_{n-1}, ..., P_0]` of the type `B` Eulerian sequence. -/
def typeBEulerianPrefix : Nat → List ℝ[X]
  | 0 => [typeBEulerian 0]
  | n + 1 => typeBEulerian (n + 1) :: typeBEulerianPrefix n

theorem isSturmSeq_typeBEulerianPrefix :
    ∀ n : Nat, IsSturmSeq (typeBEulerianPrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [typeBEulerianPrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [typeBEulerianPrefix, IsSturmSeq] using interlaces_typeBEulerian_zero_one
      | succ k =>
          simpa [typeBEulerianPrefix, IsSturmSeq] using
            And.intro (interlaces_typeBEulerian_succ (k + 1)) ih

/-- The type `B` Eulerian polynomials are the generalized Eulerian
polynomials at parameter two. -/
theorem typeBEulerian_eq_generalizedEulerian_two (n : ℕ) :
    typeBEulerian n = generalizedEulerian 2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [typeBEulerian_succ, generalizedEulerian_succ, ih, typeBEulerianCoeffA,
      typeBEulerianCoeffB]

end RealRooted
