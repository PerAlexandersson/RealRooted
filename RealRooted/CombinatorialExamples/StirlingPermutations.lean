import RealRooted.CombinatorialExamples.Common
import RealRooted.DerivativeRecurrence.QuadraticInterlacing
import Mathlib.Tactic

/-!
# Stirling-Permutation Descent Polynomials

Real-rootedness and Sturm-sequence facts for Stirling-permutation descent
polynomials.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The linear coefficient block in the Stirling-permutation recurrence. -/
def stirlingPermutationsCoeffA (n : Nat) : ℝ[X] :=
  C (2 * n + 1 : ℝ) * X

/-- The derivative coefficient block in the Stirling-permutation recurrence. -/
def stirlingPermutationsCoeffB : ℝ[X] :=
  X * (1 - X)

/-- The Stirling-permutation descent polynomials, defined recursively from
`P_{n+1}(X) = (2n+1)X P_n(X) + X(1-X) P'_n(X)` with `P₀(X) = 1`. -/
def stirlingPermutations : Nat → ℝ[X]
  | 0 => 1
  | n + 1 =>
      stirlingPermutationsCoeffA n * stirlingPermutations n +
        stirlingPermutationsCoeffB * (stirlingPermutations n).derivative

@[simp] lemma stirlingPermutations_zero :
    stirlingPermutations 0 = 1 := rfl

lemma stirlingPermutations_succ (n : Nat) :
    stirlingPermutations (n + 1) =
      stirlingPermutationsCoeffA n * stirlingPermutations n +
        stirlingPermutationsCoeffB * (stirlingPermutations n).derivative := rfl

private lemma stirlingPermutations_quadratic_derivative_linear (n : Nat) :
    stirlingPermutations (n + 1) =
      (C (1 : ℝ) * X + C (-1 : ℝ) * X ^ 2) *
          (stirlingPermutations n).derivative +
        (C (0 : ℝ) + C (1 + 2 * (n : ℝ)) * X) * stirlingPermutations n := by
  rw [stirlingPermutations_succ]
  simp only [stirlingPermutationsCoeffA, stirlingPermutationsCoeffB]
  ring

lemma stirlingPermutations_one :
    stirlingPermutations 1 = X := by
  simp [stirlingPermutations, stirlingPermutationsCoeffA, stirlingPermutationsCoeffB]

lemma coeff_stirlingPermutationsCoeffA_mul (n k : Nat) (p : ℝ[X]) :
    coeff (stirlingPermutationsCoeffA n * p) (k + 1) =
      (2 * n + 1 : ℝ) * coeff p k := by
  rw [stirlingPermutationsCoeffA, mul_assoc, coeff_C_mul]
  simp

lemma coeff_stirlingPermutationsCoeffB_mul_derivative (k : Nat) (p : ℝ[X]) :
    coeff (stirlingPermutationsCoeffB * p.derivative) (k + 1) =
      (k + 1 : ℝ) * coeff p (k + 1) - (k : ℝ) * coeff p k := by
  have hB :
      stirlingPermutationsCoeffB * p.derivative =
        X * p.derivative - X * X * p.derivative := by
    rw [stirlingPermutationsCoeffB]
    ring
  cases k with
  | zero =>
      rw [hB, coeff_sub]
      have h₁ : coeff (X * p.derivative) 1 = coeff p 1 := by simp [coeff_derivative]
      have h₂ : coeff (X * X * p.derivative) 1 = 0 := by simp [mul_assoc]
      simp [h₁, h₂]
  | succ k =>
      rw [hB, coeff_sub]
      have h₁ : coeff (X * p.derivative) (k + 2) =
          (k + 2 : ℝ) * coeff p (k + 2) := by
        simp [coeff_derivative]
        ring
      have h₂ : coeff (X * X * p.derivative) (k + 2) =
          (k + 1 : ℝ) * coeff p (k + 1) := by
        rw [show X * X * p.derivative = X * (X * p.derivative) by ring]
        simp [coeff_derivative]
        ring
      grind

lemma coeff_stirlingPermutations_succ (n k : Nat) :
    coeff (stirlingPermutations (n + 1)) (k + 1) =
      ((2 * n + 1 : ℝ) - k) * coeff (stirlingPermutations n) k +
        (k + 1 : ℝ) * coeff (stirlingPermutations n) (k + 1) := by
  rw [stirlingPermutations_succ, coeff_add, coeff_stirlingPermutationsCoeffA_mul,
    coeff_stirlingPermutationsCoeffB_mul_derivative]
  ring

lemma coeff_stirlingPermutations_top_pos_and_above :
    ∀ n : Nat,
      0 < coeff (stirlingPermutations n) n ∧
        ∀ k > n, coeff (stirlingPermutations n) k = 0
  | 0 => by
      grind [stirlingPermutations_zero, coeff_one]
  | n + 1 => by
      rcases coeff_stirlingPermutations_top_pos_and_above n with ⟨htop, habove⟩
      constructor
      · rw [show n + 1 = n + 0 + 1 by lia, coeff_stirlingPermutations_succ]
        have hzero : coeff (stirlingPermutations n) (n + 1) = 0 :=
          habove (n + 1) (by lia)
        have hscale : 0 < ((2 * n + 1 : ℝ) - n) := by nlinarith
        simp_all
      · intro k hk
        cases k with
        | zero =>
            lia
        | succ j =>
            rw [show j + 1 = j + 0 + 1 by lia, coeff_stirlingPermutations_succ]
            simp [habove j (by lia), habove (j + 1) (by lia)]

lemma natDegree_stirlingPermutations (n : Nat) :
    (stirlingPermutations n).natDegree = n := by
  exact natDegree_of_quadratic_derivative_linear stirlingPermutations 1 1 0 1 2
    stirlingPermutations_zero stirlingPermutations_quadratic_derivative_linear
    (by norm_num) (by norm_num) n

lemma stirlingPermutations_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (stirlingPermutations n) := by
  exact hasPosLeadingCoeff_of_quadratic_derivative_linear stirlingPermutations 1 1 0 1 2
    stirlingPermutations_zero stirlingPermutations_quadratic_derivative_linear
    (by norm_num) (by norm_num) n

lemma stirlingPermutations_ne_zero (n : Nat) :
    stirlingPermutations n ≠ 0 :=
  (stirlingPermutations_posLeadingCoeff n).ne_zero

lemma stirlingPermutations_nonnegCoeffs :
    ∀ n : Nat, HasNonnegCoeffs (stirlingPermutations n) := by
  exact hasNonnegCoeffs_of_quadratic_derivative_linear stirlingPermutations 1 1 0 1 2
    stirlingPermutations_zero stirlingPermutations_quadratic_derivative_linear
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma roots_nonpos_stirlingPermutations_of_isRealRooted {n : Nat}
    (hrr : (stirlingPermutations n).Splits) :
    ∀ r ∈ (stirlingPermutations n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (stirlingPermutations_nonnegCoeffs n)

lemma interlaces_stirlingPermutations_zero_one :
    Interlaces (stirlingPermutations 0) (stirlingPermutations 1) := by
  simpa [stirlingPermutations_zero, stirlingPermutations_one] using
    interlaces_one_linear (p := X) (by simp)

lemma eval_stirlingPermutationsCoeffB_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    stirlingPermutationsCoeffB.eval r ≤ 0 := by
  simp [stirlingPermutationsCoeffB]
  nlinarith

private theorem strictInterl_stirlingPermutations_quadratic :
    ∀ n : Nat, StrictInterl (stirlingPermutations n) (stirlingPermutations (n + 1)) := by
  exact strictInterl_of_quadratic_derivative_linear stirlingPermutations 1 1 0 1 2
    stirlingPermutations_zero stirlingPermutations_quadratic_derivative_linear
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma strictInterl_stirlingPermutations_one_two :
    StrictInterl (stirlingPermutations 1) (stirlingPermutations 2) := by
  simpa using strictInterl_stirlingPermutations_quadratic 1

theorem strictInterl_stirlingPermutations_succ :
    ∀ n : Nat, StrictInterl (stirlingPermutations n) (stirlingPermutations (n + 1)) := by
  exact strictInterl_stirlingPermutations_quadratic

theorem interlaces_stirlingPermutations_succ (n : Nat) :
    Interlaces (stirlingPermutations n) (stirlingPermutations (n + 1)) :=
  (strictInterl_stirlingPermutations_succ n).toInterlaces
    (by simp [natDegree_stirlingPermutations])

theorem isRealRooted_stirlingPermutations :
    ∀ n : Nat, ((stirlingPermutations n) ≠ 0 ∧ (stirlingPermutations n).Splits)
  | 0 => by simp
  | n + 1 => (strictInterl_stirlingPermutations_succ n).2.1

/-- The descending prefix `[P_n, P_{n-1}, ..., P_0]` of the Stirling-permutation
sequence. -/
def stirlingPermutationsPrefix : Nat → List ℝ[X]
  | 0 => [stirlingPermutations 0]
  | n + 1 => stirlingPermutations (n + 1) :: stirlingPermutationsPrefix n

@[simp] lemma stirlingPermutationsPrefix_zero :
    stirlingPermutationsPrefix 0 = [stirlingPermutations 0] := rfl

@[simp] lemma stirlingPermutationsPrefix_succ (n : Nat) :
    stirlingPermutationsPrefix (n + 1) =
      stirlingPermutations (n + 1) :: stirlingPermutationsPrefix n := rfl

theorem isSturmSeq_stirlingPermutationsPrefix :
    ∀ n : Nat, IsSturmSeq (stirlingPermutationsPrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [stirlingPermutationsPrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [stirlingPermutationsPrefix, IsSturmSeq] using
            interlaces_stirlingPermutations_zero_one
      | succ k =>
          simpa [stirlingPermutationsPrefix, IsSturmSeq] using
            And.intro (interlaces_stirlingPermutations_succ (k + 1)) ih

end RealRooted
