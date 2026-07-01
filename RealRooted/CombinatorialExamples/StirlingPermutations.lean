import RealRooted.CombinatorialExamples.Common
import RealRooted.MaWang
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
      have h₁ : coeff (X * p.derivative) 1 = coeff p 1 := by
        simp [coeff_derivative]
      have h₂ : coeff (X * X * p.derivative) 1 = 0 := by
        simp [mul_assoc]
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
        have hscale : 0 < ((2 * n + 1 : ℝ) - n) := by
          nlinarith
        simpa [hzero] using mul_pos hscale htop
      · intro k hk
        cases k with
        | zero =>
            lia
        | succ j =>
            rw [show j + 1 = j + 0 + 1 by lia, coeff_stirlingPermutations_succ]
            simp [habove j (by lia), habove (j + 1) (by lia)]

lemma natDegree_stirlingPermutations (n : Nat) :
    (stirlingPermutations n).natDegree = n := by
  rcases coeff_stirlingPermutations_top_pos_and_above n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => habove k hk))
    (ne_of_gt htop)

lemma stirlingPermutations_ne_zero (n : Nat) :
    stirlingPermutations n ≠ 0 := by
  rcases coeff_stirlingPermutations_top_pos_and_above n with ⟨htop, _⟩
  exact fun h0 => by
    simp [h0] at htop

lemma stirlingPermutations_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (stirlingPermutations n) := by
  simpa [HasPosLeadingCoeff, leadingCoeff, natDegree_stirlingPermutations] using
    (coeff_stirlingPermutations_top_pos_and_above n).1

lemma stirlingPermutations_nonnegCoeffs :
    ∀ n : Nat, HasNonnegCoeffs (stirlingPermutations n)
  | 0 => by
      intro k
      cases k <;> simp [stirlingPermutations_zero, coeff_one]
  | n + 1 => by
      rintro (_ | j)
      · simp [stirlingPermutations_succ, stirlingPermutationsCoeffA, stirlingPermutationsCoeffB]
      · rw [coeff_stirlingPermutations_succ]
        by_cases hj : j ≤ n
        · have hcoeff_j : 0 ≤ coeff (stirlingPermutations n) j :=
            stirlingPermutations_nonnegCoeffs n j
          have hcoeff_j1 : 0 ≤ coeff (stirlingPermutations n) (j + 1) :=
            stirlingPermutations_nonnegCoeffs n (j + 1)
          have hscale : 0 ≤ ((2 * n + 1 : ℝ) - j) := by
            have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj
            nlinarith
          exact add_nonneg (mul_nonneg hscale hcoeff_j)
            (mul_nonneg (by positivity) hcoeff_j1)
        · have hj' : n < j := lt_of_not_ge hj
          rcases coeff_stirlingPermutations_top_pos_and_above n with ⟨_, habove⟩
          have hcoeff_j : coeff (stirlingPermutations n) j = 0 := habove j hj'
          have hcoeff_j1 : coeff (stirlingPermutations n) (j + 1) = 0 :=
            habove (j + 1) (by lia)
          simp [hcoeff_j, hcoeff_j1]

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

lemma prec_stirlingPermutations_one_two :
    Prec (stirlingPermutations 1) (stirlingPermutations 2) := by
  have hdeg : (stirlingPermutations 1).natDegree = 1 :=
    natDegree_stirlingPermutations 1
  have hf : ((stirlingPermutations 1) ≠ 0 ∧ (stirlingPermutations 1).Splits) :=
    isRealRooted_of_degree_one hdeg
  have hInter :
      Interlaces (stirlingPermutations 1).derivative (stirlingPermutations 1) := by
    simpa [stirlingPermutations_one] using
      interlaces_one_linear (p := stirlingPermutations 1) hdeg
  have hg_pos : HasPosLeadingCoeff (stirlingPermutations 1).derivative :=
    (stirlingPermutations_posLeadingCoeff 1).derivative (by simp [natDegree_stirlingPermutations])
  have hNext_eq :
      stirlingPermutationsCoeffA 1 * stirlingPermutations 1 +
          stirlingPermutationsCoeffB * (stirlingPermutations 1).derivative =
        stirlingPermutations 2 :=
    (stirlingPermutations_succ 1).symm
  have hF_pos :
      HasPosLeadingCoeff
        (stirlingPermutationsCoeffA 1 * stirlingPermutations 1 +
          stirlingPermutationsCoeffB * (stirlingPermutations 1).derivative) := by
    simpa [hNext_eq] using stirlingPermutations_posLeadingCoeff 2
  have hdeg_lo :
      (stirlingPermutations 1).natDegree ≤
        (stirlingPermutationsCoeffA 1 * stirlingPermutations 1 +
          stirlingPermutationsCoeffB * (stirlingPermutations 1).derivative).natDegree := by
    rw [hNext_eq, natDegree_stirlingPermutations, natDegree_stirlingPermutations]
    lia
  have hdeg_hi :
      (stirlingPermutationsCoeffA 1 * stirlingPermutations 1 +
          stirlingPermutationsCoeffB * (stirlingPermutations 1).derivative).natDegree ≤
        (stirlingPermutations 1).natDegree + 1 := by
    rw [hNext_eq, natDegree_stirlingPermutations, natDegree_stirlingPermutations]
  have hb_nonpos :
      ∀ r, (stirlingPermutations 1).IsRoot r →
        stirlingPermutationsCoeffB.eval r ≤ 0 := by
    intro r hr
    have hr_nonpos :
        r ≤ 0 :=
      roots_nonpos_stirlingPermutations_of_isRealRooted hf.2 r ((mem_roots hf.1).mpr hr)
    exact eval_stirlingPermutationsCoeffB_nonpos_of_nonpos hr_nonpos
  simpa [hNext_eq] using
    prec_of_interlaces_evalCoeff_nonpos
      (f := stirlingPermutations 1)
      (g := (stirlingPermutations 1).derivative)
      (a := stirlingPermutationsCoeffA 1)
      (b := stirlingPermutationsCoeffB)
      hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos

theorem prec_stirlingPermutations_succ :
    ∀ n : Nat, Prec (stirlingPermutations n) (stirlingPermutations (n + 1))
  | 0 => interlaces_stirlingPermutations_zero_one.toPrec
  | 1 => prec_stirlingPermutations_one_two
  | n + 2 => by
      have hInter :
          Interlaces (stirlingPermutations (n + 2)).derivative
            (stirlingPermutations (n + 2)) :=
        derivative_interlaces (prec_stirlingPermutations_succ (n + 1)).2.1.2 (by
          simp [natDegree_stirlingPermutations])
      have hg_pos : HasPosLeadingCoeff (stirlingPermutations (n + 2)).derivative :=
        (stirlingPermutations_posLeadingCoeff (n + 2)).derivative (by
          simp [natDegree_stirlingPermutations])
      have hNext_eq :
          stirlingPermutationsCoeffA (n + 2) * stirlingPermutations (n + 2) +
              stirlingPermutationsCoeffB * (stirlingPermutations (n + 2)).derivative =
            stirlingPermutations (n + 3) :=
        (stirlingPermutations_succ (n + 2)).symm
      have hF_pos :
          HasPosLeadingCoeff
            (stirlingPermutationsCoeffA (n + 2) * stirlingPermutations (n + 2) +
              stirlingPermutationsCoeffB * (stirlingPermutations (n + 2)).derivative) := by
        simpa [hNext_eq] using stirlingPermutations_posLeadingCoeff (n + 3)
      have hdeg_lo :
          (stirlingPermutations (n + 2)).natDegree ≤
            (stirlingPermutationsCoeffA (n + 2) * stirlingPermutations (n + 2) +
              stirlingPermutationsCoeffB *
                (stirlingPermutations (n + 2)).derivative).natDegree := by
        rw [hNext_eq, natDegree_stirlingPermutations, natDegree_stirlingPermutations]
        lia
      have hdeg_hi :
          (stirlingPermutationsCoeffA (n + 2) * stirlingPermutations (n + 2) +
              stirlingPermutationsCoeffB * (stirlingPermutations (n + 2)).derivative).natDegree ≤
            (stirlingPermutations (n + 2)).natDegree + 1 := by
        rw [hNext_eq, natDegree_stirlingPermutations, natDegree_stirlingPermutations]
      have hb_nonpos :
          ∀ r, (stirlingPermutations (n + 2)).IsRoot r →
            stirlingPermutationsCoeffB.eval r ≤ 0 := by
        intro r hr
        have hr_nonpos : r ≤ 0 :=
          roots_nonpos_stirlingPermutations_of_isRealRooted
            (prec_stirlingPermutations_succ (n + 1)).2.1.2 r
            ((mem_roots (prec_stirlingPermutations_succ (n + 1)).2.1.1).mpr hr)
        exact eval_stirlingPermutationsCoeffB_nonpos_of_nonpos hr_nonpos
      simpa [hNext_eq] using
        prec_of_interlaces_evalCoeff_nonpos
          (f := stirlingPermutations (n + 2))
          (g := (stirlingPermutations (n + 2)).derivative)
          (a := stirlingPermutationsCoeffA (n + 2))
          (b := stirlingPermutationsCoeffB)
          hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos

theorem interlaces_stirlingPermutations_succ (n : Nat) :
    Interlaces (stirlingPermutations n) (stirlingPermutations (n + 1)) :=
  (prec_stirlingPermutations_succ n).toInterlaces
    (by simp [natDegree_stirlingPermutations])

theorem isRealRooted_stirlingPermutations :
    ∀ n : Nat, ((stirlingPermutations n) ≠ 0 ∧ (stirlingPermutations n).Splits)
  | 0 => by simp
  | n + 1 => (prec_stirlingPermutations_succ n).2.1

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
