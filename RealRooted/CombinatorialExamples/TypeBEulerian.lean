import RealRooted.CombinatorialExamples.Common
import RealRooted.MaWang
import Mathlib.Tactic

/-!
# Type B Eulerian Polynomials

Real-rootedness and Sturm-sequence facts for the type `B` Eulerian recurrence.
-/

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
  have hCX : coeff (C (2 * n + 1 : ℝ) * X * p) (m + 1) =
      (2 * n + 1 : ℝ) * coeff p m := by
    calc
      coeff (C (2 * n + 1 : ℝ) * X * p) (m + 1)
          = coeff (C (2 * n + 1 : ℝ) * (X * p)) (m + 1) := by grind
      _ = (2 * n + 1 : ℝ) * coeff (X * p) (m + 1) := by grind
      _ = (2 * n + 1 : ℝ) * coeff p m := by simp
  rw [typeBEulerianCoeffA, add_mul, one_mul, coeff_add, hCX]

lemma coeff_typeBEulerianCoeffB_mul_derivative (m : Nat) (p : ℝ[X]) :
    coeff (typeBEulerianCoeffB * p.derivative) (m + 1) =
      (2 * (m + 1) : ℝ) * coeff p (m + 1) - (2 * m : ℝ) * coeff p m := by
  have hB :
      typeBEulerianCoeffB * p.derivative =
        C (2 : ℝ) * X * p.derivative - C (2 : ℝ) * X * X * p.derivative := by
    rw [typeBEulerianCoeffB]
    ring
  cases m with
  | zero =>
      rw [hB, coeff_sub]
      have h₁ : coeff (C (2 : ℝ) * X * p.derivative) 1 = (2 : ℝ) * coeff p 1 := by
        calc
          coeff (C (2 : ℝ) * X * p.derivative) 1
              = coeff (C (2 : ℝ) * (X * p.derivative)) 1 := by grind
          _ = (2 : ℝ) * coeff (X * p.derivative) 1 := by simp
          _ = (2 : ℝ) * coeff p.derivative 0 := by simp
          _ = (2 : ℝ) * coeff p 1 := by
              rw [coeff_derivative]
              ring
      have h₂ : coeff (C (2 : ℝ) * X * X * p.derivative) 1 = 0 := by
        calc
          coeff (C (2 : ℝ) * X * X * p.derivative) 1
              = coeff (C (2 : ℝ) * (X * (X * p.derivative))) 1 := by grind
          _ = (2 : ℝ) * coeff (X * (X * p.derivative)) 1 := by simp
          _ = (2 : ℝ) * coeff (X * p.derivative) 0 := by simp
          _ = 0 := by simp
      simp_all
  | succ m =>
      rw [hB, coeff_sub]
      have h₁ : coeff (C (2 : ℝ) * X * p.derivative) (m + 2) =
          (2 * (m + 2) : ℝ) * coeff p (m + 2) := by
        calc
          coeff (C (2 : ℝ) * X * p.derivative) (m + 2)
              = coeff (C (2 : ℝ) * (X * p.derivative)) (m + 2) := by grind
          _ = (2 : ℝ) * coeff (X * p.derivative) (m + 2) := by simp
          _ = (2 : ℝ) * coeff p.derivative (m + 1) := by simp
          _ = (2 : ℝ) * (coeff p (m + 2) * ((m : ℝ) + 2)) := by
              rw [coeff_derivative]
              grind
          _ = (2 * (m + 2) : ℝ) * coeff p (m + 2) := by grind
      have h₂ : coeff (C (2 : ℝ) * X * X * p.derivative) (m + 2) =
          (2 * (m + 1) : ℝ) * coeff p (m + 1) := by
        calc
          coeff (C (2 : ℝ) * X * X * p.derivative) (m + 2)
              = coeff (C (2 : ℝ) * (X * (X * p.derivative))) (m + 2) := by
                  grind
          _ = (2 : ℝ) * coeff (X * (X * p.derivative)) (m + 2) := by simp
          _ = (2 : ℝ) * coeff (X * p.derivative) (m + 1) := by simp
          _ = (2 : ℝ) * coeff p.derivative m := by simp
          _ = (2 * (m + 1) : ℝ) * coeff p (m + 1) := by
              rw [coeff_derivative]
              grind
      grind

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
        simp_all
      · rintro (_ | k) hm
        · lia
        · rw [show k + 1 = k + 0 + 1 by lia, coeff_typeBEulerian_succ]
          grind

lemma natDegree_typeBEulerian (n : Nat) :
    (typeBEulerian n).natDegree = n := by
  rcases coeff_typeBEulerian_top_and_above n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm))
    (by simp [htop])

lemma monic_typeBEulerian (n : Nat) :
    (typeBEulerian n).Monic := by
  rcases coeff_typeBEulerian_top_and_above n with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_typeBEulerian]
  lia

lemma typeBEulerian_ne_zero (n : Nat) :
    typeBEulerian n ≠ 0 :=
  (monic_typeBEulerian n).ne_zero

lemma typeBEulerian_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (typeBEulerian n) := by
  simp [HasPosLeadingCoeff, (monic_typeBEulerian n).leadingCoeff]

lemma typeBEulerian_nonnegCoeffs : ∀ n : Nat, HasNonnegCoeffs (typeBEulerian n)
  | 0 => by
      intro m
      cases m <;> simp [typeBEulerian_zero, coeff_one]
  | n + 1 => by
      rintro (_ | m)
      · rw [coeff_typeBEulerian_zero]
        positivity
      · rw [coeff_typeBEulerian_succ]
        by_cases hm : m ≤ n
        · have hcoeff_m : 0 ≤ coeff (typeBEulerian n) m :=
            typeBEulerian_nonnegCoeffs n m
          have hcoeff_succ : 0 ≤ coeff (typeBEulerian n) (m + 1) :=
            typeBEulerian_nonnegCoeffs n (m + 1)
          have hnm : 0 ≤ ((2 * n + 1 : ℝ) - 2 * m) := by
            have hm' : (m : ℝ) ≤ n := by simp_all
            nlinarith
          exact add_nonneg (mul_nonneg hnm hcoeff_m)
            (mul_nonneg (by grind) hcoeff_succ)
        · have hm' : n < m := lt_of_not_ge hm
          rcases coeff_typeBEulerian_top_and_above n with ⟨_, habove⟩
          have hcoeff_m : coeff (typeBEulerian n) m = 0 := by
            simp_all
          have hcoeff_succ : coeff (typeBEulerian n) (m + 1) = 0 := by
            grind
          simp [hcoeff_m, hcoeff_succ]

lemma roots_nonpos_typeBEulerian_of_isRealRooted {n : Nat} (hrr : (typeBEulerian n).Splits) :
    ∀ r ∈ (typeBEulerian n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (typeBEulerian_nonnegCoeffs n)

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
      derivative_interlaces hrr (by simp [natDegree_typeBEulerian])

lemma eval_typeBEulerianCoeffB_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    typeBEulerianCoeffB.eval r ≤ 0 := by
  simp [typeBEulerianCoeffB]
  nlinarith

theorem prec_typeBEulerian_succ : ∀ n : Nat, Prec (typeBEulerian n) (typeBEulerian (n + 1))
  | 0 => interlaces_typeBEulerian_zero_one.toPrec
  | n + 1 => by
      have hInter :
          Interlaces (typeBEulerian (n + 1)).derivative (typeBEulerian (n + 1)) :=
        interlaces_derivative_typeBEulerian (n + 1) (by lia) (prec_typeBEulerian_succ n).2.1.2
      have hg_pos : HasPosLeadingCoeff (typeBEulerian (n + 1)).derivative :=
        (typeBEulerian_posLeadingCoeff (n + 1)).derivative (by
          simp [natDegree_typeBEulerian])
      have hNext_eq :
          typeBEulerianCoeffA (n + 1) * typeBEulerian (n + 1) +
            typeBEulerianCoeffB * (typeBEulerian (n + 1)).derivative =
          typeBEulerian (n + 2) :=
        (typeBEulerian_succ (n + 1)).symm
      have hF_pos :
          HasPosLeadingCoeff
            (typeBEulerianCoeffA (n + 1) * typeBEulerian (n + 1) +
              typeBEulerianCoeffB * (typeBEulerian (n + 1)).derivative) := by
        simpa [hNext_eq] using typeBEulerian_posLeadingCoeff (n + 2)
      have hdeg_lo :
          (typeBEulerian (n + 1)).natDegree ≤
            (typeBEulerianCoeffA (n + 1) * typeBEulerian (n + 1) +
              typeBEulerianCoeffB * (typeBEulerian (n + 1)).derivative).natDegree := by
        rw [hNext_eq, natDegree_typeBEulerian, natDegree_typeBEulerian]
        lia
      have hdeg_hi :
          (typeBEulerianCoeffA (n + 1) * typeBEulerian (n + 1) +
              typeBEulerianCoeffB * (typeBEulerian (n + 1)).derivative).natDegree ≤
            (typeBEulerian (n + 1)).natDegree + 1 := by
        rw [hNext_eq, natDegree_typeBEulerian, natDegree_typeBEulerian]
      have hb_nonpos :
          ∀ r, (typeBEulerian (n + 1)).IsRoot r → typeBEulerianCoeffB.eval r ≤ 0 := by
        intro r hr
        have hr_nonpos :
            r ≤ 0 := roots_nonpos_typeBEulerian_of_isRealRooted (prec_typeBEulerian_succ n).2.1.2 r
              ((mem_roots (prec_typeBEulerian_succ n).2.1.1).mpr hr)
        exact eval_typeBEulerianCoeffB_nonpos_of_nonpos hr_nonpos
      simpa [hNext_eq] using
        prec_of_interlaces_evalCoeff_nonpos
          (f := typeBEulerian (n + 1))
          (g := (typeBEulerian (n + 1)).derivative)
          (a := typeBEulerianCoeffA (n + 1))
          (b := typeBEulerianCoeffB)
          hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos

theorem interlaces_typeBEulerian_succ (n : Nat) :
    Interlaces (typeBEulerian n) (typeBEulerian (n + 1)) :=
  (prec_typeBEulerian_succ n).toInterlaces (by simp [natDegree_typeBEulerian])

theorem isRealRooted_typeBEulerian : ∀ n : Nat, ((typeBEulerian n) ≠ 0 ∧ (typeBEulerian n).Splits)
  | 0 => by simp
  | n + 1 => (prec_typeBEulerian_succ n).2.1

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

end RealRooted
