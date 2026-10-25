module

public import RealRooted.CombinatorialExamples.Common
public import RealRooted.MaWang
public import RealRooted.Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic
import RealRooted.Tactic.RowInterlacing

/-!
# Simsun Descent Polynomials

Real-rootedness and Sturm-sequence facts for the simsun descent recurrence.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The linear coefficient block in the simsun descent recurrence. -/
def simsunCoeffA (n : Nat) : ℝ[X] :=
  1 + C (n : ℝ) * X

/-- The derivative coefficient block in the simsun descent recurrence. -/
def simsunCoeffB : ℝ[X] :=
  X * (1 - C (2 : ℝ) * X)

/-- Simsun descent polynomials, defined recursively from
`P_{n+1} = (1 + nX) P_n + X(1 - 2X) P'_n` with `P_0 = 1`. -/
def simsun : Nat → ℝ[X]
  | 0 => 1
  | n + 1 =>
      simsunCoeffA n * simsun n +
        simsunCoeffB * (simsun n).derivative

@[simp] lemma simsun_zero : simsun 0 = 1 := rfl

lemma simsun_succ (n : Nat) :
    simsun (n + 1) =
      simsunCoeffA n * simsun n +
        simsunCoeffB * (simsun n).derivative := rfl

@[simp] lemma simsun_one : simsun 1 = 1 := by simp [simsun, simsunCoeffA, simsunCoeffB]

lemma simsun_two : simsun 2 = 1 + X := by simp [simsun, simsunCoeffA, simsunCoeffB]

lemma simsun_three : simsun 3 = 1 + C (4 : ℝ) * X := by
  rw [simsun_succ, simsun_two]
  calc
    simsunCoeffA 2 * (1 + X) + simsunCoeffB * (1 + X).derivative
        = (1 + C (2 : ℝ) * X) * (1 + X) + X * (1 - C (2 : ℝ) * X) := by
            simp [simsunCoeffA, simsunCoeffB]
    _ = 1 + X + C (2 : ℝ) * X + C (2 : ℝ) * X * X + (X - C (2 : ℝ) * X * X) := by ring
    _ = 1 + X + C (2 : ℝ) * X + X := by ring
    _ = 1 + X * C (4 : ℝ) := by
          have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := (ofNat_def 2).symm
          have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := (ofNat_def 4).symm
          grind
    _ = 1 + C (4 : ℝ) * X := by simp

lemma coeff_simsunCoeffA_mul (n m : Nat) (p : ℝ[X]) :
    coeff (simsunCoeffA n * p) (m + 1) =
      coeff p (m + 1) + (n : ℝ) * coeff p m := by
  simp [simsunCoeffA, add_mul, coeff_add, mul_assoc]

lemma coeff_simsunCoeffB_mul_derivative (m : Nat) (p : ℝ[X]) :
    coeff (simsunCoeffB * p.derivative) (m + 1) =
      (m + 1 : ℝ) * coeff p (m + 1) - (2 * m : ℝ) * coeff p m := by
  rw [show simsunCoeffB * p.derivative =
    X * p.derivative - C (2 : ℝ) * X * X * p.derivative by
      rw [simsunCoeffB]; ring, coeff_sub]
  rcases m with _ | m
  · simp [coeff_derivative, mul_assoc]
  · simp [coeff_derivative, mul_assoc]
    ring

lemma coeff_simsun_succ (n m : Nat) :
    coeff (simsun (n + 1)) (m + 1) =
      ((n : ℝ) - 2 * m) * coeff (simsun n) m +
      (m + 2 : ℝ) * coeff (simsun n) (m + 1) := by
  rw [simsun_succ, coeff_add, coeff_simsunCoeffA_mul, coeff_simsunCoeffB_mul_derivative]
  ring

lemma coeff_simsun_zero :
    ∀ n : Nat, coeff (simsun n) 0 = 1
  | 0 => by
      simp [simsun_zero]
  | n + 1 => by
      rw [simsun_succ, coeff_add, simsunCoeffA]
      simp [simsunCoeffB, coeff_simsun_zero n]

lemma simsun_nonnegCoeffs_top_pos_and_above :
    ∀ n : Nat, HasNonnegCoeffs (simsun n) ∧
      0 < coeff (simsun n) (n / 2) ∧
      ∀ m > n / 2, coeff (simsun n) m = 0
  | 0 => by
      refine ⟨?_, ?_, ?_⟩
      · rintro (_ | m)
        · simp [simsun_zero]
        · rw [simsun_zero, coeff_one, ite_eq_right (Nat.succ_ne_zero m)]
      · simp [simsun_zero]
      · intro m hm
        rw [simsun_zero, coeff_one]
        lia
  | 1 => by
      refine ⟨?_, ?_, ?_⟩
      · rintro (_ | m)
        · simp [simsun_one]
        · rw [simsun_one, coeff_one, ite_eq_right (Nat.succ_ne_zero m)]
      · simp [simsun_one]
      · intro m hm
        rw [simsun_one, coeff_one]
        lia
  | n + 2 => by
      rcases simsun_nonnegCoeffs_top_pos_and_above (n + 1) with
        ⟨hprev_nonneg, hprev_top, hprev_above⟩
      refine ⟨?_, ?_, ?_⟩
      · rintro (_ | m)
        · rw [coeff_simsun_zero]
          positivity
        · rw [coeff_simsun_succ]
          by_cases hm : m ≤ (n + 1) / 2
          · have hscale : 0 ≤ (((n + 1 : Nat) : ℝ) - 2 * (m : ℝ)) := by
              have hm' : ((2 * m : Nat) : ℝ) ≤ ((n + 1 : Nat) : ℝ) :=
                Nat.cast_le.mpr (by lia)
              simp_all
            exact add_nonneg
              (mul_nonneg hscale (hprev_nonneg m))
              (mul_nonneg (by positivity) (hprev_nonneg (m + 1)))
          · have hm' : (n + 1) / 2 < m := lt_of_not_ge hm
            have hm_zero : coeff (simsun (n + 1)) m = 0 := hprev_above m hm'
            have hm_succ_zero : coeff (simsun (n + 1)) (m + 1) = 0 :=
              hprev_above (m + 1) (by lia)
            simp [hm_zero, hm_succ_zero]
      · set k : Nat := (n + 2) / 2 - 1
        have hk_succ : k + 1 = (n + 2) / 2 := by lia
        rw [show (n + 2) / 2 = k + 1 by lia, coeff_simsun_succ]
        rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
        · have hk_eq : k = n / 2 := by lia
          have hprev_idx : (n + 1) / 2 = n / 2 := by lia
          have hprev_pos : 0 < coeff (simsun (n + 1)) k := by lia
          have hprev_zero : coeff (simsun (n + 1)) (k + 1) = 0 := by simp_all
          have hdouble : (2 : ℝ) * (k : ℝ) = (n : ℝ) := by
            simpa [Nat.cast_mul] using
              congrArg (fun r : Nat => (r : ℝ)) (show 2 * k = n by lia)
          simp_all
        · have hk_eq : k = n / 2 := by lia
          have hk_top : k + 1 = (n + 1) / 2 := by lia
          have hprev_nonneg_k : 0 ≤ coeff (simsun (n + 1)) k :=
            hprev_nonneg k
          have hprev_pos : 0 < coeff (simsun (n + 1)) (k + 1) := by lia
          have hdouble : (2 : ℝ) * (k : ℝ) + 1 = (n : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, Nat.cast_mul] using
              congrArg (fun r : Nat => (r : ℝ)) (show 2 * k + 1 = n by lia)
          have hcast :
              (((n + 1 : Nat) : ℝ) - 2 * (k : ℝ)) = (n : ℝ) + 1 - 2 * (k : ℝ) := by
            lia
          have hscale_eq : (n : ℝ) + 1 - 2 * (k : ℝ) = 2 := by nlinarith
          have hlead_pos :
              0 < ((k : ℝ) + 2) * coeff (simsun (n + 1)) (k + 1) := by
            have hscale : 0 < (k : ℝ) + 2 := by positivity
            simp_all
          have hsmall_nonneg :
              0 ≤ (((n + 1 : Nat) : ℝ) - 2 * (k : ℝ)) *
                coeff (simsun (n + 1)) k := by
            simp_all
          grind
      · intro m hm
        cases m with
        | zero =>
            lia
        | succ k =>
            rw [coeff_simsun_succ]
            have hk_succ_zero : coeff (simsun (n + 1)) (k + 1) = 0 :=
              hprev_above (k + 1) (by lia)
            by_cases hk : (n + 1) / 2 < k
            · simp_all
            · have hk_le : k ≤ (n + 1) / 2 := le_of_not_gt hk
              have hk_ge : (n + 2) / 2 ≤ k := by lia
              have hk_eq : k = (n + 1) / 2 := by lia
              have hdouble : (2 : ℝ) * (k : ℝ) = (((n + 1 : Nat) : ℝ)) := by
                simpa [Nat.cast_add, Nat.cast_one, Nat.cast_mul] using
                  congrArg (fun r : Nat => (r : ℝ)) (show 2 * k = n + 1 by lia)
              simp_all

lemma simsun_nonnegCoeffs (n : Nat) :
    HasNonnegCoeffs (simsun n) :=
  (simsun_nonnegCoeffs_top_pos_and_above n).1

lemma coeff_simsun_top_pos_and_above (n : Nat) :
    0 < coeff (simsun n) (n / 2) ∧
      ∀ m > n / 2, coeff (simsun n) m = 0 :=
  ⟨(simsun_nonnegCoeffs_top_pos_and_above n).2.1,
    (simsun_nonnegCoeffs_top_pos_and_above n).2.2⟩

lemma natDegree_simsun (n : Nat) :
    (simsun n).natDegree = n / 2 := by
  rr_row_natDegree

lemma simsun_nonzero (n : Nat) :
    simsun n ≠ 0 := by
  rr_row_ne_zero

lemma simsun_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (simsun n) := by
  simpa [HasPosLeadingCoeff, leadingCoeff, natDegree_simsun] using
    (coeff_simsun_top_pos_and_above n).1

lemma interlaces_simsun_zero_one :
    StrictInterl (simsun 0) (simsun 1) :=
  by simpa [simsun_zero, simsun_one] using StrictInterl.refl (f := (1 : ℝ[X])) (by simp)

/-- Consecutive simsun descent polynomials satisfy `StrictInterl`. -/
theorem strictInterl_simsun_succ : ∀ n : Nat, StrictInterl (simsun n) (simsun (n + 1)) := by
  rr_row_strictInterl

theorem isRealRooted_simsun : ∀ n : Nat, ((simsun n) ≠ 0 ∧ (simsun n).Splits) :=
  fun n => ⟨by rr_row_ne_zero, by rr_row_splits⟩

theorem interlaces_simsun_succ_of_odd {n : Nat} (hodd : n % 2 = 1) :
    Interlaces (simsun n) (simsun (n + 1)) :=
  (strictInterl_simsun_succ n).toInterlaces
    (by rw [natDegree_simsun, natDegree_simsun]; lia)

/-- The descending prefix `[P_n, P_{n-1}, ..., P_0]` of the simsun sequence. -/
def simsunPrefix : Nat → List ℝ[X]
  | 0 => [simsun 0]
  | n + 1 => simsun (n + 1) :: simsunPrefix n

@[simp] lemma simsunPrefix_zero :
    simsunPrefix 0 = [simsun 0] := rfl

@[simp] lemma simsunPrefix_succ (n : Nat) :
    simsunPrefix (n + 1) = simsun (n + 1) :: simsunPrefix n := rfl

theorem isGeneralizedSturmSeq_simsunPrefix :
    ∀ n : Nat, IsGeneralizedSturmSeq (simsunPrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [simsunPrefix, IsGeneralizedSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [simsunPrefix, IsGeneralizedSturmSeq] using interlaces_simsun_zero_one
      | succ n =>
          simpa [simsunPrefix, IsGeneralizedSturmSeq] using
            And.intro (strictInterl_simsun_succ (n + 1)) ih

end RealRooted
