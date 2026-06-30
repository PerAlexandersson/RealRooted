import RealRooted.CombinatorialExamples.Common
import RealRooted.MaWang
import RealRooted.Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-!
# Simsun Descent Polynomials

Real-rootedness and Sturm-sequence facts for the simsun descent recurrence.
-/

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

@[simp] lemma simsun_one : simsun 1 = 1 := by
  simp [simsun, simsunCoeffA, simsunCoeffB]

lemma simsun_two : simsun 2 = 1 + X := by
  simp [simsun, simsunCoeffA, simsunCoeffB]

lemma simsun_three : simsun 3 = 1 + C (4 : ℝ) * X := by
  rw [simsun_succ, simsun_two]
  calc
    simsunCoeffA 2 * (1 + X) + simsunCoeffB * (1 + X).derivative
        = (1 + C (2 : ℝ) * X) * (1 + X) + X * (1 - C (2 : ℝ) * X) := by
            simp [simsunCoeffA, simsunCoeffB]
    _ = 1 + X + C (2 : ℝ) * X + C (2 : ℝ) * X * X + (X - C (2 : ℝ) * X * X) := by
          ring
    _ = 1 + X + C (2 : ℝ) * X + X := by
          ring
    _ = 1 + X * C (4 : ℝ) := by
          have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := (ofNat_def 2).symm
          have hC4 : (C (4 : ℝ) : ℝ[X]) = 4 := (ofNat_def 4).symm
          grind
    _ = 1 + C (4 : ℝ) * X := by
          simp

lemma coeff_simsunCoeffA_mul (n m : Nat) (p : ℝ[X]) :
    coeff (simsunCoeffA n * p) (m + 1) =
      coeff p (m + 1) + (n : ℝ) * coeff p m := by
  have hCX : coeff (C (n : ℝ) * X * p) (m + 1) =
      (n : ℝ) * coeff p m := by
    calc
      coeff (C (n : ℝ) * X * p) (m + 1)
          = coeff (C (n : ℝ) * (X * p)) (m + 1) := by rw [mul_assoc]
      _ = (n : ℝ) * coeff (X * p) (m + 1) := by simp
      _ = (n : ℝ) * coeff p m := by simp
  rw [simsunCoeffA, add_mul, one_mul, coeff_add, hCX]

lemma coeff_simsunCoeffB_mul_derivative (m : Nat) (p : ℝ[X]) :
    coeff (simsunCoeffB * p.derivative) (m + 1) =
      (m + 1 : ℝ) * coeff p (m + 1) - (2 * m : ℝ) * coeff p m := by
  have hB :
      simsunCoeffB * p.derivative =
        X * p.derivative - C (2 : ℝ) * X * X * p.derivative := by
    rw [simsunCoeffB]
    ring
  cases m with
  | zero =>
      rw [hB, coeff_sub]
      have h₁ : coeff (X * p.derivative) 1 = coeff p 1 := by
        calc
          coeff (X * p.derivative) 1 = coeff p.derivative 0 := by simp
          _ = coeff p 1 := by
              rw [coeff_derivative]
              ring
      have h₂ : coeff (C (2 : ℝ) * X * X * p.derivative) 1 = 0 := by
        calc
          coeff (C (2 : ℝ) * X * X * p.derivative) 1
              = (2 : ℝ) * coeff (X * (X * p.derivative)) 1 := by
                  rw [mul_assoc, mul_assoc, coeff_C_mul]
          _ = (2 : ℝ) * coeff (X * p.derivative) 0 := by simp
          _ = 0 := by simp
      simp_all
  | succ m =>
      rw [hB, coeff_sub]
      have h₁ : coeff (X * p.derivative) (m + 2) =
          (m + 2 : ℝ) * coeff p (m + 2) := by
        calc
          coeff (X * p.derivative) (m + 2) = coeff p.derivative (m + 1) := by simp
          _ = (((m + 1 : Nat) : ℝ) + 1) * coeff p (m + 1 + 1) := by
              rw [coeff_derivative]
              ring
          _ = (m + 2 : ℝ) * coeff p (m + 2) := by
              grind
      have h₂ : coeff (C (2 : ℝ) * X * X * p.derivative) (m + 2) =
          (2 * (m + 1) : ℝ) * coeff p (m + 1) := by
        calc
          coeff (C (2 : ℝ) * X * X * p.derivative) (m + 2)
              = (2 : ℝ) * coeff (X * (X * p.derivative)) (m + 2) := by
                  rw [mul_assoc, mul_assoc, coeff_C_mul]
          _ = (2 : ℝ) * coeff (X * p.derivative) (m + 1) := by simp
          _ = (2 : ℝ) * coeff p.derivative m := by simp
          _ = (2 : ℝ) * (((m : Nat) : ℝ) + 1) * coeff p (m + 1) := by
              rw [coeff_derivative]
              grind
          _ = (2 * (m + 1) : ℝ) * coeff p (m + 1) := by lia
      grind

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
      · intro m
        cases m with
        | zero =>
            simp [simsun_zero]
        | succ m =>
            rw [simsun_zero, coeff_one, if_neg (Nat.succ_ne_zero m)]
      · simp [simsun_zero]
      · intro m hm
        rw [simsun_zero, coeff_one]
        lia
  | 1 => by
      refine ⟨?_, ?_, ?_⟩
      · intro m
        cases m with
        | zero =>
            simp [simsun_one]
        | succ m =>
            rw [simsun_one, coeff_one, if_neg (Nat.succ_ne_zero m)]
      · simp [simsun_one]
      · intro m hm
        rw [simsun_one, coeff_one]
        lia
  | n + 2 => by
      rcases simsun_nonnegCoeffs_top_pos_and_above (n + 1) with
        ⟨hprev_nonneg, hprev_top, hprev_above⟩
      refine ⟨?_, ?_, ?_⟩
      · intro m
        cases m with
        | zero =>
            rw [coeff_simsun_zero]
            positivity
        | succ m =>
            rw [coeff_simsun_succ]
            by_cases hm : m ≤ (n + 1) / 2
            · have hm' : (2 : ℝ) * (m : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by
                exact_mod_cast (show 2 * m ≤ n + 1 by lia)
              have hscale : 0 ≤ (((n + 1 : Nat) : ℝ) - 2 * (m : ℝ)) := by
                nlinarith
              exact add_nonneg
                (mul_nonneg (by lia) (hprev_nonneg m))
                (mul_nonneg (by grind) (hprev_nonneg (m + 1)))
            · have hm' : (n + 1) / 2 < m := lt_of_not_ge hm
              have hm_zero : coeff (simsun (n + 1)) m = 0 := hprev_above m hm'
              have hm_succ_zero : coeff (simsun (n + 1)) (m + 1) = 0 := by
                grind
              simp [hm_zero, hm_succ_zero]
      · set k : Nat := (n + 2) / 2 - 1
        have hk_succ : k + 1 = (n + 2) / 2 := by
          lia
        rw [show (n + 2) / 2 = k + 1 by lia, coeff_simsun_succ]
        rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
        · have hk_eq : k = n / 2 := by
            lia
          have hprev_idx : (n + 1) / 2 = n / 2 := by
            lia
          have hprev_pos : 0 < coeff (simsun (n + 1)) k := by
            lia
          have hprev_zero : coeff (simsun (n + 1)) (k + 1) = 0 := by
            simp_all
          have hdouble : (2 : ℝ) * (k : ℝ) = (n : ℝ) := by
            exact_mod_cast (show 2 * k = n by lia)
          simp_all
        · have hk_eq : k = n / 2 := by
            lia
          have hk_top : k + 1 = (n + 1) / 2 := by
            lia
          have hprev_nonneg_k : 0 ≤ coeff (simsun (n + 1)) k :=
            hprev_nonneg k
          have hprev_pos : 0 < coeff (simsun (n + 1)) (k + 1) := by
            lia
          have hdouble : (2 : ℝ) * (k : ℝ) + 1 = (n : ℝ) := by
            exact_mod_cast (show 2 * k + 1 = n by lia)
          have hcast :
              (((n + 1 : Nat) : ℝ) - 2 * (k : ℝ)) = (n : ℝ) + 1 - 2 * (k : ℝ) := by
            lia
          have hscale_eq : (n : ℝ) + 1 - 2 * (k : ℝ) = 2 := by
            nlinarith
          have hlead_pos :
              0 < ((k : ℝ) + 2) * coeff (simsun (n + 1)) (k + 1) := by
            have hscale : 0 < (k : ℝ) + 2 := by grind
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
            rw [show k + 1 = k + 1 by lia, coeff_simsun_succ]
            have hk_succ_zero : coeff (simsun (n + 1)) (k + 1) = 0 := by
              grind
            by_cases hk : (n + 1) / 2 < k
            · simp_all
            · have hk_le : k ≤ (n + 1) / 2 := le_of_not_gt hk
              have hk_ge : (n + 2) / 2 ≤ k := by
                lia
              have hk_eq : k = (n + 1) / 2 := by
                lia
              have hdouble : (2 : ℝ) * (k : ℝ) = (((n + 1 : Nat) : ℝ)) := by
                exact_mod_cast (show 2 * k = n + 1 by lia)
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
  rcases coeff_simsun_top_pos_and_above n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm))
    (by grind)

lemma simsun_nonzero (n : Nat) :
    simsun n ≠ 0 := by
  rcases coeff_simsun_top_pos_and_above n with ⟨htop, _⟩
  exact fun h0 => by simp [h0] at htop

lemma interlaces_derivative_simsun_three :
    Interlaces (simsun 3).derivative (simsun 3) := by
  have hlin : Interlaces (1 : ℝ[X]) (1 + C (4 : ℝ) * X) := by
    refine interlaces_one_linear ?_
    simpa [add_comm] using
      (Polynomial.natDegree_linear (a := (4 : ℝ)) (b := (1 : ℝ)) (by simp))
  have hprec : Prec (1 : ℝ[X]) (1 + C (4 : ℝ) * X) := hlin.toPrec
  have hprecC : Prec (C (4 : ℝ) * (1 : ℝ[X])) (1 + C (4 : ℝ) * X) :=
    prec_C_mul_left hprec (by simp)
  have hInter : Interlaces (C (4 : ℝ) * (1 : ℝ[X])) (1 + C (4 : ℝ) * X) :=
    hprecC.toInterlaces (by
      simpa [add_comm] using
        (Polynomial.natDegree_linear (a := (4 : ℝ)) (b := (1 : ℝ)) (by simp)).symm)
  simpa [simsun_three] using hInter

lemma simsun_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (simsun n) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff, natDegree_simsun]
  exact (coeff_simsun_top_pos_and_above n).1

lemma roots_nonpos_simsun_of_isRealRooted {n : Nat} (hrr : (simsun n).Splits) :
    ∀ r ∈ (simsun n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (simsun_nonnegCoeffs n)

lemma interlaces_simsun_zero_one :
    Prec (simsun 0) (simsun 1) :=
  by simpa [simsun_zero, simsun_one] using prec_refl (f := (1 : ℝ[X])) (by simp)

lemma interlaces_simsun_one_two :
    Interlaces (simsun 1) (simsun 2) := by
  simpa [simsun_one, simsun_two] using
    interlaces_one_linear (p := (1 + X : ℝ[X])) (by
      simpa [add_comm] using
        (Polynomial.natDegree_linear (a := (1 : ℝ)) (b := (1 : ℝ)) (by simp)))

lemma interlaces_derivative_simsun :
    ∀ n : Nat, 2 ≤ n → (simsun n).Splits →
      Interlaces (simsun n).derivative (simsun n)
  | 0, hn, _ => by
      lia
  | 1, hn, _ => by
      lia
  | 2, _, _ => by
      simpa [simsun_two] using
        interlaces_one_linear (p := (1 + X : ℝ[X])) (by
          simpa [add_comm] using
            (Polynomial.natDegree_linear (a := (1 : ℝ)) (b := (1 : ℝ)) (by simp)))
  | 3, _, _ => by
      simpa using interlaces_derivative_simsun_three
  | n + 4, _, hrr => by
      apply derivative_interlaces hrr
      rw [natDegree_simsun]
      lia

lemma eval_simsunCoeffB_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    simsunCoeffB.eval r ≤ 0 := by
  unfold simsunCoeffB
  rw [eval_mul, eval_X, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  have hfac : 0 ≤ 1 - 2 * r := by
    linarith
  nlinarith

/-- Consecutive simsun descent polynomials satisfy `Prec`. -/
theorem prec_simsun_succ : ∀ n : Nat, Prec (simsun n) (simsun (n + 1))
  | 0 => interlaces_simsun_zero_one
  | 1 => interlaces_simsun_one_two.toPrec
  | n + 2 => by
    have hInter :
        Interlaces (simsun (n + 2)).derivative (simsun (n + 2)) :=
      interlaces_derivative_simsun (n + 2) (by lia) (prec_simsun_succ (n + 1)).2.1.2
    have hg_pos : HasPosLeadingCoeff (simsun (n + 2)).derivative :=
      (simsun_posLeadingCoeff (n + 2)).derivative (by rw [natDegree_simsun]; lia)
    have hNext_eq :
        simsunCoeffA (n + 2) * simsun (n + 2) +
          simsunCoeffB * (simsun (n + 2)).derivative =
        simsun (n + 3) :=
      (simsun_succ (n + 2)).symm
    have hF_pos :
        HasPosLeadingCoeff
          (simsunCoeffA (n + 2) * simsun (n + 2) +
            simsunCoeffB * (simsun (n + 2)).derivative) := by
      rw [hNext_eq]
      exact simsun_posLeadingCoeff (n + 3)
    have hdeg_lo :
        (simsun (n + 2)).natDegree ≤
          (simsunCoeffA (n + 2) * simsun (n + 2) +
            simsunCoeffB * (simsun (n + 2)).derivative).natDegree := by
      rw [hNext_eq, natDegree_simsun, natDegree_simsun]
      lia
    have hdeg_hi :
        (simsunCoeffA (n + 2) * simsun (n + 2) +
            simsunCoeffB * (simsun (n + 2)).derivative).natDegree ≤
          (simsun (n + 2)).natDegree + 1 := by
      rw [hNext_eq, natDegree_simsun, natDegree_simsun]
      lia
    have hb_nonpos :
        ∀ r, (simsun (n + 2)).IsRoot r → simsunCoeffB.eval r ≤ 0 := by
      intro r hr
      have hr_nonpos :
          r ≤ 0 := roots_nonpos_simsun_of_isRealRooted (prec_simsun_succ (n + 1)).2.1.2 r
            ((mem_roots (prec_simsun_succ (n + 1)).2.1.1).mpr hr)
      exact eval_simsunCoeffB_nonpos_of_nonpos hr_nonpos
    rw [← hNext_eq]
    exact
      prec_of_interlaces_evalCoeff_nonpos
        (f := simsun (n + 2))
        (g := (simsun (n + 2)).derivative)
        (a := simsunCoeffA (n + 2))
        (b := simsunCoeffB)
        hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos

theorem isRealRooted_simsun : ∀ n : Nat, ((simsun n) ≠ 0 ∧ (simsun n).Splits)
  | 0 => by simp
  | n + 1 => (prec_simsun_succ n).2.1

theorem interlaces_simsun_succ_of_odd {n : Nat} (hodd : n % 2 = 1) :
    Interlaces (simsun n) (simsun (n + 1)) :=
  (prec_simsun_succ n).toInterlaces
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
            And.intro (prec_simsun_succ (n + 1)) ih

end RealRooted
