import RealRooted.CombinatorialExamples.Common
import RealRooted.MaWang
import Mathlib.Tactic

/-!
# Touchard Polynomials

Real-rootedness and Sturm-sequence facts for the Touchard polynomial
recurrence.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The Touchard polynomial sequence, defined recursively from
`T_{n+1}(X) = X * T_n(X) + X * T'_n(X)` with `T_0(X) = 1`. -/
def touchard : Nat → ℝ[X]
  | 0 => 1
  | n + 1 => X * touchard n + X * (touchard n).derivative

@[simp] lemma touchard_zero : touchard 0 = 1 := rfl

lemma touchard_succ (n : Nat) :
    touchard (n + 1) = X * touchard n + X * (touchard n).derivative := rfl

lemma touchard_one : touchard 1 = X := by
  simp [touchard]

lemma touchard_two : touchard 2 = X + X ^ 2 := by
  rw [touchard_succ, touchard_one]
  simp [pow_two]
  ring

lemma coeff_touchard_succ (n m : Nat) :
    coeff (touchard (n + 1)) (m + 1) =
      coeff (touchard n) m + (m + 1 : ℝ) * coeff (touchard n) (m + 1) := by
  rw [touchard_succ, coeff_add, coeff_X_mul, coeff_X_mul, coeff_derivative]
  ring

lemma coeff_touchard_top_and_above :
    ∀ n : Nat, coeff (touchard n) n = 1 ∧ ∀ m > n, coeff (touchard n) m = 0
  | 0 => by
      constructor
      · simp [touchard_zero]
      · intro m hm
        rw [touchard_zero, coeff_one, if_neg hm.ne']
  | n + 1 => by
      rcases coeff_touchard_top_and_above n with ⟨htop, habove⟩
      constructor
      · rw [show n + 1 = n + 0 + 1 by lia, coeff_touchard_succ]
        simp_all
      · intro m hm
        cases m with
        | zero =>
            lia
        | succ k =>
            have hk0 : n + 1 < k + 1 := hm
            rw [show k + 1 = k + 0 + 1 by lia, coeff_touchard_succ]
            grind

lemma natDegree_touchard (n : Nat) :
    (touchard n).natDegree = n := by
  rcases coeff_touchard_top_and_above n with ⟨htop, habove⟩
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)
  · simp [htop]

lemma monic_touchard (n : Nat) :
    (touchard n).Monic := by
  rcases coeff_touchard_top_and_above n with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_touchard]
  lia

lemma touchard_ne_zero (n : Nat) :
    touchard n ≠ 0 :=
  (monic_touchard n).ne_zero

lemma touchard_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (touchard n) := by
  unfold HasPosLeadingCoeff
  rw [(monic_touchard n).leadingCoeff]
  norm_num

lemma touchard_nonnegCoeffs : ∀ n : Nat, HasNonnegCoeffs (touchard n)
  | 0 => by
      intro m
      cases m with
      | zero =>
          simp [touchard_zero]
      | succ m =>
          rw [touchard_zero, coeff_one, if_neg (Nat.succ_ne_zero m)]
  | n + 1 => by
      intro m
      cases m with
      | zero =>
          simp [touchard_succ]
      | succ m =>
          rw [coeff_touchard_succ]
          exact add_nonneg (touchard_nonnegCoeffs n m)
            (mul_nonneg (by grind) (touchard_nonnegCoeffs n (m + 1)))

lemma roots_nonpos_touchard_of_isRealRooted {n : Nat} (hrr : (touchard n).Splits) :
    ∀ r ∈ (touchard n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (touchard_nonnegCoeffs n)

lemma interlaces_touchard_zero_one :
    Interlaces (touchard 0) (touchard 1) :=
  by simpa [touchard_zero, touchard_one] using interlaces_one_linear (p := X) (by simp)

lemma prec_touchard_one_two :
    Prec (touchard 1) (touchard 2) := by
  have hInter : Interlaces (touchard 0) (touchard 1) := interlaces_touchard_zero_one
  have h0_pos : HasPosLeadingCoeff (touchard 0) := touchard_posLeadingCoeff 0
  have hF_eq : X * touchard 1 + X * touchard 0 = touchard 2 := by
    rw [touchard_two, touchard_one, touchard_zero]
    ring
  have hF_pos : HasPosLeadingCoeff (X * touchard 1 + X * touchard 0) := by
    rw [hF_eq]
    exact touchard_posLeadingCoeff 2
  have hdeg_lo :
      (touchard 1).natDegree ≤
        (X * touchard 1 + X * touchard 0).natDegree := by
    rw [hF_eq, natDegree_touchard, natDegree_touchard]
    lia
  have hdeg_hi :
      (X * touchard 1 + X * touchard 0).natDegree ≤
        (touchard 1).natDegree + 1 := by
    rw [hF_eq, natDegree_touchard, natDegree_touchard]
  have hb_nonpos : ∀ r, (touchard 1).IsRoot r → X.eval r ≤ 0 := by
    intro r hr
    have hr_zero : r = 0 := by
      simpa [touchard_one, Polynomial.IsRoot.def] using hr
    simp [hr_zero]
  rw [← hF_eq]
  exact
    prec_of_interlaces_evalCoeff_nonpos
      (f := touchard 1)
      (g := touchard 0)
      (a := X)
      (b := X)
      hInter h0_pos hF_pos hdeg_lo hdeg_hi hb_nonpos

/-- Consecutive Touchard polynomials satisfy `Prec`, hence are real-rooted. -/
theorem prec_touchard_succ : ∀ n : Nat, Prec (touchard n) (touchard (n + 1))
  | 0 => interlaces_touchard_zero_one.toPrec
  | 1 => prec_touchard_one_two
  | n + 2 => by
      have hprev : Prec (touchard (n + 1)) (touchard (n + 2)) :=
        prec_touchard_succ (n + 1)
      have hdegf : 2 ≤ (touchard (n + 2)).natDegree := by
        rw [natDegree_touchard]
        lia
      have hInter :
          Interlaces (touchard (n + 2)).derivative (touchard (n + 2)) :=
        derivative_interlaces hprev.2.1.2 hdegf
      have hg_pos : HasPosLeadingCoeff (touchard (n + 2)).derivative :=
        (touchard_posLeadingCoeff (n + 2)).derivative (by
          lia)
      have hNext_eq :
          X * touchard (n + 2) + X * (touchard (n + 2)).derivative = touchard (n + 3) :=
        (touchard_succ (n + 2)).symm
      have hF_pos :
          HasPosLeadingCoeff
            (X * touchard (n + 2) + X * (touchard (n + 2)).derivative) := by
        rw [hNext_eq]
        exact touchard_posLeadingCoeff (n + 3)
      have hdeg_lo :
          (touchard (n + 2)).natDegree ≤
            (X * touchard (n + 2) + X * (touchard (n + 2)).derivative).natDegree := by
        rw [hNext_eq, natDegree_touchard, natDegree_touchard]
        lia
      have hdeg_hi :
          (X * touchard (n + 2) + X * (touchard (n + 2)).derivative).natDegree ≤
            (touchard (n + 2)).natDegree + 1 := by
        rw [hNext_eq, natDegree_touchard, natDegree_touchard]
      have hb_nonpos : ∀ r, (touchard (n + 2)).IsRoot r → X.eval r ≤ 0 := by
        intro r hr
        have hr_nonpos : r ≤ 0 :=
          roots_nonpos_touchard_of_isRealRooted hprev.2.1.2 r ((mem_roots hprev.2.1.1).mpr hr)
        simp_all
      rw [← hNext_eq]
      exact
        prec_of_interlaces_evalCoeff_nonpos
          (f := touchard (n + 2))
          (g := (touchard (n + 2)).derivative)
          (a := X)
          (b := X)
          hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos

theorem interlaces_touchard_succ (n : Nat) :
    Interlaces (touchard n) (touchard (n + 1)) :=
  (prec_touchard_succ n).toInterlaces (by simp [natDegree_touchard])

theorem isRealRooted_touchard : ∀ n : Nat, ((touchard n) ≠ 0 ∧ (touchard n).Splits)
  | 0 => by simp
  | n + 1 => (prec_touchard_succ n).2.1

/-- The descending prefix `[T_n, T_{n-1}, ..., T_0]` of the Touchard sequence. -/
def touchardPrefix : Nat → List ℝ[X]
  | 0 => [touchard 0]
  | n + 1 => touchard (n + 1) :: touchardPrefix n

@[simp] lemma touchardPrefix_zero :
    touchardPrefix 0 = [touchard 0] := rfl

@[simp] lemma touchardPrefix_succ (n : Nat) :
    touchardPrefix (n + 1) = touchard (n + 1) :: touchardPrefix n := rfl

theorem isSturmSeq_touchardPrefix :
    ∀ n : Nat, IsSturmSeq (touchardPrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [touchardPrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [touchardPrefix, IsSturmSeq] using interlaces_touchard_zero_one
      | succ k =>
          simpa [touchardPrefix, IsSturmSeq] using
            And.intro (interlaces_touchard_succ (k + 1)) ih

end RealRooted
