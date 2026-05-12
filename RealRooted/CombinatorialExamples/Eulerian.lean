/- 
# Real-rootedness of the Eulerian tilde polynomials

This file formalizes the recurrence

`P_{n+1} = X * (C (n+2) * P_n + (1 - X) * P'_n)`

with `P_0 = X`. The proof strategy is the intended human induction:
if `P_n` is real-rooted, then the affine block preceding the outer `X`
interlaces `P_n`, hence `P_n ≪ P_{n+1}` and `P_{n+1}` is real-rooted.
-/
import RealRooted.Basic
import RealRooted.Derivative
import RealRooted.Wagner
import RealRooted.AffineDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace RealRooted

/-- The shifted Eulerian polynomial sequence in the standard indexing
with `P_0 = X`. -/
def eulerianTilde : Nat → ℝ[X]
  | 0 => X
  | n + 1 =>
      X * (C (n + 2 : ℝ) * eulerianTilde n +
        (1 - X) * (eulerianTilde n).derivative)

@[simp] lemma eulerianTilde_zero : eulerianTilde 0 = X := rfl

lemma eulerianTilde_recurrence (n : Nat) :
    eulerianTilde (n + 1) =
      X * (C (n + 2 : ℝ) * eulerianTilde n +
        (1 - X) * (eulerianTilde n).derivative) := rfl

lemma eulerianTilde_one : eulerianTilde 1 = X + X ^ 2 := by
  rw [eulerianTilde_recurrence 0]
  have htwo : (C (2 : ℝ) : ℝ[X]) = (2 : ℝ[X]) := by
    ext n <;> cases n <;> simp
  simp [eulerianTilde_zero, pow_two]
  rw [htwo]
  ring

/-- The affine derivative block appearing in the Eulerian recurrence. -/
def affineEulerianTilde (n : Nat) : ℝ[X] :=
  C (n + 2 : ℝ) * eulerianTilde n + (1 - X) * (eulerianTilde n).derivative

lemma eulerianTilde_succ_eq_X_mul_affineEulerianTilde (n : Nat) :
    eulerianTilde (n + 1) = X * affineEulerianTilde n := by
  rw [eulerianTilde_recurrence, affineEulerianTilde]

lemma coeff_one_sub_X_mul_derivative (p : ℝ[X]) (m : Nat) :
    coeff ((1 - X) * p.derivative) m =
      ((m + 1 : ℝ) * coeff p (m + 1)) - ((m : ℝ) * coeff p m) := by
  cases m with
  | zero =>
      simp [coeff_derivative]
  | succ m =>
      rw [sub_mul, one_mul, coeff_sub, coeff_X_mul, coeff_derivative, coeff_derivative]
      norm_num
      ring

lemma coeff_eulerianTilde_succ (n m : Nat) :
    coeff (eulerianTilde (n + 1)) (m + 1) =
      ((n + 2 : ℝ) - m) * coeff (eulerianTilde n) m +
      (m + 1 : ℝ) * coeff (eulerianTilde n) (m + 1) := by
  rw [eulerianTilde_recurrence, coeff_X_mul]
  simp [coeff_one_sub_X_mul_derivative]
  have hC :
      (C (n + 2 : ℝ) * eulerianTilde n).coeff m =
        (n + 2 : ℝ) * (eulerianTilde n).coeff m := by
    simpa using
      (coeff_C_mul (n := m) (a := (n + 2 : ℝ)) (p := eulerianTilde n))
  have hCpoly : ((n : ℝ[X]) + C 2) = C (n + 2 : ℝ) := by
    simp
  rw [hCpoly, hC]
  ring

lemma coeff_eulerianTilde_top_and_above :
    ∀ n : Nat,
      coeff (eulerianTilde n) (n + 1) = 1 ∧
      ∀ m > n + 1, coeff (eulerianTilde n) m = 0
  | 0 => by
      constructor
      · simp [eulerianTilde_zero, coeff_X]
      · intro m hm
        have hm1 : 1 < m := by simpa using hm
        simp [eulerianTilde_zero, coeff_X, Nat.ne_of_lt hm1]
  | n + 1 => by
      rcases coeff_eulerianTilde_top_and_above n with ⟨htop, habove⟩
      constructor
      · rw [coeff_eulerianTilde_succ n (n + 1)]
        have hzero : coeff (eulerianTilde n) (n + 2) = 0 :=
          habove (n + 2) (by omega)
        rw [hzero, htop]
        norm_num
      · intro m hm
        cases m with
        | zero =>
            omega
        | succ m =>
            have hzero₁ : coeff (eulerianTilde n) m = 0 := by
              apply habove
              omega
            have hzero₂ : coeff (eulerianTilde n) (m + 1) = 0 := by
              apply habove
              omega
            rw [coeff_eulerianTilde_succ n m]
            simp [hzero₁, hzero₂]

lemma natDegree_eulerianTilde (n : Nat) :
    (eulerianTilde n).natDegree = n + 1 := by
  rcases coeff_eulerianTilde_top_and_above n with ⟨htop, habove⟩
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm)
  · rw [htop]
    norm_num

lemma monic_eulerianTilde (n : Nat) :
    (eulerianTilde n).Monic := by
  rcases coeff_eulerianTilde_top_and_above n with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_eulerianTilde]
  exact htop

lemma eulerianTilde_ne_zero (n : Nat) :
    eulerianTilde n ≠ 0 :=
  (monic_eulerianTilde n).ne_zero

lemma eulerianTilde_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (eulerianTilde n) := by
  unfold HasPosLeadingCoeff
  rw [(monic_eulerianTilde n).leadingCoeff]
  norm_num

lemma eulerianTilde_nonnegCoeffs : ∀ n : Nat, HasNonnegCoeffs (eulerianTilde n)
  | 0 => by
      intro m
      by_cases hm : m = 1
      · subst hm
        simp [eulerianTilde_zero, coeff_X]
      · have hm' : 1 ≠ m := by simpa [eq_comm] using hm
        simp [eulerianTilde_zero, coeff_X, hm']
  | n + 1 => by
      intro m
      cases m with
      | zero =>
          rw [eulerianTilde_recurrence]
          simp
      | succ m =>
          rw [coeff_eulerianTilde_succ n m]
          by_cases hm : m ≤ n + 1
          · have hcoeff_m : 0 ≤ coeff (eulerianTilde n) m :=
              eulerianTilde_nonnegCoeffs n m
            have hcoeff_succ : 0 ≤ coeff (eulerianTilde n) (m + 1) :=
              eulerianTilde_nonnegCoeffs n (m + 1)
            have hnm : 0 ≤ (n + 2 : ℝ) - m := by
              have hm' : (m : ℝ) ≤ n + 2 := by
                exact_mod_cast (Nat.le_trans hm (Nat.le_succ _))
              linarith
            exact add_nonneg (mul_nonneg hnm hcoeff_m) (mul_nonneg (by positivity) hcoeff_succ)
          · have hm' : n + 1 < m := lt_of_not_ge hm
            rcases coeff_eulerianTilde_top_and_above n with ⟨_, habove⟩
            have hcoeff_m : coeff (eulerianTilde n) m = 0 := by
              apply habove
              omega
            have hcoeff_succ : coeff (eulerianTilde n) (m + 1) = 0 := by
              apply habove
              omega
            simp [hcoeff_m, hcoeff_succ]

lemma roots_nonpos_eulerianTilde_of_isRealRooted {n : Nat}
    (hrr : IsRealRooted (eulerianTilde n)) :
    ∀ r ∈ (eulerianTilde n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (eulerianTilde_nonnegCoeffs n)

lemma prec_affineEulerianTilde {n : Nat}
    (hrr : IsRealRooted (eulerianTilde n)) :
    Prec (affineEulerianTilde n) (eulerianTilde n) := by
  rw [affineEulerianTilde]
  exact prec_affine_derivative' hrr (by rw [natDegree_eulerianTilde]; omega)
    (eulerianTilde_posLeadingCoeff n)
    (roots_nonpos_eulerianTilde_of_isRealRooted hrr)
    (by
      have hlt : (((eulerianTilde n).natDegree : ℝ)) < n + 2 := by
        rw [natDegree_eulerianTilde]
        exact_mod_cast (Nat.lt_succ_self (n + 1))
      exact hlt)

lemma affineEulerianTilde_nonnegCoeffs (n : Nat) :
    HasNonnegCoeffs (affineEulerianTilde n) := by
  intro m
  rw [affineEulerianTilde, coeff_add]
  rw [show coeff (C (n + 2 : ℝ) * eulerianTilde n) m =
      (n + 2 : ℝ) * coeff (eulerianTilde n) m by
      simpa using
        (coeff_C_mul (n := m) (a := (n + 2 : ℝ)) (p := eulerianTilde n))]
  rw [coeff_one_sub_X_mul_derivative]
  by_cases hm : m ≤ n + 1
  · have hcoeff_m : 0 ≤ coeff (eulerianTilde n) m :=
      eulerianTilde_nonnegCoeffs n m
    have hcoeff_succ : 0 ≤ coeff (eulerianTilde n) (m + 1) :=
      eulerianTilde_nonnegCoeffs n (m + 1)
    have hnm : 0 ≤ (n + 2 : ℝ) - m := by
      have hm' : (m : ℝ) ≤ n + 2 := by
        exact_mod_cast (Nat.le_trans hm (Nat.le_succ _))
      linarith
    nlinarith
  · have hm' : n + 1 < m := lt_of_not_ge hm
    rcases coeff_eulerianTilde_top_and_above n with ⟨_, habove⟩
    have hcoeff_m : coeff (eulerianTilde n) m = 0 := by
      apply habove
      omega
    have hcoeff_succ : coeff (eulerianTilde n) (m + 1) = 0 := by
      apply habove
      omega
    simp [hcoeff_m, hcoeff_succ]

lemma roots_nonpos_affineEulerianTilde_of_isRealRooted {n : Nat}
    (hrr : IsRealRooted (eulerianTilde n)) :
    ∀ r ∈ (affineEulerianTilde n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs (prec_affineEulerianTilde hrr).1
    (affineEulerianTilde_nonnegCoeffs n)

lemma natDegree_affineEulerianTilde (n : Nat) :
    (affineEulerianTilde n).natDegree = (eulerianTilde n).natDegree := by
  rw [affineEulerianTilde]
  refine natDegree_affineDeriv (eulerianTilde_ne_zero n) ?_ ?_
  · rw [natDegree_eulerianTilde]
    omega
  · rw [natDegree_eulerianTilde]
    norm_num

/-- Once the affine block is known to precede `P_n`, the outer `X` factor in the
recurrence gives `P_n ≪ P_{n+1}`. -/
lemma prec_eulerianTilde_succ_of_prec_affine {n : Nat}
    (haff : Prec (affineEulerianTilde n) (eulerianTilde n)) :
    Prec (eulerianTilde n) (eulerianTilde (n + 1)) := by
  have haff_nonpos :
      ∀ r ∈ (affineEulerianTilde n).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs haff.1 (affineEulerianTilde_nonnegCoeffs n)
  have hp_nonpos :
      ∀ r ∈ (eulerianTilde n).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs haff.2.1 (eulerianTilde_nonnegCoeffs n)
  have hmain :
      Prec (eulerianTilde n) (X * affineEulerianTilde n) :=
    prec_sameDegree_to_prec_mul_X_of_roots_nonpos haff
      (natDegree_affineEulerianTilde n) haff_nonpos hp_nonpos
  simpa [eulerianTilde_succ_eq_X_mul_affineEulerianTilde n] using hmain

/-- Main induction theorem: consecutive Eulerian tilde polynomials interlace in
the oriented `Prec` sense. The induction hypothesis supplies real-rootedness of
`P_n` as the right-hand half of `Prec P_{n-1} P_n`. -/
theorem prec_eulerianTilde_succ : ∀ n : Nat,
    Prec (eulerianTilde n) (eulerianTilde (n + 1))
  | 0 => by
      have hrr0 : IsRealRooted (eulerianTilde 0) := by
        apply isRealRooted_of_degree_one
        simp [eulerianTilde_zero]
      exact prec_eulerianTilde_succ_of_prec_affine
        (n := 0) (prec_affineEulerianTilde (n := 0) hrr0)
  | n + 1 => by
      have hprev : Prec (eulerianTilde n) (eulerianTilde (n + 1)) :=
        prec_eulerianTilde_succ n
      exact prec_eulerianTilde_succ_of_prec_affine
        (n := n + 1) (prec_affineEulerianTilde (n := n + 1) hprev.2.1)

/-- Every Eulerian tilde polynomial is real-rooted, obtained as the
right-hand component of the interlacing induction. -/
theorem isRealRooted_eulerianTilde : ∀ n : Nat,
    IsRealRooted (eulerianTilde n)
  | 0 => by
      apply isRealRooted_of_degree_one
      simp [eulerianTilde_zero]
  | n + 1 => by
      exact (prec_eulerianTilde_succ n).2.1

theorem interlaces_eulerianTilde_succ (n : Nat) :
    Interlaces (eulerianTilde n) (eulerianTilde (n + 1)) := by
  apply (prec_eulerianTilde_succ n).toInterlaces
  rw [natDegree_eulerianTilde, natDegree_eulerianTilde]

/-- The descending prefix `[P_n, P_{n-1}, ..., P_0]` of the Eulerian tilde
sequence. -/
def eulerianTildePrefix : Nat → List ℝ[X]
  | 0 => [eulerianTilde 0]
  | n + 1 => eulerianTilde (n + 1) :: eulerianTildePrefix n

@[simp] lemma eulerianTildePrefix_zero : eulerianTildePrefix 0 = [eulerianTilde 0] := rfl

@[simp] lemma eulerianTildePrefix_succ (n : Nat) :
    eulerianTildePrefix (n + 1) =
      eulerianTilde (n + 1) :: eulerianTildePrefix n := rfl

theorem isSturmSeq_eulerianTildePrefix :
    ∀ n : Nat, IsSturmSeq (eulerianTildePrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [eulerianTildePrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [eulerianTildePrefix, IsSturmSeq] using
            interlaces_eulerianTilde_succ 0
      | succ n =>
          simpa [eulerianTildePrefix, IsSturmSeq] using
            And.intro (interlaces_eulerianTilde_succ (n + 1)) ih

end RealRooted
