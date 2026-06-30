import RealRooted.AffineDerivative
import RealRooted.Basic
import RealRooted.Derivative
import RealRooted.Mathlib.Algebra.Polynomial.Basic
import RealRooted.Wagner
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# Eulerian Tilde Polynomials

Real-rootedness and Sturm-sequence facts for the shifted Eulerian recurrence,
using the affine derivative block before the outer `X` factor.
-/

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
  have htwo : (C (2 : ℝ) : ℝ[X]) = (2 : ℝ[X]) := (ofNat_def 2).symm
  simp only [CharP.cast_eq_zero, zero_add, eulerianTilde_zero, derivative_X, mul_one]
  grind

/-- The affine derivative block appearing in the Eulerian recurrence. -/
def affineEulerianTilde (n : Nat) : ℝ[X] :=
  C (n + 2 : ℝ) * eulerianTilde n + (1 - X) * (eulerianTilde n).derivative

lemma eulerianTilde_succ_eq_X_mul_affineEulerianTilde (n : Nat) :
    eulerianTilde (n + 1) = X * affineEulerianTilde n := by
  rw [eulerianTilde_recurrence, affineEulerianTilde]

lemma coeff_eulerianTilde_succ (n m : Nat) :
    coeff (eulerianTilde (n + 1)) (m + 1) =
      ((n + 2 : ℝ) - m) * coeff (eulerianTilde n) m +
      (m + 1 : ℝ) * coeff (eulerianTilde n) (m + 1) := by
  rw [eulerianTilde_recurrence, coeff_X_mul]
  simp only [map_add, map_natCast, coeff_add, coeff_one_sub_X_mul_derivative]
  have hC :
      (C (n + 2 : ℝ) * eulerianTilde n).coeff m =
        (n + 2 : ℝ) * (eulerianTilde n).coeff m := by
    grind
  have hCpoly : ((n : ℝ[X]) + C 2) = C (n + 2 : ℝ) := by
    simp
  grind

lemma coeff_eulerianTilde_top_and_above :
    ∀ n : Nat,
      coeff (eulerianTilde n) (n + 1) = 1 ∧
      ∀ m > n + 1, coeff (eulerianTilde n) m = 0
  | 0 => by
      constructor
      · simp
      · intro m hm
        have hm1 : 1 < m := by lia
        simp [eulerianTilde_zero, coeff_X, Nat.ne_of_lt hm1]
  | n + 1 => by
      rcases coeff_eulerianTilde_top_and_above n with ⟨htop, habove⟩
      constructor
      · rw [coeff_eulerianTilde_succ n (n + 1)]
        grind
      · intro m hm
        cases m with
        | zero =>
            lia
        | succ m =>
            have hzero₁ : coeff (eulerianTilde n) m = 0 := by
              simp_all
            have hzero₂ : coeff (eulerianTilde n) (m + 1) = 0 := by
              grind
            rw [coeff_eulerianTilde_succ n m]
            simp [hzero₁, hzero₂]

lemma natDegree_eulerianTilde (n : Nat) :
    (eulerianTilde n).natDegree = n + 1 := by
  rcases coeff_eulerianTilde_top_and_above n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm))
    (by simp_all)

lemma monic_eulerianTilde (n : Nat) :
    (eulerianTilde n).Monic := by
  rcases coeff_eulerianTilde_top_and_above n with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_eulerianTilde]
  lia

lemma eulerianTilde_ne_zero (n : Nat) :
    eulerianTilde n ≠ 0 :=
  (monic_eulerianTilde n).ne_zero

lemma eulerianTilde_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (eulerianTilde n) := by
  simp [HasPosLeadingCoeff, (monic_eulerianTilde n).leadingCoeff]

lemma eulerianTilde_nonnegCoeffs : ∀ n : Nat, HasNonnegCoeffs (eulerianTilde n)
  | 0 => by
      intro m
      by_cases hm : m = 1
      · simp_all
      · have hm' : 1 ≠ m := by lia
        simp [eulerianTilde_zero, coeff_X, hm']
  | n + 1 => by
      rintro (_ | m)
      · rw [eulerianTilde_recurrence]
        simp
      · rw [coeff_eulerianTilde_succ n m]
        by_cases hm : m ≤ n + 1
        · have hcoeff_m : 0 ≤ coeff (eulerianTilde n) m :=
            eulerianTilde_nonnegCoeffs n m
          have hcoeff_succ : 0 ≤ coeff (eulerianTilde n) (m + 1) :=
            eulerianTilde_nonnegCoeffs n (m + 1)
          have hnm : 0 ≤ (n + 2 : ℝ) - m := by
            nlinarith [show (m : ℝ) ≤ n + 2 by
              exact_mod_cast Nat.le_trans hm (Nat.le_succ _)]
          exact add_nonneg (mul_nonneg hnm hcoeff_m) (mul_nonneg (by grind) hcoeff_succ)
        · have hm' : n + 1 < m := lt_of_not_ge hm
          rcases coeff_eulerianTilde_top_and_above n with ⟨_, habove⟩
          have hcoeff_m : coeff (eulerianTilde n) m = 0 := by
            simp_all
          have hcoeff_succ : coeff (eulerianTilde n) (m + 1) = 0 := by
            grind
          simp [hcoeff_m, hcoeff_succ]

lemma roots_nonpos_eulerianTilde_of_isRealRooted {n : Nat} (hrr : (eulerianTilde n).Splits) :
    ∀ r ∈ (eulerianTilde n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (eulerianTilde_nonnegCoeffs n)

lemma prec_affineEulerianTilde {n : Nat} (hrr : (eulerianTilde n).Splits) :
    Prec (affineEulerianTilde n) (eulerianTilde n) := by
  rw [affineEulerianTilde]
  exact prec_affine_derivative' hrr (by simp [natDegree_eulerianTilde])
    (eulerianTilde_posLeadingCoeff n)
    (roots_nonpos_eulerianTilde_of_isRealRooted hrr)
    (by
      have hlt : (((eulerianTilde n).natDegree : ℝ)) < n + 2 := by
        rw [natDegree_eulerianTilde]
        simp
      lia)

lemma affineEulerianTilde_nonnegCoeffs (n : Nat) :
    HasNonnegCoeffs (affineEulerianTilde n) := by
  intro m
  rw [affineEulerianTilde, coeff_add, coeff_C_mul]
  rw [coeff_one_sub_X_mul_derivative]
  by_cases hm : m ≤ n + 1
  · have hcoeff_m : 0 ≤ coeff (eulerianTilde n) m :=
      eulerianTilde_nonnegCoeffs n m
    have hcoeff_succ : 0 ≤ coeff (eulerianTilde n) (m + 1) :=
      eulerianTilde_nonnegCoeffs n (m + 1)
    have hnm : 0 ≤ (n + 2 : ℝ) - m := by
      nlinarith [show (m : ℝ) ≤ n + 2 by
        exact_mod_cast Nat.le_trans hm (Nat.le_succ _)]
    nlinarith
  · have hm' : n + 1 < m := lt_of_not_ge hm
    rcases coeff_eulerianTilde_top_and_above n with ⟨_, habove⟩
    have hcoeff_m : coeff (eulerianTilde n) m = 0 := by
      simp_all
    have hcoeff_succ : coeff (eulerianTilde n) (m + 1) = 0 := by
      grind
    simp [hcoeff_m, hcoeff_succ]

lemma roots_nonpos_affineEulerianTilde_of_isRealRooted {n : Nat} (hrr : (eulerianTilde n).Splits) :
    ∀ r ∈ (affineEulerianTilde n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs (prec_affineEulerianTilde hrr).1.2
    (affineEulerianTilde_nonnegCoeffs n)

lemma natDegree_affineEulerianTilde (n : Nat) :
    (affineEulerianTilde n).natDegree = (eulerianTilde n).natDegree := by
  rw [affineEulerianTilde]
  refine natDegree_affineDeriv (eulerianTilde_ne_zero n) ?_ ?_
  · rw [natDegree_eulerianTilde]
    lia
  · rw [natDegree_eulerianTilde]
    norm_num

/-- Once the affine block is known to precede `P_n`, the outer `X` factor in the
recurrence gives `P_n ≪ P_{n+1}`. -/
lemma prec_eulerianTilde_succ_of_prec_affine {n : Nat}
    (haff : Prec (affineEulerianTilde n) (eulerianTilde n)) :
    Prec (eulerianTilde n) (eulerianTilde (n + 1)) := by
  have haff_nonpos :
      ∀ r ∈ (affineEulerianTilde n).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs haff.1.2 (affineEulerianTilde_nonnegCoeffs n)
  have hp_nonpos :
      ∀ r ∈ (eulerianTilde n).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs haff.2.1.2 (eulerianTilde_nonnegCoeffs n)
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
  | 0 => prec_eulerianTilde_succ_of_prec_affine <| prec_affineEulerianTilde <| by simp
  | n + 1 => prec_eulerianTilde_succ_of_prec_affine <| prec_affineEulerianTilde
    (prec_eulerianTilde_succ n).2.1.2

/-- Every Eulerian tilde polynomial is real-rooted, obtained as the
right-hand component of the interlacing induction. -/
theorem isRealRooted_eulerianTilde : ∀ n : Nat,
    ((eulerianTilde n) ≠ 0 ∧ (eulerianTilde n).Splits)
  | 0 => by
      simp
  | n + 1 => (prec_eulerianTilde_succ n).2.1

theorem interlaces_eulerianTilde_succ (n : Nat) :
    Interlaces (eulerianTilde n) (eulerianTilde (n + 1)) :=
  (prec_eulerianTilde_succ n).toInterlaces
    (by simp [natDegree_eulerianTilde])

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
