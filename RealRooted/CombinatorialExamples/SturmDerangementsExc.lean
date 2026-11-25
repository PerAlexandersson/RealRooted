module

public import RealRooted.Basic
public import RealRooted.Derivative
public import RealRooted.Wagner
import RealRooted.AffineDerivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import RealRooted.Tactic.Finish
public import Mathlib.Tactic
import RealRooted.Mathlib.Algebra.Polynomial.Basic
import RealRooted.SequenceClosure
import RealRooted.WagnerRightSum
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Derivative.Algebra
import RealRooted.DerivativeRecurrence.Interlacing
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Derangement Excedance Polynomials

Sturm-sequence and real-rootedness facts for derangement excedance polynomials,
using `X` for the polynomial variable.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The derangement excedance recurrence, viewed as a candidate Sturm sequence. -/
def sturmDerangementsExc : Nat → ℝ[X]
  | 0 => 0
  | 1 => 0
  | 2 => X
  | n + 3 =>
      X * (((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 1) +
        ((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 2) +
        (1 - X) * (sturmDerangementsExc (n + 2)).derivative)

@[simp] lemma sturmDerangementsExc_zero : sturmDerangementsExc 0 = 0 := rfl

@[simp] lemma sturmDerangementsExc_one : sturmDerangementsExc 1 = 0 := rfl

@[simp] lemma sturmDerangementsExc_two : sturmDerangementsExc 2 = X := rfl

lemma sturmDerangementsExc_recurrence (n : Nat) :
    sturmDerangementsExc (n + 3) =
      X * (((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 1) +
        ((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 2) +
        (1 - X) * (sturmDerangementsExc (n + 2)).derivative) := rfl

/-- The affine derivative block appearing in the derangement recurrence. -/
def affineSturmDerangementsExc (n : Nat) : ℝ[X] :=
  C (n : ℝ) * sturmDerangementsExc n + (1 - X) * (sturmDerangementsExc n).derivative

/-- The full recurrence core before the outer `X` factor:
`n * P_{n-1} + (n * P_n + (1 - X) P'_n)`. -/
def recurrenceCoreSturmDerangementsExc (n : Nat) : ℝ[X] :=
  C (n : ℝ) * sturmDerangementsExc (n - 1) + affineSturmDerangementsExc n

lemma sturmDerangementsExc_succ_eq_X_mul_recurrenceCore (n : Nat) (hn : 2 ≤ n) :
    sturmDerangementsExc (n + 1) = X * recurrenceCoreSturmDerangementsExc n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [recurrenceCoreSturmDerangementsExc, affineSturmDerangementsExc,
    add_assoc, add_left_comm, add_comm, ofNat_def] using sturmDerangementsExc_recurrence k

/-- Every derangement excedance polynomial has `X` as a factor. In the original variable,
this says every `P_n` is divisible by `t`. -/
lemma X_dvd_sturmDerangementsExc : ∀ n : Nat, X ∣ sturmDerangementsExc n
  | 0 => ⟨0, by simp [sturmDerangementsExc]⟩
  | 1 => ⟨0, by simp [sturmDerangementsExc]⟩
  | 2 => ⟨1, by simp [sturmDerangementsExc]⟩
  | n + 3 =>
      ⟨((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 1) +
        ((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 2) +
        (1 - X) * (sturmDerangementsExc (n + 2)).derivative, by
        simp [sturmDerangementsExc]⟩

lemma sturmDerangementsExc_three :
    sturmDerangementsExc 3 = X ^ 2 + X := by
  rw [sturmDerangementsExc_recurrence 0]
  simp
  grind

lemma sturmDerangementsExc_four :
    sturmDerangementsExc 4 = X ^ 3 + 7 * X ^ 2 + X := by
  rw [sturmDerangementsExc_recurrence 1, sturmDerangementsExc_three]
  simp
  grind

lemma sturmDerangementsExc_five :
    sturmDerangementsExc 5 = X ^ 4 + 21 * X ^ 3 + 21 * X ^ 2 + X := by
  have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := (ofNat_def 2).symm
  rw [sturmDerangementsExc_recurrence 2, sturmDerangementsExc_three, sturmDerangementsExc_four]
  simp only [Nat.cast_ofNat, derivative_X_pow_succ, map_add, map_one,
    derivative_mul, derivative_ofNat, zero_mul, Nat.cast_one, pow_one, zero_add, derivative_X]
  grind

lemma coeff_sturmDerangementsExc_succ (n m : Nat) :
    (sturmDerangementsExc (n + 3)).coeff (m + 1) =
      (n + 2 : ℝ) * (sturmDerangementsExc (n + 1)).coeff m +
      ((n + 2 : ℝ) - m) * (sturmDerangementsExc (n + 2)).coeff m +
      (m + 1 : ℝ) * (sturmDerangementsExc (n + 2)).coeff (m + 1) := by
  rw [sturmDerangementsExc_recurrence, coeff_X_mul]
  simp only [coeff_add, coeff_one_sub_X_mul_derivative]
  rw [show ((n + 2 : ℝ[X])) = C (n + 2 : ℝ) by simp [ofNat_def],
    coeff_C_mul, coeff_C_mul]
  ring

lemma coeff_sturmDerangementsExc_top_and_above :
    ∀ n : Nat, 2 ≤ n →
      (sturmDerangementsExc n).coeff (n - 1) = 1 ∧
      ∀ m > n - 1, (sturmDerangementsExc n).coeff m = 0
  | 0, h => by lia
  | 1, h => by lia
  | 2, _ => by
      grind [sturmDerangementsExc_two, coeff_X]
  | 3, _ => by
      constructor
      · rw [sturmDerangementsExc_three]
        norm_num [coeff_X_pow, coeff_X]
      · intro m hm
        have hm' : 2 < m := by lia
        rw [sturmDerangementsExc_three]
        have hX2 : (X ^ 2 : ℝ[X]).coeff m = 0 := by grind
        have hX : (X : ℝ[X]).coeff m = 0 := by
          have hm1' : ¬1 = m := by lia
          simp [coeff_X, hm1']
        simp [hX2, hX]
  | n + 4, _ => by
      rcases coeff_sturmDerangementsExc_top_and_above (n + 2) (by lia) with
        ⟨hsmall_top, hsmall_hi⟩
      rcases coeff_sturmDerangementsExc_top_and_above (n + 3) (by lia) with ⟨hbig_top, hbig_hi⟩
      constructor
      · have hsmall_zero : (sturmDerangementsExc (n + 2)).coeff (n + 2) = 0 :=
          hsmall_hi (n + 2) (by lia)
        have hbig_zero : (sturmDerangementsExc (n + 3)).coeff (n + 3) = 0 :=
          hbig_hi (n + 3) (by lia)
        have hbig_top' : (sturmDerangementsExc (n + 3)).coeff (n + 2) = 1 := by lia
        have htop :
            (sturmDerangementsExc (n + 4)).coeff (n + 3) = 1 := by
          rw [coeff_sturmDerangementsExc_succ (n + 1) (n + 2)]
          simp [hsmall_zero, hbig_top', hbig_zero]
        lia
      · intro m hm
        cases m with
        | zero =>
            lia
        | succ m =>
            have hsmall_zero : (sturmDerangementsExc (n + 2)).coeff m = 0 :=
              hsmall_hi m (by lia)
            have hbig_zero₁ : (sturmDerangementsExc (n + 3)).coeff m = 0 :=
              hbig_hi m (by lia)
            have hbig_zero₂ : (sturmDerangementsExc (n + 3)).coeff (m + 1) = 0 :=
              hbig_hi (m + 1) (by lia)
            rw [coeff_sturmDerangementsExc_succ (n + 1) m]
            simp [hsmall_zero, hbig_zero₁, hbig_zero₂]

lemma coeff_sturmDerangementsExc_symm :
    ∀ n : Nat, ∀ m ≤ n,
      (sturmDerangementsExc n).coeff m = (sturmDerangementsExc n).coeff (n - m)
  | 0, m, hm => by
      lia
  | 1, m, hm => by
      simp
  | 2, m, hm => by
      have hm0 : m = 0 ∨ m = 1 ∨ m = 2 := by lia
      rcases hm0 with rfl | rfl | rfl <;> simp [sturmDerangementsExc_two, coeff_X]
  | n + 3, 0, hm => by
      have hcoeff0 : (sturmDerangementsExc (n + 3)).coeff 0 = 0 := by
        rcases X_dvd_sturmDerangementsExc (n + 3) with ⟨q, hq⟩
        simp [hq]
      have hcoeff_hi : (sturmDerangementsExc (n + 3)).coeff (n + 3) = 0 := by
        rcases coeff_sturmDerangementsExc_top_and_above (n + 3) (by lia) with ⟨_, habove⟩
        simp_all
      lia
  | n + 3, m + 1, hm => by
      by_cases htop : m + 1 = n + 3
      · have hcoeff_hi : (sturmDerangementsExc (n + 3)).coeff (m + 1) = 0 := by
          rcases coeff_sturmDerangementsExc_top_and_above (n + 3) (by lia) with ⟨_, habove⟩
          simp_all
        have hcoeff0 : (sturmDerangementsExc (n + 3)).coeff 0 = 0 := by
          rcases X_dvd_sturmDerangementsExc (n + 3) with ⟨q, hq⟩
          simp [hq]
        simp_all
      · have hm_le : m ≤ n + 1 := by lia
        have hm_succ_le : m + 1 ≤ n + 2 := by lia
        have hsub : n + 2 - (m + 1) = n + 1 - m := by lia
        have hidx : (n + 1 - m) + 1 = n + 2 - m := by lia
        have hgoal : n + 3 - (m + 1) = n + 2 - m := by lia
        have hs1 :=
          coeff_sturmDerangementsExc_symm (n + 1) m hm_le
        have hs2m :=
          coeff_sturmDerangementsExc_symm (n + 2) m (by lia)
        have hs2m1 :
            (sturmDerangementsExc (n + 2)).coeff (m + 1) =
              (sturmDerangementsExc (n + 2)).coeff (n + 1 - m) := by
          simpa [hsub] using
            coeff_sturmDerangementsExc_symm (n + 2) (m + 1) hm_succ_le
        have hrec1 := coeff_sturmDerangementsExc_succ n m
        have hrec2 :
            (sturmDerangementsExc (n + 3)).coeff (n + 2 - m) =
              (n + 2 : ℝ) * (sturmDerangementsExc (n + 1)).coeff (n + 1 - m) +
              ((n + 2 : ℝ) - ↑(n + 1 - m)) * (sturmDerangementsExc (n + 2)).coeff (n + 1 - m) +
              (((n + 1 - m : Nat) : ℝ) + 1) *
                (sturmDerangementsExc (n + 2)).coeff (n + 2 - m) := by
          simpa [hidx] using coeff_sturmDerangementsExc_succ n (n + 1 - m)
        rw [hgoal, hrec1, hrec2, hs1, hs2m, hs2m1]
        have hcast1 : (((n + 1 - m : Nat) : ℝ)) = (n + 1 : ℝ) - m := by simp_all
        grind

lemma natDegree_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n) :
    (sturmDerangementsExc n).natDegree = n - 1 := by
  rcases coeff_sturmDerangementsExc_top_and_above n hn with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm ↦ habove m hm))
    (by simp_all)

lemma monic_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n) :
    (sturmDerangementsExc n).Monic := by
  rcases coeff_sturmDerangementsExc_top_and_above n hn with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_sturmDerangementsExc hn]
  lia

lemma sturmDerangementsExc_ne_zero {n : Nat} (hn : 2 ≤ n) :
    sturmDerangementsExc n ≠ 0 :=
  (monic_sturmDerangementsExc hn).ne_zero

lemma sturmDerangementsExc_posLeadingCoeff {n : Nat} (hn : 2 ≤ n) :
    HasPosLeadingCoeff (sturmDerangementsExc n) :=
  hasPosLeadingCoeff_of_monic (monic_sturmDerangementsExc hn)

lemma natDegree_le_sturmDerangementsExc (n : Nat) :
    (sturmDerangementsExc n).natDegree ≤ n := by
  cases n with
  | zero =>
      simp [sturmDerangementsExc_zero]
  | succ n =>
      cases n with
      | zero =>
          simp [sturmDerangementsExc_one]
      | succ n =>
          rw [natDegree_sturmDerangementsExc (by lia)]
          lia

lemma reflect_sturmDerangementsExc (n : Nat) :
    Polynomial.reflect n (sturmDerangementsExc n) = sturmDerangementsExc n := by
  ext m
  rw [Polynomial.coeff_reflect]
  by_cases hm : m ≤ n
  · rw [Polynomial.revAt_le hm, coeff_sturmDerangementsExc_symm n m hm]
  · rw [Polynomial.revAt_eq_self_of_lt (lt_of_not_ge hm)]

lemma sturmDerangementsExc_isRoot_neg_one_of_odd {n : Nat} (hn : Odd n) :
    (sturmDerangementsExc n).IsRoot (-1) :=
  Polynomial.isRoot_neg_one_of_reflect_eq_self_of_odd
    (natDegree_le_sturmDerangementsExc n) (reflect_sturmDerangementsExc n) hn

lemma X_add_one_dvd_sturmDerangementsExc_of_odd {n : Nat} (hn : Odd n) :
    X + 1 ∣ sturmDerangementsExc n :=
  by simpa [sub_eq_add_neg, add_comm] using
    (dvd_iff_isRoot).2 (sturmDerangementsExc_isRoot_neg_one_of_odd hn)

/-- The affine derivative block is a generic nonnegative differential step. -/
private lemma hasNonnegCoeffs_affineDerivative {f : ℝ[X]} {n : ℕ}
    (hf : HasNonnegCoeffs f) (hd : f.natDegree ≤ n) :
    HasNonnegCoeffs (C (n : ℝ) * f + (1 - X) * f.derivative) := by
  apply hasNonnegCoeffs_mul_add_mul_derivative hd (by simp) ?_ hf
  intro i j hj
  simp only [coeff_sub, coeff_one, coeff_X, coeff_C]
  rcases i with _ | i
  · norm_num
    exact_mod_cast hj
  · simp

lemma sturmDerangementsExc_nonnegCoeffs : ∀ n : Nat, HasNonnegCoeffs (sturmDerangementsExc n)
  | 0 => hasNonnegCoeffs_zero
  | 1 => hasNonnegCoeffs_zero
  | 2 => by simpa [sturmDerangementsExc_two] using hasNonnegCoeffs_X
  | n + 3 => by
    rw [sturmDerangementsExc_recurrence, add_assoc]
    have h := ((hasNonnegCoeffs_C (by positivity : (0 : ℝ) ≤ n + 2)).mul
      (sturmDerangementsExc_nonnegCoeffs (n + 1))).add
      (hasNonnegCoeffs_affineDerivative (sturmDerangementsExc_nonnegCoeffs (n + 2))
        (natDegree_le_sturmDerangementsExc (n + 2)))
    simpa only [map_add, map_natCast, map_ofNat, Nat.cast_add, Nat.cast_ofNat] using h.X_mul

lemma roots_nonpos_sturmDerangementsExc_of_isRealRooted {n : Nat} :
    ∀ r ∈ (sturmDerangementsExc n).roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (sturmDerangementsExc_nonnegCoeffs n)

lemma strictInterl_lowerTerm_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n)
    (hstrictInterl : StrictInterl (sturmDerangementsExc (n - 1)) (sturmDerangementsExc n)) :
    StrictInterl (C (n : ℝ) * sturmDerangementsExc (n - 1)) (sturmDerangementsExc n) :=
  StrictInterl.C_mul_left hstrictInterl (by positivity)

lemma strictInterl_affine_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n)
    (hrr : (sturmDerangementsExc n).Splits) :
    StrictInterl (affineSturmDerangementsExc n) (sturmDerangementsExc n) := by
  apply strictInterl_affine_derivative'
  · lia
  · rw [natDegree_sturmDerangementsExc hn]
    lia
  · exact sturmDerangementsExc_posLeadingCoeff hn
  · exact roots_nonpos_sturmDerangementsExc_of_isRealRooted
  · rw [natDegree_sturmDerangementsExc hn]
    exact Nat.cast_lt.mpr (Nat.sub_lt (by lia) (by lia))

lemma natDegree_affine_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n) :
    (affineSturmDerangementsExc n).natDegree = (sturmDerangementsExc n).natDegree := by
  refine natDegree_affineDeriv (sturmDerangementsExc_ne_zero hn) ?_ ?_
  · rw [natDegree_sturmDerangementsExc hn]
    lia
  · rw [natDegree_sturmDerangementsExc hn]
    have hn0 : 0 < n := by lia
    have hlt : ((n - 1 : Nat) : ℝ) < n := by simp_all
    linarith

lemma affine_sturmDerangementsExc_nonnegCoeffs {n : Nat} (hn : 2 ≤ n) :
    HasNonnegCoeffs (affineSturmDerangementsExc n) := by
  apply hasNonnegCoeffs_affineDerivative (sturmDerangementsExc_nonnegCoeffs n)
  rw [natDegree_sturmDerangementsExc hn]
  lia

lemma affine_sturmDerangementsExc_isRoot_neg_one_of_even {n : Nat}
    (hn : Even n) (h2 : 2 ≤ n) :
    (affineSturmDerangementsExc n).IsRoot (-1) := by
  rw [IsRoot.def]
  have hprev : (sturmDerangementsExc (n - 1)).eval (-1) = 0 :=
    (sturmDerangementsExc_isRoot_neg_one_of_odd (Nat.Even.sub_odd (by lia) hn odd_one)).eq_zero
  have hnext := (sturmDerangementsExc_isRoot_neg_one_of_odd (hn.add_odd odd_one)).eq_zero
  rw [sturmDerangementsExc_succ_eq_X_mul_recurrenceCore n h2] at hnext
  simpa only [recurrenceCoreSturmDerangementsExc, eval_mul, eval_X, eval_add, eval_C,
    hprev, mul_zero, zero_add, neg_mul, one_mul, neg_eq_zero] using hnext

lemma X_add_one_dvd_affine_sturmDerangementsExc_of_even {n : Nat}
    (hn : Even n) (h2 : 2 ≤ n) :
    X + 1 ∣ affineSturmDerangementsExc n :=
  by simpa [sub_eq_add_neg, add_comm] using
    (dvd_iff_isRoot).2 (affine_sturmDerangementsExc_isRoot_neg_one_of_even hn h2)

lemma X_add_one_dvd_recurrenceCoreSturmDerangementsExc_of_even {n : Nat}
    (hn : Even n) (h2 : 2 ≤ n) :
    X + 1 ∣ recurrenceCoreSturmDerangementsExc n := by
  rw [recurrenceCoreSturmDerangementsExc]
  apply dvd_add
  · have hodd : Odd (n - 1) := by grind
    exact dvd_mul_of_dvd_right (X_add_one_dvd_sturmDerangementsExc_of_odd hodd) (C (n : ℝ))
  · exact X_add_one_dvd_affine_sturmDerangementsExc_of_even hn h2

lemma recurrenceCoreSturmDerangementsExc_nonnegCoeffs {n : Nat} (hn : 2 ≤ n) :
    HasNonnegCoeffs (recurrenceCoreSturmDerangementsExc n) := by
  rw [recurrenceCoreSturmDerangementsExc]
  intro m
  have hscalar :
      0 ≤ (C (n : ℝ) * sturmDerangementsExc (n - 1)).coeff m := by
    simpa [coeff_C_mul] using mul_nonneg (by simp) (sturmDerangementsExc_nonnegCoeffs (n - 1) m)
  rw [coeff_add]
  exact add_nonneg hscalar (affine_sturmDerangementsExc_nonnegCoeffs hn m)

lemma recurrenceCoreSturmDerangementsExc_ne_zero {n : Nat} (hn : 2 ≤ n) :
    recurrenceCoreSturmDerangementsExc n ≠ 0 := by
  have hsucc_ne : sturmDerangementsExc (n + 1) ≠ 0 :=
    sturmDerangementsExc_ne_zero (by lia)
  rw [sturmDerangementsExc_succ_eq_X_mul_recurrenceCore n hn] at hsucc_ne
  simp_all

lemma strictInterl_X_mul_affine_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n)
    (hrr : (sturmDerangementsExc n).Splits) :
    StrictInterl (X * affineSturmDerangementsExc n) (X * sturmDerangementsExc n) :=
  by simpa using (strictInterl_affine_sturmDerangementsExc hn hrr).mul_X_sub_C_both 0

lemma strictInterl_X_mul_lowerTerm_sturmDerangementsExc {n : Nat} (hn : 3 ≤ n)
    (hstrictInterl : StrictInterl (sturmDerangementsExc (n - 1)) (sturmDerangementsExc n)) :
    StrictInterl (X * (C (n : ℝ) * sturmDerangementsExc (n - 1)))
      (X * sturmDerangementsExc n) := by
  have hlower : StrictInterl (C (n : ℝ) * sturmDerangementsExc (n - 1))
      (sturmDerangementsExc n) :=
    strictInterl_lowerTerm_sturmDerangementsExc (by lia) hstrictInterl
  have hlower_nonneg :
      HasNonnegCoeffs (C (n : ℝ) * sturmDerangementsExc (n - 1)) :=
    hasNonnegCoeffs_C_mul (by positivity) (sturmDerangementsExc_nonnegCoeffs (n - 1))
  simpa using hlower.mul_X_sub_C_both 0

/-- The recurrence core
`n * P_{n-1} + (n * P_n + (1 - X) P'_n)` precedes `P_n` once `P_{n-1} ≪ P_n`.
This is the inner addition step in the human proof of Sturm interlacing. -/
lemma strictInterl_recurrenceCoreSturmDerangementsExc {n : Nat} (hn : 3 ≤ n)
    (hstrictInterl : StrictInterl (sturmDerangementsExc (n - 1)) (sturmDerangementsExc n)) :
    StrictInterl (recurrenceCoreSturmDerangementsExc n) (sturmDerangementsExc n) := by
  rw [recurrenceCoreSturmDerangementsExc]
  have hlower :
      StrictInterl (C (n : ℝ) * sturmDerangementsExc (n - 1)) (sturmDerangementsExc n) :=
    strictInterl_lowerTerm_sturmDerangementsExc (by lia) hstrictInterl
  have haff : StrictInterl (affineSturmDerangementsExc n) (sturmDerangementsExc n) :=
    strictInterl_affine_sturmDerangementsExc (by lia) hstrictInterl.2.1.2
  have hlower_pos : HasPosLeadingCoeff (C (n : ℝ) * sturmDerangementsExc (n - 1)) :=
    hasPosLeadingCoeff_C_mul (by positivity) (sturmDerangementsExc_posLeadingCoeff (by lia))
  have haff_pos : HasPosLeadingCoeff (affineSturmDerangementsExc n) :=
    (affine_sturmDerangementsExc_nonnegCoeffs (by lia)).pos_leadingCoeff haff.1.1
  exact StrictInterl.add_of_right_of_posLeadingCoeff hlower haff hlower_pos haff_pos

/-- Once the recurrence core is known to precede `P_n`, the actual Sturm step
`P_n ≪ P_{n+1}` follows immediately from the outer `X` factor in the recurrence. -/
lemma strictInterl_sturmDerangementsExc_succ_of_strictInterl_recurrenceCore {n : Nat} (hn : 2 ≤ n)
    (hcore : StrictInterl (recurrenceCoreSturmDerangementsExc n) (sturmDerangementsExc n)) :
    StrictInterl (sturmDerangementsExc n) (sturmDerangementsExc (n + 1)) := by
  have hmain :
      StrictInterl (sturmDerangementsExc n) (X * recurrenceCoreSturmDerangementsExc n) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hcore
      (recurrenceCoreSturmDerangementsExc_nonnegCoeffs hn)
      (sturmDerangementsExc_nonnegCoeffs n)
  simpa [sturmDerangementsExc_succ_eq_X_mul_recurrenceCore n hn] using hmain

/-- Consecutive derangement excedance polynomials interlace in the oriented
`StrictInterl` sense: `P_n ≪ P_{n+1}` for every `n ≥ 2`. -/
theorem strictInterl_sturmDerangementsExc_succ : ∀ n : Nat, 2 ≤ n →
    StrictInterl (sturmDerangementsExc n) (sturmDerangementsExc (n + 1))
  | 0, hn => by lia
  | 1, hn => by lia
  | 2, _ => by
      exact
        strictInterl_sturmDerangementsExc_succ_of_strictInterl_recurrenceCore
          (n := 2) (by lia) <| by
        simpa [recurrenceCoreSturmDerangementsExc, affineSturmDerangementsExc]
          using strictInterl_affine_sturmDerangementsExc (n := 2) (by lia) (by simp)
  | n + 3, _ => by
      have hprev : StrictInterl (sturmDerangementsExc (n + 2)) (sturmDerangementsExc (n + 3)) :=
        strictInterl_sturmDerangementsExc_succ (n + 2) (by lia)
      have hcore : StrictInterl (recurrenceCoreSturmDerangementsExc (n + 3))
          (sturmDerangementsExc (n + 3)) :=
        strictInterl_recurrenceCoreSturmDerangementsExc (n := n + 3) (by lia) hprev
      exact
        strictInterl_sturmDerangementsExc_succ_of_strictInterl_recurrenceCore
          (n := n + 3) (by lia) hcore

/-- In particular, every nontrivial derangement excedance polynomial is real-rooted. -/
theorem isRealRooted_sturmDerangementsExc : ∀ n : Nat, 2 ≤ n →
    ((sturmDerangementsExc n) ≠ 0 ∧ (sturmDerangementsExc n).Splits) := by
  intro n hn
  rr_finish using strictInterl_sturmDerangementsExc_succ n hn

/-- Consecutive derangement excedance polynomials form a genuine differ-by-1
interlacing pair, not just an abstract `StrictInterl` pair. -/
theorem interlaces_sturmDerangementsExc_succ {n : Nat} (hn : 2 ≤ n) :
    Interlaces (sturmDerangementsExc n) (sturmDerangementsExc (n + 1)) :=
  (strictInterl_sturmDerangementsExc_succ n hn).toInterlaces <| by
    rw [natDegree_sturmDerangementsExc hn, natDegree_sturmDerangementsExc (by lia)]
    lia

/-- The descending prefix `[P_{n+1}, P_n, ..., P_2]` of the derangement
excedance sequence. This is the natural finite list for `IsSturmSeq`. -/
def sturmDerangementsExcPrefix : Nat → List ℝ[X]
  | 0 => []
  | n + 1 => sturmDerangementsExc (n + 2) :: sturmDerangementsExcPrefix n

@[simp] lemma sturmDerangementsExcPrefix_zero :
    sturmDerangementsExcPrefix 0 = [] := rfl

@[simp] lemma sturmDerangementsExcPrefix_succ (n : Nat) :
    sturmDerangementsExcPrefix (n + 1) =
      sturmDerangementsExc (n + 2) :: sturmDerangementsExcPrefix n := rfl

/-- Every finite descending prefix of the nonzero derangement excedance sequence
is a Sturm sequence. -/
theorem isSturmSeq_sturmDerangementsExcPrefix :
    ∀ n : Nat, IsSturmSeq (sturmDerangementsExcPrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [sturmDerangementsExcPrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simp [sturmDerangementsExcPrefix, IsSturmSeq]
      | succ n =>
          simpa [sturmDerangementsExcPrefix, IsSturmSeq] using
            And.intro (interlaces_sturmDerangementsExc_succ (n := n + 2) (by lia)) ih

end RealRooted
