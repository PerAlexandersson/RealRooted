module

public import RealRooted.CombinatorialExamples.Common
public import RealRooted.CombinatorialExamples.ColoredSetPartitions
public import RealRooted.MaWang
public import RealRooted.Touchard
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Tactic
import RealRooted.Tactic.RowInterlacing

/-!
# Touchard Polynomials

Real-rootedness and Sturm-sequence facts for the Touchard polynomial
recurrence.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

lemma coeff_touchard_succ (n m : Nat) :
    coeff (touchard (n + 1)) (m + 1) =
      coeff (touchard n) m + (m + 1 : ℝ) * coeff (touchard n) (m + 1) := by
  simp [touchard_succ, coeff_derivative]
  ring

/-- Touchard coefficients are Stirling numbers of the second kind. -/
theorem coeff_touchard_eq_stirlingSecond : ∀ n k : ℕ,
    (touchard n).coeff k = (Nat.stirlingSecond n k : ℝ)
  | 0, 0 => by simp [touchard]
  | 0, k + 1 => by
      rw [touchard_zero, coeff_one]
      simp
  | n + 1, 0 => by simp [touchard_succ]
  | n + 1, k + 1 => by
      rw [coeff_touchard_succ, coeff_touchard_eq_stirlingSecond,
        coeff_touchard_eq_stirlingSecond]
      exact_mod_cast (by
        simpa [add_comm] using (Nat.stirlingSecond_succ_succ n k).symm)

lemma coeff_touchard_top_and_above :
    ∀ n : Nat, coeff (touchard n) n = 1 ∧ ∀ m > n, coeff (touchard n) m = 0
  | 0 => by
      grind [touchard_zero, coeff_one]
  | n + 1 => by
      rcases coeff_touchard_top_and_above n with ⟨htop, habove⟩
      constructor
      · rw [show n + 1 = n + 0 + 1 by lia, coeff_touchard_succ]
        simp [htop, habove (n + 1) (by lia)]
      · rintro (_ | k) hm
        · lia
        · rw [show k + 1 = k + 0 + 1 by lia, coeff_touchard_succ]
          simp [habove k (by lia), habove (k + 1) (by lia)]

lemma natDegree_touchard (n : Nat) :
    (touchard n).natDegree = n := by
  rr_row_natDegree

lemma monic_touchard (n : Nat) :
    (touchard n).Monic := by
  rcases coeff_touchard_top_and_above n with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_touchard]
  lia

lemma touchard_ne_zero (n : Nat) :
    touchard n ≠ 0 := by
  rr_row_ne_zero

lemma touchard_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (touchard n) :=
  hasPosLeadingCoeff_of_monic (monic_touchard n)

lemma touchard_nonnegCoeffs : ∀ n : Nat, HasNonnegCoeffs (touchard n) := by
  rr_row_nonneg_coeffs

lemma roots_nonpos_touchard_of_isRealRooted {n : Nat} :
    ∀ r ∈ (touchard n).roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (touchard_nonnegCoeffs n)

lemma interlaces_touchard_zero_one :
    Interlaces (touchard 0) (touchard 1) :=
  by simpa [touchard_zero, touchard_one] using interlaces_one_linear (p := X) (by simp)

lemma strictInterl_touchard_one_two :
    StrictInterl (touchard 1) (touchard 2) := by
  exact (show Interlaces (touchard 1) (touchard 2) by
    rr_row_interlaces).toStrictInterl

/-- Consecutive Touchard polynomials satisfy `StrictInterl`, hence are real-rooted. -/
theorem strictInterl_touchard_succ : ∀ n : Nat, StrictInterl (touchard n) (touchard (n + 1))
  | n => (show Interlaces (touchard n) (touchard (n + 1)) by
      rr_row_interlaces).toStrictInterl

theorem interlaces_touchard_succ (n : Nat) :
    Interlaces (touchard n) (touchard (n + 1)) := by
  rr_row_interlaces

theorem isRealRooted_touchard : ∀ n : Nat, ((touchard n) ≠ 0 ∧ (touchard n).Splits)
  | 0 => by simp
  | n + 1 => (strictInterl_touchard_succ n).2.1

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

/-- The Touchard polynomials are the colored set-partition polynomials with
parameters `c = 0` and `m = 1`. -/
theorem touchard_eq_coloredSetPartitions_zero_one (n : ℕ) :
    touchard n = coloredSetPartitions 0 1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [touchard_succ, coloredSetPartitions_succ, ih]
    simp [coloredSetPartitionsCoeffA, coloredSetPartitionsCoeffB]

end RealRooted
