module

public import RealRooted.CombinatorialExamples.Common
public import RealRooted.CombinatorialExamples.ColoredSetPartitions
public import RealRooted.MaWang
public import RealRooted.Touchard
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Tactic

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
  rcases coeff_touchard_top_and_above n with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm))
    (by simp [htop])

lemma monic_touchard (n : Nat) :
    (touchard n).Monic := by
  rcases coeff_touchard_top_and_above n with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_touchard]
  lia

lemma touchard_ne_zero (n : Nat) :
    touchard n ≠ 0 :=
  (monic_touchard n).ne_zero

lemma touchard_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (touchard n) :=
  hasPosLeadingCoeff_of_monic (monic_touchard n)

lemma touchard_nonnegCoeffs : ∀ n : Nat, HasNonnegCoeffs (touchard n)
  | 0 => by
      intro m
      cases m <;> simp [touchard_zero, coeff_one]
  | n + 1 => by
      rintro (_ | m)
      · simp [touchard_succ]
      · rw [coeff_touchard_succ]
        exact add_nonneg (touchard_nonnegCoeffs n m)
          (mul_nonneg (by positivity) (touchard_nonnegCoeffs n (m + 1)))

lemma roots_nonpos_touchard_of_isRealRooted {n : Nat} :
    ∀ r ∈ (touchard n).roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (touchard_nonnegCoeffs n)

lemma interlaces_touchard_zero_one :
    Interlaces (touchard 0) (touchard 1) :=
  by simpa [touchard_zero, touchard_one] using interlaces_one_linear (p := X) (by simp)

private lemma strictInterl_touchard_step (n : Nat) (hn : 1 ≤ n) (hsplit : (touchard n).Splits) :
    StrictInterl (touchard n) (touchard (n + 1)) := by
  have hInter : Interlaces (touchard n).derivative (touchard n) :=
    derivative_interlaces_of_natDegree_ne_zero hsplit (by rw [natDegree_touchard]; lia)
  have hderiv_pos : HasPosLeadingCoeff (touchard n).derivative :=
    (touchard_posLeadingCoeff n).derivative (by rw [natDegree_touchard]; lia)
  have hnext_pos : HasPosLeadingCoeff (X * touchard n + X * (touchard n).derivative) := by
    simpa [touchard_succ, add_comm] using touchard_posLeadingCoeff (n + 1)
  have hdeg_lo :
      (touchard n).natDegree ≤ (X * touchard n + X * (touchard n).derivative).natDegree := by
    rw [← touchard_succ, natDegree_touchard, natDegree_touchard]
    lia
  have hdeg_hi :
      (X * touchard n + X * (touchard n).derivative).natDegree ≤
        (touchard n).natDegree + 1 := by
    rw [← touchard_succ, natDegree_touchard, natDegree_touchard]
  exact strictInterl_of_interlaces_evalCoeff_nonpos hInter hderiv_pos hnext_pos
    hdeg_lo hdeg_hi (fun r hr => by
      simpa using roots_nonpos_touchard_of_isRealRooted r
        ((mem_roots (touchard_ne_zero n)).mpr hr))

lemma strictInterl_touchard_one_two :
    StrictInterl (touchard 1) (touchard 2) := by
  exact strictInterl_touchard_step 1 (by simp)
    interlaces_touchard_zero_one.toStrictInterl.2.1.2

/-- Consecutive Touchard polynomials satisfy `StrictInterl`, hence are real-rooted. -/
theorem strictInterl_touchard_succ : ∀ n : Nat, StrictInterl (touchard n) (touchard (n + 1))
  | 0 => interlaces_touchard_zero_one.toStrictInterl
  | n + 1 => strictInterl_touchard_step (n + 1) (by simp)
      (strictInterl_touchard_succ n).2.1.2

theorem interlaces_touchard_succ (n : Nat) :
    Interlaces (touchard n) (touchard (n + 1)) :=
  (strictInterl_touchard_succ n).toInterlaces (by simp [natDegree_touchard])

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
