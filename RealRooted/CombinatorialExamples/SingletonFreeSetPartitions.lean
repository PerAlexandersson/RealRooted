import RealRooted.CombinatorialExamples.Common
import Mathlib.Tactic

/-!
# Singleton-Free Set-Partition Polynomials

Real-rootedness and interlacing facts for the recurrence counting set
partitions without singleton blocks.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The polynomial sequence counting set partitions without singleton blocks,
defined recursively by
`D_{n+2}(X) = X * ((n+1) D_n(X) + D'_{n+1}(X))`
with `D₀(X) = 1` and `D₁(X) = 0`. -/
def singletonFreeSetPartitions : Nat → ℝ[X]
  | 0 => 1
  | 1 => 0
  | n + 2 =>
      X * (C (n + 1 : ℝ) * singletonFreeSetPartitions n +
        (singletonFreeSetPartitions (n + 1)).derivative)

@[simp] lemma singletonFreeSetPartitions_zero :
    singletonFreeSetPartitions 0 = 1 := rfl

@[simp] lemma singletonFreeSetPartitions_one :
    singletonFreeSetPartitions 1 = 0 := rfl

lemma singletonFreeSetPartitions_succ_succ (n : Nat) :
    singletonFreeSetPartitions (n + 2) =
      X * (C (n + 1 : ℝ) * singletonFreeSetPartitions n +
        (singletonFreeSetPartitions (n + 1)).derivative) := rfl

lemma singletonFreeSetPartitions_two :
    singletonFreeSetPartitions 2 = X := by
  simp [singletonFreeSetPartitions]

lemma singletonFreeSetPartitions_three :
    singletonFreeSetPartitions 3 = X := by
  simp [singletonFreeSetPartitions]

lemma coeff_singletonFreeSetPartitions_succ_succ (n m : Nat) :
    coeff (singletonFreeSetPartitions (n + 2)) (m + 1) =
      (n + 1 : ℝ) * coeff (singletonFreeSetPartitions n) m +
      (m + 1 : ℝ) * coeff (singletonFreeSetPartitions (n + 1)) (m + 1) := by
  rw [singletonFreeSetPartitions_succ_succ, coeff_X_mul, coeff_add]
  have hC :
      coeff (C (n + 1 : ℝ) * singletonFreeSetPartitions n) m =
        (n + 1 : ℝ) * coeff (singletonFreeSetPartitions n) m := by
    grind
  rw [hC, coeff_derivative]
  ring

lemma singletonFreeSetPartitions_nonnegCoeffs :
    ∀ n : Nat, HasNonnegCoeffs (singletonFreeSetPartitions n)
  | 0 => by
      rintro (_ | m)
      · simp [singletonFreeSetPartitions_zero]
      · rw [singletonFreeSetPartitions_zero, coeff_one, if_neg (Nat.succ_ne_zero m)]
  | 1 => by
      intro m
      simp [singletonFreeSetPartitions_one]
  | n + 2 => by
      rintro (_ | m)
      · simp [singletonFreeSetPartitions_succ_succ]
      · rw [coeff_singletonFreeSetPartitions_succ_succ]
        exact add_nonneg
          (mul_nonneg (by grind) (singletonFreeSetPartitions_nonnegCoeffs n m))
          (mul_nonneg (by grind)
            (singletonFreeSetPartitions_nonnegCoeffs (n + 1) (m + 1)))

lemma coeff_singletonFreeSetPartitions_top_pos_and_above :
    ∀ n : Nat, 2 ≤ n →
      0 < coeff (singletonFreeSetPartitions n) (n / 2) ∧
      ∀ m > n / 2, coeff (singletonFreeSetPartitions n) m = 0
  | 0, h => by
      lia
  | 1, h => by
      lia
  | 2, _ => by
      constructor <;> simp [singletonFreeSetPartitions_two, coeff_X]
      lia
  | 3, _ => by
      constructor <;> simp [singletonFreeSetPartitions_three, coeff_X]
      lia
  | n + 4, _ => by
      rcases coeff_singletonFreeSetPartitions_top_pos_and_above (n + 2) (by lia) with
        ⟨hsmall_top, hsmall_hi⟩
      rcases coeff_singletonFreeSetPartitions_top_pos_and_above (n + 3) (by lia) with
        ⟨hbig_top, hbig_hi⟩
      constructor
      · rw [show (n + 4) / 2 = ((n + 4) / 2 - 1) + 1 by lia,
          coeff_singletonFreeSetPartitions_succ_succ]
        rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
        · have hsmall_pos : 0 < coeff (singletonFreeSetPartitions (n + 2)) ((n + 4) / 2 - 1) := by
            grind
          have hbig_zero : coeff (singletonFreeSetPartitions (n + 3)) ((n + 4) / 2) = 0 := by grind
          have hidx : ((n + 4) / 2 - 1) + 1 = (n + 4) / 2 := by
            lia
          have hscale_eq : (((n + 2 : Nat) : ℝ) + 1) = (n + 3 : ℝ) := by
            grind
          have hcoeff_eq :
              ((((n + 4) / 2 - 1 : Nat) : ℝ) + 1) = (((n + 4) / 2 : Nat) : ℝ) := by
            simp
          rw [hidx, hscale_eq, hcoeff_eq, hbig_zero]
          have hscale : 0 < (n + 3 : ℝ) := by
            positivity
          nlinarith
        · have hsmall_pos : 0 < coeff (singletonFreeSetPartitions (n + 2)) ((n + 4) / 2 - 1) := by
            grind
          have hbig_pos : 0 < coeff (singletonFreeSetPartitions (n + 3)) ((n + 4) / 2) := by grind
          have hidx : ((n + 4) / 2 - 1) + 1 = (n + 4) / 2 := by
            lia
          have hscale_eq : (((n + 2 : Nat) : ℝ) + 1) = (n + 3 : ℝ) := by
            grind
          have hcoeff_eq :
              ((((n + 4) / 2 - 1 : Nat) : ℝ) + 1) = (((n + 4) / 2 : Nat) : ℝ) := by
            simp
          rw [hidx, hscale_eq, hcoeff_eq]
          have hscale₁ : 0 < (n + 3 : ℝ) := by
            positivity
          have hscale₂ : 0 < (((n + 4) / 2 : Nat) : ℝ) := by
            simp
          nlinarith
      · intro m hm
        cases m with
        | zero =>
            lia
        | succ k =>
            rw [coeff_singletonFreeSetPartitions_succ_succ]
            grind

lemma natDegree_singletonFreeSetPartitions (n : Nat) (hn : 2 ≤ n) :
    (singletonFreeSetPartitions n).natDegree = n / 2 := by
  rcases coeff_singletonFreeSetPartitions_top_pos_and_above n hn with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm))
    (by grind)

lemma singletonFreeSetPartitions_nonzero (n : Nat) (hn : 2 ≤ n) :
    singletonFreeSetPartitions n ≠ 0 := by
  rcases coeff_singletonFreeSetPartitions_top_pos_and_above n hn with ⟨htop, _⟩
  exact fun h0 => by simp [h0] at htop

lemma singletonFreeSetPartitions_posLeadingCoeff (n : Nat) (hn : 2 ≤ n) :
    HasPosLeadingCoeff (singletonFreeSetPartitions n) := by
  simpa [HasPosLeadingCoeff, leadingCoeff, natDegree_singletonFreeSetPartitions n hn] using
    (coeff_singletonFreeSetPartitions_top_pos_and_above n hn).1

/-- The inner recurrence core
`(n+1) D_n(X) + D'_{n+1}(X)` for singleton-free set partitions. -/
def singletonFreeSetPartitionsCore (n : Nat) : ℝ[X] :=
  C (n + 1 : ℝ) * singletonFreeSetPartitions n +
    (singletonFreeSetPartitions (n + 1)).derivative

lemma singletonFreeSetPartitions_succ_succ_eq_X_mul_core (n : Nat) :
    singletonFreeSetPartitions (n + 2) = X * singletonFreeSetPartitionsCore n := by
  rw [singletonFreeSetPartitions_succ_succ, singletonFreeSetPartitionsCore]

lemma singletonFreeSetPartitionsCore_nonnegCoeffs (n : Nat) :
    HasNonnegCoeffs (singletonFreeSetPartitionsCore n) := by
  intro m
  rw [singletonFreeSetPartitionsCore, coeff_add, coeff_C_mul]
  exact add_nonneg
    (mul_nonneg (by grind) (singletonFreeSetPartitions_nonnegCoeffs n m))
    ((singletonFreeSetPartitions_nonnegCoeffs (n + 1)).derivative m)

lemma singletonFreeSetPartitionsCore_ne_zero (n : Nat) :
    singletonFreeSetPartitionsCore n ≠ 0 := by
  have hsucc_ne : singletonFreeSetPartitions (n + 2) ≠ 0 :=
    singletonFreeSetPartitions_nonzero (n + 2) (by lia)
  rw [singletonFreeSetPartitions_succ_succ_eq_X_mul_core n] at hsucc_ne
  simp_all

lemma natDegree_singletonFreeSetPartitionsCore (n : Nat) :
    (singletonFreeSetPartitionsCore n).natDegree = (n + 2) / 2 - 1 := by
  have hcore_ne : singletonFreeSetPartitionsCore n ≠ 0 :=
    singletonFreeSetPartitionsCore_ne_zero n
  have hdeg :=
    congrArg Polynomial.natDegree
      (singletonFreeSetPartitions_succ_succ_eq_X_mul_core n)
  rw [natDegree_singletonFreeSetPartitions (n + 2) (by lia), natDegree_X_mul hcore_ne] at hdeg
  lia

lemma roots_nonpos_singletonFreeSetPartitions_of_isRealRooted {n : Nat}
    (hrr : (singletonFreeSetPartitions n).Splits) :
    ∀ r ∈ (singletonFreeSetPartitions n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (singletonFreeSetPartitions_nonnegCoeffs n)

lemma roots_nonpos_singletonFreeSetPartitionsCore_of_isRealRooted {n : Nat}
    (hrr : (singletonFreeSetPartitionsCore n).Splits) :
    ∀ r ∈ (singletonFreeSetPartitionsCore n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (singletonFreeSetPartitionsCore_nonnegCoeffs n)

lemma prec_singletonFreeSetPartitionsCore_of_prec {n : Nat} (hn : 3 ≤ n)
    (hprev : Prec (singletonFreeSetPartitions n) (singletonFreeSetPartitions (n + 1))) :
    Prec (singletonFreeSetPartitionsCore n) (singletonFreeSetPartitions (n + 1)) := by
  rw [singletonFreeSetPartitionsCore]
  have hscalar_ne : (n + 1 : ℝ) ≠ 0 := by
    grind
  have hlower :
      Prec (C (n + 1 : ℝ) * singletonFreeSetPartitions n)
        (singletonFreeSetPartitions (n + 1)) :=
    prec_C_mul_left hprev hscalar_ne
  have hder :
      Interlaces (singletonFreeSetPartitions (n + 1)).derivative
        (singletonFreeSetPartitions (n + 1)) :=
    derivative_interlaces hprev.2.1.2 <| by
      rw [natDegree_singletonFreeSetPartitions (n + 1) (by lia)]
      lia
  have hlower_pos :
      HasPosLeadingCoeff (C (n + 1 : ℝ) * singletonFreeSetPartitions n) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hscalar_ne)]
    exact mul_pos (by grind) (singletonFreeSetPartitions_posLeadingCoeff n (by lia))
  have hder_pos :
      HasPosLeadingCoeff (singletonFreeSetPartitions (n + 1)).derivative :=
      (singletonFreeSetPartitions_posLeadingCoeff (n + 1) (by lia)).derivative (by
        rw [natDegree_singletonFreeSetPartitions (n + 1) (by lia)]
        lia)
  exact
    prec_add_of_prec_right_of_posLeadingCoeff
      hlower hder.toPrec hlower_pos hder_pos

lemma prec_singletonFreeSetPartitions_two_three :
    Prec (singletonFreeSetPartitions 2) (singletonFreeSetPartitions 3) :=
  by simpa [singletonFreeSetPartitions_two, singletonFreeSetPartitions_three] using
    prec_refl (f := X) (by simp)

lemma prec_singletonFreeSetPartitions_three_four :
    Prec (singletonFreeSetPartitions 3) (singletonFreeSetPartitions 4) := by
  have hlin : Interlaces (1 : ℝ[X]) (1 + C (3 : ℝ) * X) := by
    refine interlaces_one_linear ?_
    simpa [add_comm] using
      (Polynomial.natDegree_linear (a := (3 : ℝ)) (b := (1 : ℝ)) (by simp))
  have hprec : Prec (1 : ℝ[X]) (1 + C (3 : ℝ) * X) := hlin.toPrec
  have hone_nonpos : ∀ r ∈ (1 : ℝ[X]).roots, r ≤ 0 := by
    simp
  have hlin_nonneg : HasNonnegCoeffs (1 + C (3 : ℝ) * X) := by
    have hX_nonneg : HasNonnegCoeffs (X : ℝ[X]) := by
      rintro (_ | _ | m) <;> simp [coeff_X]
    have hCX_nonneg : HasNonnegCoeffs (C (3 : ℝ) * X) :=
      nonnegCoeffs_C_mul (by simp) hX_nonneg
    intro m
    exact add_nonneg (hasNonnegCoeffs_one m) (hCX_nonneg m)
  have hlin_nonpos : ∀ r ∈ (1 + C (3 : ℝ) * X).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hprec.2.1.2 hlin_nonneg
  have hmul :
      Prec (X * (1 : ℝ[X])) (X * (1 + C (3 : ℝ) * X)) :=
    prec_mul_X_both_of_roots_nonpos hprec hone_nonpos hlin_nonpos
  have hfour : singletonFreeSetPartitions 4 = X * (1 + C (3 : ℝ) * X) := by
    rw [singletonFreeSetPartitions_succ_succ_eq_X_mul_core, singletonFreeSetPartitionsCore,
      singletonFreeSetPartitions_two, singletonFreeSetPartitions_three]
    simp only [Nat.cast_ofNat, map_add, map_one, derivative_X, mul_eq_mul_left_iff,
      X_ne_zero, or_false]
    have hC : (C (2 : ℝ) + 1 : ℝ[X]) = C (3 : ℝ) := by
      ext m
      cases m with
      | zero =>
          norm_num
      | succ m =>
          rw [coeff_add, coeff_C, coeff_one]
          simp
    grind
  simpa [singletonFreeSetPartitions_three, hfour] using hmul

lemma prec_singletonFreeSetPartitions_succ_of_prec_core {n : Nat} (hn : 3 ≤ n)
    (hcore :
      Prec (singletonFreeSetPartitionsCore n) (singletonFreeSetPartitions (n + 1))) :
    Prec (singletonFreeSetPartitions (n + 1)) (singletonFreeSetPartitions (n + 2)) := by
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · have hsame :
        (singletonFreeSetPartitionsCore n).natDegree =
          (singletonFreeSetPartitions (n + 1)).natDegree := by
      rw [natDegree_singletonFreeSetPartitionsCore n,
        natDegree_singletonFreeSetPartitions (n + 1) (by lia)]
      lia
    have hcore_nonpos :
        ∀ r ∈ (singletonFreeSetPartitionsCore n).roots, r ≤ 0 :=
      roots_nonpos_singletonFreeSetPartitionsCore_of_isRealRooted hcore.1.2
    have hsucc_nonpos :
        ∀ r ∈ (singletonFreeSetPartitions (n + 1)).roots, r ≤ 0 :=
      roots_nonpos_singletonFreeSetPartitions_of_isRealRooted hcore.2.1.2
    have hmain :
        Prec (singletonFreeSetPartitions (n + 1))
          (X * singletonFreeSetPartitionsCore n) :=
      prec_sameDegree_to_prec_mul_X_of_roots_nonpos
        hcore hsame hcore_nonpos hsucc_nonpos
    simpa [singletonFreeSetPartitions_succ_succ_eq_X_mul_core n] using hmain
  · have hdeg :
        (singletonFreeSetPartitionsCore n).natDegree + 1 =
          (singletonFreeSetPartitions (n + 1)).natDegree := by
      rw [natDegree_singletonFreeSetPartitionsCore n,
        natDegree_singletonFreeSetPartitions (n + 1) (by lia)]
      lia
    have hmain :
        Prec (singletonFreeSetPartitions (n + 1))
          (X * singletonFreeSetPartitionsCore n) :=
      (prec_iff_prec_mul_X
        (singletonFreeSetPartitionsCore_nonnegCoeffs n)
        (singletonFreeSetPartitions_nonnegCoeffs (n + 1))
        hcore.1.1 hcore.1.2 hcore.2.1.1 hcore.2.1.2 hdeg).mp hcore
    simpa [singletonFreeSetPartitions_succ_succ_eq_X_mul_core n] using hmain

/-- Consecutive singleton-free set partition polynomials satisfy `Prec`. -/
theorem prec_singletonFreeSetPartitions_succ :
    ∀ n : Nat, 2 ≤ n →
      Prec (singletonFreeSetPartitions n) (singletonFreeSetPartitions (n + 1))
  | 0, hn => by
      lia
  | 1, hn => by
      lia
  | 2, _ => prec_singletonFreeSetPartitions_two_three
  | 3, _ => prec_singletonFreeSetPartitions_three_four
  | n + 4, _ => by
      have hprev :
          Prec (singletonFreeSetPartitions (n + 3))
            (singletonFreeSetPartitions (n + 4)) :=
        prec_singletonFreeSetPartitions_succ (n + 3) (by lia)
      have hcore :
          Prec (singletonFreeSetPartitionsCore (n + 3))
            (singletonFreeSetPartitions (n + 4)) :=
        prec_singletonFreeSetPartitionsCore_of_prec (n := n + 3) (by lia) hprev
      exact
        prec_singletonFreeSetPartitions_succ_of_prec_core
          (n := n + 3) (by lia) hcore

theorem isRealRooted_singletonFreeSetPartitions :
    ∀ n : Nat, 2 ≤ n → (singletonFreeSetPartitions n).Splits
  | 2, _ => by simp [singletonFreeSetPartitions_two]
  | n + 3, _ => by exact (prec_singletonFreeSetPartitions_succ (n + 2) (by lia)).2.1.2

theorem interlaces_singletonFreeSetPartitions_succ_of_odd {n : Nat}
    (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    Interlaces (singletonFreeSetPartitions n) (singletonFreeSetPartitions (n + 1)) :=
  (prec_singletonFreeSetPartitions_succ n (by lia)).toInterlaces <| by
    rw [natDegree_singletonFreeSetPartitions n (by lia),
      natDegree_singletonFreeSetPartitions (n + 1) (by lia)]
    lia

/-- The descending prefix `[D_{n+2}, D_{n+1}, ..., D_2]` of the nonzero
singleton-free set partition sequence. -/
def singletonFreeSetPartitionsPrefix : Nat → List ℝ[X]
  | 0 => [singletonFreeSetPartitions 2]
  | n + 1 =>
      singletonFreeSetPartitions (n + 3) :: singletonFreeSetPartitionsPrefix n

@[simp] lemma singletonFreeSetPartitionsPrefix_zero :
    singletonFreeSetPartitionsPrefix 0 = [singletonFreeSetPartitions 2] := rfl

@[simp] lemma singletonFreeSetPartitionsPrefix_succ (n : Nat) :
    singletonFreeSetPartitionsPrefix (n + 1) =
      singletonFreeSetPartitions (n + 3) :: singletonFreeSetPartitionsPrefix n := rfl

theorem isGeneralizedSturmSeq_singletonFreeSetPartitionsPrefix :
    ∀ n : Nat, IsGeneralizedSturmSeq (singletonFreeSetPartitionsPrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [singletonFreeSetPartitionsPrefix, IsGeneralizedSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simp [singletonFreeSetPartitionsPrefix, IsGeneralizedSturmSeq,
            prec_singletonFreeSetPartitions_two_three]
      | succ n =>
          simpa [singletonFreeSetPartitionsPrefix, IsGeneralizedSturmSeq] using
            And.intro
              (prec_singletonFreeSetPartitions_succ (n := n + 3) (by lia))
              ih

end RealRooted
