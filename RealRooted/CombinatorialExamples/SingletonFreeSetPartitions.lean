module

public import RealRooted.CombinatorialExamples.Common
public import RealRooted.Tactic.WagnerX
import RealRooted.Tactic.RowInterlacing
public import Mathlib.Tactic

/-!
# Singleton-Free Set-Partition Polynomials

Real-rootedness and interlacing facts for the recurrence counting set
partitions without singleton blocks.
-/

@[expose] public section

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

private def singletonFreeSetPartitionsTail : Nat → ℝ[X]
  | 0 => X
  | 1 => X
  | n + 2 =>
      (X * C ((n : ℝ) + 3)) * singletonFreeSetPartitionsTail n +
        X * (singletonFreeSetPartitionsTail (n + 1)).derivative

private lemma singletonFreeSetPartitionsTail_eq (n : Nat) :
    singletonFreeSetPartitionsTail n = singletonFreeSetPartitions (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [singletonFreeSetPartitionsTail, singletonFreeSetPartitions_two]
  | one => simp [singletonFreeSetPartitionsTail, singletonFreeSetPartitions_three]
  | more n ih₀ ih₁ =>
      rw [singletonFreeSetPartitionsTail, ih₀, ih₁,
        singletonFreeSetPartitions_succ_succ (n + 2)]
      push_cast
      ring_nf

private lemma singletonFreeSetPartitionsTail_natDegree (n : Nat) :
    (singletonFreeSetPartitionsTail n).natDegree = n / 2 + 1 := by
  rr_row_natDegree

private lemma singletonFreeSetPartitionsTail_posLeadingCoeff (n : Nat) :
    HasPosLeadingCoeff (singletonFreeSetPartitionsTail n) := by
  rr_row_leadingCoeff_pos

private lemma singletonFreeSetPartitionsTail_nonnegCoeffs :
    ∀ n : Nat, HasNonnegCoeffs (singletonFreeSetPartitionsTail n) := by
  rr_row_nonneg_coeffs

private lemma singletonFreeSetPartitionsTail_splits (n : Nat) :
    (singletonFreeSetPartitionsTail n).Splits := by
  rr_row_splits

private lemma singletonFreeSetPartitionsTail_strictInterl (n : Nat) :
    StrictInterl (singletonFreeSetPartitionsTail n)
      (singletonFreeSetPartitionsTail (n + 1)) := by
  apply derivativeLag_strictInterl_of_nonnegCoeffs_of_step
    (P := singletonFreeSetPartitionsTail) (U := fun _ => 0) (V := fun _ => X)
    (W := fun m => X * C ((m : ℝ) + 3))
  · intro m
    rw [singletonFreeSetPartitionsTail]
    ring_nf
  · intro m
    rw [singletonFreeSetPartitionsTail_natDegree,
      singletonFreeSetPartitionsTail_natDegree]
    lia
  · exact singletonFreeSetPartitionsTail_posLeadingCoeff
  · exact singletonFreeSetPartitionsTail_nonnegCoeffs
  · intro m x hx
    simp only [eval_X]
    exact hx
  · intro m x hx
    rw [eval_mul, eval_X, eval_C]
    exact mul_nonpos_of_nonpos_of_nonneg hx (by positivity)
  · simpa [singletonFreeSetPartitionsTail] using StrictInterl.refl (f := X) (by simp)

lemma coeff_singletonFreeSetPartitions_succ_succ (n m : Nat) :
    coeff (singletonFreeSetPartitions (n + 2)) (m + 1) =
      (n + 1 : ℝ) * coeff (singletonFreeSetPartitions n) m +
      (m + 1 : ℝ) * coeff (singletonFreeSetPartitions (n + 1)) (m + 1) := by
  rw [singletonFreeSetPartitions_succ_succ, coeff_X_mul, coeff_add]
  rw [coeff_C_mul, coeff_derivative]
  ring

lemma singletonFreeSetPartitions_nonnegCoeffs :
    ∀ n : Nat, HasNonnegCoeffs (singletonFreeSetPartitions n) := by
  rintro (_ | _ | n)
  · exact hasNonnegCoeffs_one
  · exact hasNonnegCoeffs_zero
  · rw [← singletonFreeSetPartitionsTail_eq]
    exact singletonFreeSetPartitionsTail_nonnegCoeffs n

lemma coeff_singletonFreeSetPartitions_top_pos_and_above :
    ∀ n : Nat, 2 ≤ n →
      0 < coeff (singletonFreeSetPartitions n) (n / 2) ∧
      ∀ m > n / 2, coeff (singletonFreeSetPartitions n) m = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k = k + 2 by lia, ← singletonFreeSetPartitionsTail_eq]
  have hdeg := singletonFreeSetPartitionsTail_natDegree k
  have hpos := singletonFreeSetPartitionsTail_posLeadingCoeff k
  constructor
  · simpa [HasPosLeadingCoeff, leadingCoeff, hdeg] using hpos
  · intro m hm
    exact coeff_eq_zero_of_natDegree_lt (by lia)

lemma natDegree_singletonFreeSetPartitions (n : Nat) (hn : 2 ≤ n) :
    (singletonFreeSetPartitions n).natDegree = n / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k = k + 2 by lia, ← singletonFreeSetPartitionsTail_eq,
    singletonFreeSetPartitionsTail_natDegree]
  lia

lemma singletonFreeSetPartitions_nonzero (n : Nat) (hn : 2 ≤ n) :
    singletonFreeSetPartitions n ≠ 0 := by
  rcases coeff_singletonFreeSetPartitions_top_pos_and_above n hn with ⟨htop, _⟩
  exact fun h0 => by simp [h0] at htop

lemma singletonFreeSetPartitions_posLeadingCoeff (n : Nat) (hn : 2 ≤ n) :
    HasPosLeadingCoeff (singletonFreeSetPartitions n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k = k + 2 by lia, ← singletonFreeSetPartitionsTail_eq]
  exact singletonFreeSetPartitionsTail_posLeadingCoeff k

/-- The inner recurrence core
`(n+1) D_n(X) + D'_{n+1}(X)` for singleton-free set partitions. -/
def singletonFreeSetPartitionsCore (n : Nat) : ℝ[X] :=
  C (n + 1 : ℝ) * singletonFreeSetPartitions n +
    (singletonFreeSetPartitions (n + 1)).derivative

lemma singletonFreeSetPartitions_succ_succ_eq_X_mul_core (n : Nat) :
    singletonFreeSetPartitions (n + 2) = X * singletonFreeSetPartitionsCore n :=
  rfl

lemma singletonFreeSetPartitionsCore_nonnegCoeffs (n : Nat) :
    HasNonnegCoeffs (singletonFreeSetPartitionsCore n) := by
  intro m
  rw [singletonFreeSetPartitionsCore, coeff_add, coeff_C_mul]
  exact add_nonneg
    (mul_nonneg (by positivity) (singletonFreeSetPartitions_nonnegCoeffs n m))
    ((singletonFreeSetPartitions_nonnegCoeffs (n + 1)).derivative m)

lemma singletonFreeSetPartitionsCore_ne_zero (n : Nat) :
    singletonFreeSetPartitionsCore n ≠ 0 := by
  have hsucc_ne : singletonFreeSetPartitions (n + 2) ≠ 0 :=
    singletonFreeSetPartitions_nonzero (n + 2) (by lia)
  rw [singletonFreeSetPartitions_succ_succ_eq_X_mul_core n] at hsucc_ne
  simp_all

lemma strictInterl_singletonFreeSetPartitionsCore_of_strictInterl {n : Nat} (hn : 3 ≤ n)
    (hprev : StrictInterl (singletonFreeSetPartitions n) (singletonFreeSetPartitions (n + 1))) :
    StrictInterl (singletonFreeSetPartitionsCore n) (singletonFreeSetPartitions (n + 1)) := by
  rw [singletonFreeSetPartitionsCore]
  have hscalar_ne : (n + 1 : ℝ) ≠ 0 := by positivity
  have hlower :
      StrictInterl (C (n + 1 : ℝ) * singletonFreeSetPartitions n)
        (singletonFreeSetPartitions (n + 1)) :=
    StrictInterl.C_mul_left hprev hscalar_ne
  have hder :
      Interlaces (singletonFreeSetPartitions (n + 1)).derivative
        (singletonFreeSetPartitions (n + 1)) :=
    derivative_interlaces_of_natDegree_ne_zero hprev.2.1.2 <| by
      rw [natDegree_singletonFreeSetPartitions (n + 1) (by lia)]
      lia
  have hlower_pos :
      HasPosLeadingCoeff (C (n + 1 : ℝ) * singletonFreeSetPartitions n) :=
    hasPosLeadingCoeff_C_mul (by positivity)
      (singletonFreeSetPartitions_posLeadingCoeff n (by lia))
  have hder_pos :
      HasPosLeadingCoeff (singletonFreeSetPartitions (n + 1)).derivative :=
      (singletonFreeSetPartitions_posLeadingCoeff (n + 1) (by lia)).derivative (by
        rw [natDegree_singletonFreeSetPartitions (n + 1) (by lia)]
        lia)
  exact
    StrictInterl.add_of_right_of_posLeadingCoeff
      hlower hder.toStrictInterl hlower_pos hder_pos

lemma strictInterl_singletonFreeSetPartitions_two_three :
    StrictInterl (singletonFreeSetPartitions 2) (singletonFreeSetPartitions 3) :=
  by simpa [singletonFreeSetPartitionsTail_eq] using
    singletonFreeSetPartitionsTail_strictInterl 0

lemma strictInterl_singletonFreeSetPartitions_three_four :
    StrictInterl (singletonFreeSetPartitions 3) (singletonFreeSetPartitions 4) :=
  by simpa [singletonFreeSetPartitionsTail_eq] using
    singletonFreeSetPartitionsTail_strictInterl 1

lemma strictInterl_singletonFreeSetPartitions_succ_of_strictInterl_core {n : Nat}
    (hcore :
      StrictInterl (singletonFreeSetPartitionsCore n) (singletonFreeSetPartitions (n + 1))) :
    StrictInterl (singletonFreeSetPartitions (n + 1)) (singletonFreeSetPartitions (n + 2)) := by
  have hmain :
      StrictInterl (singletonFreeSetPartitions (n + 1))
        (X * singletonFreeSetPartitionsCore n) := by
    rr_strict_interl_mul_X using
      proper := hcore,
      left_nonneg := singletonFreeSetPartitionsCore_nonnegCoeffs n,
      right_nonneg := singletonFreeSetPartitions_nonnegCoeffs (n + 1)
  simpa [singletonFreeSetPartitions_succ_succ_eq_X_mul_core n] using hmain

/-- Consecutive singleton-free set partition polynomials satisfy `StrictInterl`. -/
theorem strictInterl_singletonFreeSetPartitions_succ :
    ∀ n : Nat, 2 ≤ n →
      StrictInterl (singletonFreeSetPartitions n) (singletonFreeSetPartitions (n + 1)) := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := singletonFreeSetPartitionsTail_strictInterl k
  rw [singletonFreeSetPartitionsTail_eq k,
    singletonFreeSetPartitionsTail_eq (k + 1)] at h
  convert h using 1 <;> lia

theorem isRealRooted_singletonFreeSetPartitions :
    ∀ n : Nat, 2 ≤ n → (singletonFreeSetPartitions n).Splits := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := singletonFreeSetPartitionsTail_splits k
  rw [singletonFreeSetPartitionsTail_eq] at h
  convert h using 1
  lia

theorem interlaces_singletonFreeSetPartitions_succ_of_odd {n : Nat}
    (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    Interlaces (singletonFreeSetPartitions n) (singletonFreeSetPartitions (n + 1)) :=
  (strictInterl_singletonFreeSetPartitions_succ n (by lia)).toInterlaces <| by
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
            strictInterl_singletonFreeSetPartitions_two_three]
      | succ n =>
          simpa [singletonFreeSetPartitionsPrefix, IsGeneralizedSturmSeq] using
            And.intro
              (strictInterl_singletonFreeSetPartitions_succ (n := n + 3) (by lia))
              ih

end RealRooted
