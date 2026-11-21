module

public import RealRooted.MatrixInterlacing.VariableLastRow
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Partial-product transitions

The strict upper-triangular partial-product matrix has nonnegative ordered minors.
Appending a variable row preserves interlacing when its successive weights satisfy
`q (j + 1) ≤ r j * q j`. This includes repeated or zero parameters.

Source: the mutually interlacing induction in the unpublished RealRooted issue #2415.
-/

@[expose] public section

open Finset Polynomial

namespace RealRooted

/-- The rectangular partial-product transition, including its last scalar column. -/
noncomputable def partialProductMatrix (r : ℕ → ℝ) (m : ℕ) (N : ℝ) :
    Fin m → Fin (m + 1) → ℝ :=
  fun i j => if (i : ℕ) < j then N * ∏ k ∈ Ico ((i : ℕ) + 1) (j : ℕ), r k else 0

/-- Every entry of a partial-product transition is nonnegative. -/
theorem partialProductMatrix_nonneg {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) (i : Fin m) (j : Fin (m + 1)) :
    0 ≤ partialProductMatrix r m N i j := by
  unfold partialProductMatrix
  split_ifs
  · exact mul_nonneg hN (prod_nonneg fun k _ => hr k)
  · exact le_rfl

/-- All ordered two-by-two minors of the partial-product transition are nonnegative. -/
theorem partialProductMatrix_isTP2 {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) : Matrix.IsTP2 (partialProductMatrix r m N) := by
  refine ⟨partialProductMatrix_nonneg hr hN, ?_⟩
  intro a b c d hab hcd
  by_cases hbc : (b : ℕ) < c
  · have hac : (a : ℕ) < c := lt_trans hab hbc
    have hbd : (b : ℕ) < d := lt_trans hbc hcd
    have had : (a : ℕ) < d := lt_trans hac hcd
    simp only [partialProductMatrix, ite_eq_left hac, ite_eq_left hbc, ite_eq_left had,
      ite_eq_left hbd]
    rw [← prod_Ico_consecutive r (by lia : (a : ℕ) + 1 ≤ (c : ℕ)) hcd.le,
      ← prod_Ico_consecutive r (by lia : (b : ℕ) + 1 ≤ (c : ℕ)) hcd.le]
    ring_nf
    exact le_rfl
  · have hzero : partialProductMatrix r m N b c = 0 := by
      simp [partialProductMatrix, hbc]
    rw [hzero, mul_zero, sub_zero]
    exact mul_nonneg (partialProductMatrix_nonneg hr hN _ _)
      (partialProductMatrix_nonneg hr hN _ _)

private lemma le_mul_prod_of_succ_le {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m : ℕ}
    (hstep : ∀ k, k + 1 < m → q (k + 1) ≤ r k * q k)
    {j k : ℕ} (hjk : j ≤ k) (hk : k < m) :
    q k ≤ (∏ l ∈ Ico j k, r l) * q j := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    have hprev := ih (by lia)
    rw [prod_Ico_succ_top hjk]
    calc
      q (k + 1) ≤ r k * q k := hstep k hk
      _ ≤ r k * ((∏ l ∈ Ico j k, r l) * q j) :=
        mul_le_mul_of_nonneg_left hprev (hr k)
      _ = ((∏ l ∈ Ico j k, r l) * r k) * q j := by ring

/-- The monotone weight condition certifies the full partial-product matrix step. -/
theorem partialProductMatrix_variableLastRow_preserves {r q : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) {m : ℕ} (hq : ∀ k < m, 0 ≤ q k)
    (hstep : ∀ k, k + 1 < m → q (k + 1) ≤ r k * q k)
    {N : ℝ} (hN : 0 ≤ N) :
    PreservesInterlacingSeq0 (m + 1)
      (variableLastRowMatrix (partialProductMatrix r m N) (fun j => q j)) := by
  apply variableLastRowMatrix_preserves (partialProductMatrix_isTP2 hr hN)
    (fun j => hq j j.isLt)
  intro i j k hjk
  by_cases hij : (i : ℕ) < j
  · have hik : (i : ℕ) < k := lt_of_lt_of_le hij hjk
    simp only [partialProductMatrix, Fin.val_castSucc, ite_eq_left hij, ite_eq_left hik]
    rw [← prod_Ico_consecutive r (by lia : (i : ℕ) + 1 ≤ (j : ℕ)) hjk]
    have h := le_mul_prod_of_succ_le hr hstep hjk k.isLt
    have hnonneg : 0 ≤ N * ∏ l ∈ Ico ((i : ℕ) + 1) (j : ℕ), r l :=
      mul_nonneg hN (prod_nonneg fun l _ => hr l)
    nlinarith [mul_le_mul_of_nonneg_left h hnonneg]
  · have hzero : partialProductMatrix r m N i j.castSucc = 0 := by
      simp [partialProductMatrix, hij]
    rw [hzero, zero_mul]
    exact mul_nonneg (partialProductMatrix_nonneg hr hN _ _) (hq j j.isLt)

/-- Adjacent rows of the partial-product matrix satisfy the linear-factor recursion. -/
theorem partialProductMatrix_row_succ (r : ℕ → ℝ) {m i : ℕ} (hi : i + 1 < m)
    (N : ℝ) (j : Fin (m + 1)) :
    partialProductMatrix r m N ⟨i, by lia⟩ j =
      r (i + 1) * partialProductMatrix r m N ⟨i + 1, hi⟩ j +
        if (j : ℕ) = i + 1 then N else 0 := by
  by_cases hji : (j : ℕ) ≤ i
  · have h₁ : ¬ i < (j : ℕ) := by lia
    have h₂ : ¬ i + 1 < (j : ℕ) := by lia
    have h₃ : (j : ℕ) ≠ i + 1 := by lia
    simp [partialProductMatrix, h₁, h₂, h₃]
  · by_cases hj : (j : ℕ) = i + 1
    · simp [partialProductMatrix, hj]
    · have h₁ : i < (j : ℕ) := by lia
      have h₂ : i + 1 < (j : ℕ) := by lia
      simp only [partialProductMatrix, ite_eq_left h₁, ite_eq_left h₂, ite_eq_right hj,
        add_zero]
      rw [prod_eq_prod_Ico_succ_bot h₂]
      ring

/-- Matrix action on adjacent auxiliary rows obeys the linear-factor recursion. -/
theorem partialProductMatrix_action_succ (r : ℕ → ℝ) {m i : ℕ} (hi : i + 1 < m)
    (N : ℝ) (f : Fin (m + 1) → ℝ[X]) :
    (∑ j, C (partialProductMatrix r m N ⟨i, by lia⟩ j) * f j) =
      C (r (i + 1)) * (∑ j, C (partialProductMatrix r m N ⟨i + 1, hi⟩ j) * f j) +
        C N * f ⟨i + 1, by lia⟩ := by
  classical
  have hterm (j : Fin (m + 1)) :
      C (partialProductMatrix r m N ⟨i, by lia⟩ j) * f j =
        C (r (i + 1)) * (C (partialProductMatrix r m N ⟨i + 1, hi⟩ j) * f j) +
          if j = ⟨i + 1, by lia⟩ then C N * f j else 0 := by
    rw [partialProductMatrix_row_succ r hi N j]
    have hj : (j : ℕ) = i + 1 ↔ j = (⟨i + 1, by lia⟩ : Fin (m + 1)) := by
      constructor
      · intro h
        exact Fin.ext h
      · exact fun h => congrArg Fin.val h
    by_cases h : j = (⟨i + 1, by lia⟩ : Fin (m + 1))
    · simp only [ite_eq_left h, ite_eq_left (hj.mpr h), map_add, map_mul]
      ring
    · have h' : (j : ℕ) ≠ i + 1 := fun heq => h (hj.mp heq)
      simp only [ite_eq_right h, ite_eq_right h', map_mul, add_zero]
      ring
  simp_rw [hterm]
  simp [sum_add_distrib, mul_sum]

end RealRooted
