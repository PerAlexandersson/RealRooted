/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.InventoryEquation
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

/-!
# The canonical alphabet coefficient recurrence

A finite Euler equation determines every coefficient in its jet. This identifies
the recurrence with the original alphabet polynomial without an infinite-product
assumption or a caller-supplied combinatorial identity.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

/-- The length-divisor kernel at a fixed outer degree. -/
def alphabetKernel (k i : ℕ) : ℚ[X] :=
  ∑ j ∈ range i, if k ≤ j + 1 ∧ j + 1 ∣ i then
    ((j + 1 : ℕ) : ℚ[X]) * necklacePolynomial (j + 1) else 0

private theorem coeff_expanded_inventoryKernel {H j i : ℕ} (hj : 0 < j) (hi : i ≤ H)
    (M : ℚ[X]) :
    (expand ℚ[X] j (inventoryKernel H M)).coeff i =
      if i = 0 then 0 else if j ∣ i then M else 0 := by
  rw [coeff_expand hj, coeff_inventoryKernel ((Nat.div_le_self i j).trans hi)]
  by_cases hz : i = 0
  · simp [hz]
  · by_cases hd : j ∣ i
    · rw [ite_eq_left hd, ite_eq_right hz,
        ite_eq_right (Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hd) hj)),
        ite_eq_left hd]
    · simp [hz, hd]

/-- Every finite jet has the same kernel coefficients in its valid degree range. -/
theorem coeff_alphabetProductKernel {H i : ℕ} (hi : i ≤ H) (k : ℕ) :
    (alphabetProductKernel H k).coeff i = alphabetKernel k i := by
  classical
  simp only [alphabetProductKernel, finsetSum_coeff]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    (((j + 1 : ℕ) : ℚ[X][X]) * expand ℚ[X] (j + 1)
      (inventoryKernel H (if j + 1 < k then 0 else necklacePolynomial (j + 1)))).coeff i)]
  have he (j : ℕ) :
      (((j + 1 : ℕ) : ℚ[X][X]) * expand ℚ[X] (j + 1)
        (inventoryKernel H (if j + 1 < k then 0 else necklacePolynomial (j + 1)))).coeff i =
      if i = 0 then 0 else if k ≤ j + 1 ∧ j + 1 ∣ i then
        ((j + 1 : ℕ) : ℚ[X]) * necklacePolynomial (j + 1) else 0 := by
    rw [← C_eq_natCast, coeff_C_mul,
      coeff_expanded_inventoryKernel (Nat.succ_pos _) hi]
    by_cases hz : i = 0
    · simp [hz]
    · by_cases hd : j + 1 ∣ i <;> by_cases hk : j + 1 < k <;> simp [hz, hd, hk, not_lt.mp]
  simp_rw [he]
  by_cases hz : i = 0
  · simp [hz, alphabetKernel]
  · simp only [ite_eq_right hz]
    unfold alphabetKernel
    symm
    apply sum_subset (range_mono hi)
    intro j _ hj
    apply ite_eq_right
    rintro ⟨_, hd⟩
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hd
    have hn : i ≤ j := by simpa only [mem_range, not_lt] using hj
    lia

/-- Rational alphabet coefficients defined by their Euler recurrence. -/
def alphabetRow (k n : ℕ) : ℚ[X] :=
  match n with
  | 0 => 1
  | m + 1 => C (((m + 1 : ℕ) : ℚ)⁻¹) *
      ∑ i : Fin (m + 1), alphabetKernel k (m + 1 - i.val) * alphabetRow k i.val
termination_by n

@[simp] theorem alphabetRow_zero (k : ℕ) : alphabetRow k 0 = 1 := by rw [alphabetRow]

/-- The defining recurrence with its positive integer denominator cleared. -/
theorem alphabetRow_equation (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ[X]) * alphabetRow k n =
      ∑ i ∈ range n, alphabetKernel k (n - i) * alphabetRow k i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [alphabetRow, ← C_eq_natCast, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ (by positivity : ((m + 1 : ℕ) : ℚ) ≠ 0), C_1, one_mul,
    Fin.sum_univ_eq_sum_range (fun i => alphabetKernel k (m + 1 - i) * alphabetRow k i)]

private theorem alphabetProduct_coeff_zero (H k : ℕ) : (alphabetProduct H k).coeff 0 = 1 := by
  rw [alphabetProduct, coeff_zero_prod]
  apply prod_eq_one
  intro i _
  rw [coeff_expand (Nat.succ_pos _)]
  simp [coeff_inventoryFactor]

/-- Euler uniqueness identifies every finite-product jet with the canonical row. -/
theorem alphabetProduct_coeff_eq_row {H n : ℕ} (hn : n ≤ H) (k : ℕ) :
    (alphabetProduct H k).coeff n = alphabetRow k n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hz : n = 0
    · subst n
      rw [alphabetProduct_coeff_zero, alphabetRow_zero]
    · have hp := X_pow_dvd_iff.mp (alphabetProduct_equation H k) n (by lia)
      rw [coeff_sub, coeff_X_mul_derivative, mul_comm (alphabetProductKernel H k), coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
        Nat.sub_self, coeff_alphabetProductKernel (Nat.zero_le H)] at hp
      simp only [alphabetKernel, range_zero, sum_empty, mul_zero, add_zero] at hp
      have he : (∑ i ∈ range n, (alphabetProduct H k).coeff i *
          (alphabetProductKernel H k).coeff (n - i)) =
          ∑ i ∈ range n, alphabetKernel k (n - i) * alphabetRow k i := by
        apply sum_congr rfl
        intro i hi
        have hin := mem_range.mp hi
        rw [ih i hin (by lia), coeff_alphabetProductKernel (by lia : n - i ≤ H)]
        ring
      rw [he] at hp
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hz : (n : ℚ[X]) ≠ 0)
      exact (sub_eq_zero.mp hp).symm.trans (alphabetRow_equation k hz).symm

/-- The canonical row is the genuine rational Gessel--Reutenauer alphabet polynomial. -/
theorem alphabetRow_eq_cycleAlphabet (n k : ℕ) : alphabetRow k n = cycleAlphabet n k := by
  rw [← alphabetProduct_coeff_eq_row le_rfl, alphabetProduct_coeff]

/-- The recurrence computes the original real alphabet polynomial for every positive size. -/
theorem map_alphabetRow {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (alphabetRow k n).map (Rat.castHom ℝ) = descentAlphabetPolynomial n k := by
  rw [alphabetRow_eq_cycleAlphabet, map_cycleAlphabet hn]

end RealRooted.LongCycleDescents.Structural
