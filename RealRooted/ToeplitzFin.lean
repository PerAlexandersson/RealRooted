module

public import RealRooted.AissenSchoenbergWhitneyBase
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Finite Toeplitz truncations

This file gives the shared finite lower-Toeplitz truncation and its
power-series multiplication formula.
-/

@[expose] public noncomputable section

open Matrix BigOperators

namespace RealRooted

/-- The finite principal truncation of a lower-Toeplitz matrix. -/
def toeplitzFin {R : Type*} [Zero R]
    (a : ℕ → R) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  (toeplitz a).submatrix Fin.val Fin.val

@[simp]
theorem toeplitzFin_apply {R : Type*} [Zero R]
    (a : ℕ → R) (N : ℕ) (i j : Fin (N + 1)) :
    toeplitzFin a N i j = if j ≤ i then a (i.val - j.val) else 0 := by
  simp [toeplitzFin, toeplitz_apply]

/-- Finite Toeplitz truncation commutes exactly with Cauchy multiplication. -/
theorem toeplitzFin_mul_coeff {R : Type*} [CommSemiring R]
    (a b : ℕ → R) (N : ℕ) :
    toeplitzFin a N * toeplitzFin b N =
      toeplitzFin
        (fun n => PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b)) N := by
  ext i j
  by_cases hji : j ≤ i
  · rw [Matrix.mul_apply, toeplitzFin_apply, ite_eq_left hji]
    simp only [toeplitzFin_apply]
    simp only [Fin.le_iff_val_le_val]
    change (∑ k : Fin (N + 1),
      (fun m : ℕ =>
        (if m ≤ i.val then a (i.val - m) else 0) *
          if j.val ≤ m then b (m - j.val) else 0) k.val) = _
    calc
      (∑ k : Fin (N + 1),
          (fun m : ℕ =>
            (if m ≤ i.val then a (i.val - m) else 0) *
              if j.val ≤ m then b (m - j.val) else 0) k.val) =
          ∑ k ∈ Finset.range (N + 1),
            (if k ≤ i.val then a (i.val - k) else 0) *
              if j.val ≤ k then b (k - j.val) else 0 :=
        Fin.sum_univ_eq_sum_range
          (fun m : ℕ =>
            (if m ≤ i.val then a (i.val - m) else 0) *
              if j.val ≤ m then b (m - j.val) else 0)
          (N + 1)
      (∑ k ∈ Finset.range (N + 1),
          (if k ≤ i.val then a (i.val - k) else 0) *
            if j.val ≤ k then b (k - j.val) else 0) =
          ∑ k ∈ Finset.Ico j.val (i.val + 1),
            (if k ≤ i.val then a (i.val - k) else 0) *
              if j.val ≤ k then b (k - j.val) else 0 := by
        symm
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
          exact hk.2.trans_le i.isLt
        · intro k hkRange hkIco
          simp only [Finset.mem_Ico, not_and_or, not_lt, not_le] at hkIco
          rcases hkIco with hkj | hik
          · simp [hkj]
          · simp [show ¬ k ≤ i.val by lia]
      _ =
          ∑ k ∈ Finset.Ico j.val (i.val + 1),
            a (i.val - k) * b (k - j.val) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_Ico] at hk
        simp [hk.1, show k ≤ i.val by lia]
      _ = ∑ k ∈ Finset.range (i.val + 1 - j.val),
            a (i.val - (j.val + k)) * b k := by
        rw [Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < i.val + 1 - j.val := Finset.mem_range.mp hk
        congr 2
        lia
      _ = ∑ k ∈ Finset.range (i.val - j.val + 1),
            a (i.val - j.val - k) * b k := by
        have hsize : i.val + 1 - j.val = i.val - j.val + 1 := by lia
        rw [hsize]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.sub_sub]
      _ = PowerSeries.coeff (i.val - j.val)
          (PowerSeries.mk a * PowerSeries.mk b) := by
        rw [mul_comm (PowerSeries.mk a) (PowerSeries.mk b)]
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp [mul_comm]
  · rw [toeplitzFin_apply, ite_eq_right hji, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k ≤ i
    · have hjk : ¬ j ≤ k := fun hjk => hji (hjk.trans hki)
      simp [toeplitzFin_apply, hki, hjk]
    · simp [toeplitzFin_apply, hki]

end RealRooted
