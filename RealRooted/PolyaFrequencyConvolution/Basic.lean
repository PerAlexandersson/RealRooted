import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.FinTruncation
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Cauchy convolution of Pólya-frequency sequences

This file identifies finite lower-Toeplitz truncation multiplication with
Cauchy convolution and proves that Pólya-frequency sequences are closed under
that operation.
-/

open Matrix

namespace RealRooted

/-- Cauchy convolution of two sequences indexed by the natural numbers. -/
def natCauchyConvolution (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- Coefficients of a product of power series are the Cauchy convolution of
their coefficient sequences. -/
theorem coeff_mul_eq_natCauchyConvolution (F G : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (F * G) =
      natCauchyConvolution (fun k => PowerSeries.coeff k F)
        (fun k => PowerSeries.coeff k G) n := by
  rw [PowerSeries.coeff_mul]
  simpa [natCauchyConvolution] using
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p => PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G) n

/-- The finite principal truncation of a lower-Toeplitz matrix. -/
def toeplitzFin (a : ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (toeplitz a).submatrix Fin.val Fin.val

@[simp]
lemma toeplitzFin_apply (a : ℕ → ℝ) (N : ℕ) (i j : Fin (N + 1)) :
    toeplitzFin a N i j = if j ≤ i then a (i - j) else 0 := by
  simp [toeplitzFin, toeplitz_apply]

/-- Multiplication of finite lower-Toeplitz truncations realizes Cauchy
convolution without losing any summands. -/
theorem toeplitzFin_mul (a b : ℕ → ℝ) (N : ℕ) :
    toeplitzFin a N * toeplitzFin b N =
      toeplitzFin (natCauchyConvolution a b) N := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [toeplitzFin_apply]
  by_cases hji : j.val ≤ i.val
  · rw [if_pos (Fin.le_def.mpr hji)]
    unfold natCauchyConvolution
    calc
      (∑ l : Fin (N + 1),
          (if l ≤ i then a (i.val - l.val) else 0) *
            if j ≤ l then b (l.val - j.val) else 0) =
          ∑ l ∈ Finset.Icc j i,
            (if l ≤ i then a (i.val - l.val) else 0) *
              if j ≤ l then b (l.val - j.val) else 0 := by
            symm
            apply Finset.sum_subset
            · intro l hl
              exact Finset.mem_univ l
            · intro l _ hl
              by_cases hli : l ≤ i
              · have hlj : ¬j ≤ l := fun h =>
                  hl (Finset.mem_Icc.mpr ⟨h, hli⟩)
                simp [hli, hlj]
              · simp [hli]
      _ = ∑ k ∈ Finset.range (i.val - j.val + 1),
          a k * b (i.val - j.val - k) := by
        apply Finset.sum_bij (fun l _ => i.val - l.val)
        · intro l hl
          have hl' := Finset.mem_Icc.mp hl
          have hjl : j.val ≤ l.val := Fin.le_def.mp hl'.1
          have hli : l.val ≤ i.val := Fin.le_def.mp hl'.2
          exact Finset.mem_range.mpr (by lia)
        · intro l₁ hl₁ l₂ hl₂ heq
          have hl₁' := Finset.mem_Icc.mp hl₁
          have hl₂' := Finset.mem_Icc.mp hl₂
          have hl₁i : l₁.val ≤ i.val := Fin.le_def.mp hl₁'.2
          have hl₂i : l₂.val ≤ i.val := Fin.le_def.mp hl₂'.2
          apply Fin.ext
          lia
        · intro k hk
          have hk' := Finset.mem_range.mp hk
          let l : Fin (N + 1) :=
            ⟨i.val - k, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
          refine ⟨l, Finset.mem_Icc.mpr ?_, ?_⟩
          · constructor
            · apply Fin.le_iff_val_le_val.mpr
              dsimp [l]
              lia
            · apply Fin.le_iff_val_le_val.mpr
              dsimp [l]
              exact Nat.sub_le _ _
          · dsimp [l]
            lia
        · intro l hl
          have hl' := Finset.mem_Icc.mp hl
          have hjl : j.val ≤ l.val := Fin.le_def.mp hl'.1
          have hli : l.val ≤ i.val := Fin.le_def.mp hl'.2
          rw [if_pos hl'.2, if_pos hl'.1]
          rw [show i.val - j.val - (i.val - l.val) = l.val - j.val by lia]
  · rw [if_neg (fun h => hji (Fin.le_def.mp h))]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hli : l ≤ i
    · have hlj : ¬j ≤ l := fun h => hji (Fin.le_def.mp (h.trans hli))
      simp [hli, hlj]
    · simp [hli]

/-- Pólya-frequency sequences are closed under Cauchy convolution. -/
protected theorem IsPolyaFreqSeq.natCauchyConvolution
    {a b : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (hb : IsPolyaFreqSeq b) :
    IsPolyaFreqSeq (natCauchyConvolution a b) := by
  rw [IsPolyaFreqSeq]
  apply Matrix.IsTotallyNonneg.of_fin_truncations
    (Mfin := fun N => toeplitzFin a N * toeplitzFin b N)
  · intro N i j
    rw [toeplitzFin_mul]
    rfl
  · intro N
    exact Matrix.IsTotallyNonneg.mul
      (ha.submatrix Fin.val_strictMono Fin.val_strictMono)
      (hb.submatrix Fin.val_strictMono Fin.val_strictMono)

end RealRooted
