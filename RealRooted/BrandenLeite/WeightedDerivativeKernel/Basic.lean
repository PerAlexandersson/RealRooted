module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
public import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularRankDeficient
import Mathlib.Tactic

/-! Weighted derivative kernels and their ordered incidence contractions. -/

@[expose] public section

open Matrix

namespace RealRooted.BrandenLeite

/-- The differential coefficient kernel with coefficients extended by zero
below index zero. -/
def weightedDerivativeKernel {R : Type*} [CommRing R] (κ : R) (f : ℕ → R) :
    Matrix ℕ ℕ R :=
  fun i j ↦ if j ≤ i + 1 then ((j : R) + κ * (i + 1 - j : ℕ)) * f (i + 1 - j)
    else 0

@[simp]
theorem weightedDerivativeKernel_apply_zero {R : Type*} [CommRing R]
    (κ : R) (f : ℕ → R) (i : ℕ) :
    weightedDerivativeKernel κ f i 0 = κ * (i + 1 : ℕ) * f (i + 1) := by
  simp [weightedDerivativeKernel]

/-- The contraction sends source indices `0`, `1,2`, `3,4`, ... to
successive target columns. -/
def derivativeContractionBlock (n : ℕ) : Fin (2 * n + 1) → Fin (n + 1) :=
  fun k ↦ ⟨(k.val + 1) / 2, by have := k.isLt; lia⟩

/-- Even source columns have weight `κ`; odd source columns have weight
one plus their half-index. -/
def derivativeContractionWeight {n : ℕ} (κ : ℝ) (k : Fin (2 * n + 1)) : ℝ :=
  if k.val % 2 = 0 then κ else ((k.val + 1) / 2 : ℕ)

/-- The finite matrix contracting a derivative/value column pair. -/
def derivativeContraction (n : ℕ) (κ : ℝ) :
    Matrix (Fin (2 * n + 1)) (Fin (n + 1)) ℝ :=
  weightedIncidence (derivativeContractionBlock n) (derivativeContractionWeight κ)

/-- The contraction block map respects the source order. -/
theorem monotone_derivativeContractionBlock (n : ℕ) :
    Monotone (derivativeContractionBlock n) := by
  intro i j hij
  change (i.val + 1) / 2 ≤ (j.val + 1) / 2
  exact Nat.div_le_div_right (Nat.add_le_add_right hij 1)

/-- The derivative/value contraction is totally nonnegative for nonnegative
weight, by the existing monotone incidence theorem. -/
theorem derivativeContraction_isTotallyNonnegRect (n : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    (derivativeContraction n κ).IsTotallyNonnegRect := by
  apply isTotallyNonnegRect_monotoneWeightedIncidence _
    (monotone_derivativeContractionBlock n)
  intro k
  unfold derivativeContractionWeight
  split_ifs
  · exact hκ
  · positivity

/-- The contraction maps source column `k` to target column `j` exactly for the two
columns `2 * j - 1` and `2 * j`. -/
theorem derivativeContractionBlock_eq_iff {n : ℕ} (k : Fin (2 * n + 1)) (j : Fin (n + 1)) :
    derivativeContractionBlock n k = j ↔ k.val = 2 * j.val ∨ k.val + 1 = 2 * j.val := by
  rw [Fin.ext_iff]
  change (k.val + 1) / 2 = j.val ↔ _
  lia

/-- Each column of the weighted derivative contraction uses the indicated
one or two source columns. -/
theorem mul_derivativeContraction_apply {m n : ℕ}
    (U : Matrix (Fin m) (Fin (2 * n + 1)) ℝ) (κ : ℝ)
    (i : Fin m) (j : Fin (n + 1)) :
    (U * derivativeContraction n κ) i j =
      U i ⟨2 * j.val, by have := j.isLt; lia⟩ * κ +
      if hj : j.val = 0 then 0
      else U i ⟨2 * j.val - 1, by have := j.isLt; lia⟩ * (j.val : ℝ) := by
  classical
  let e : Fin (2 * n + 1) := ⟨2 * j.val, by have := j.isLt; lia⟩
  have he : derivativeContractionBlock n e = j :=
    (derivativeContractionBlock_eq_iff e j).mpr (Or.inl rfl)
  have hwe : derivativeContractionWeight κ e = κ := by
    simp [derivativeContractionWeight, e]
  rw [Matrix.mul_apply]
  change (∑ k, U i k * weightedIncidence (derivativeContractionBlock n)
    (derivativeContractionWeight κ) k j) = _
  by_cases hj : j.val = 0
  · rw [dite_eq_left hj, Finset.sum_eq_single e]
    · simp only [weightedIncidence_apply, he, ite_true, hwe, add_zero]
      rfl
    · intro k _ hke
      have hk : derivativeContractionBlock n k ≠ j := fun h => hke (Fin.ext (by
        have := (derivativeContractionBlock_eq_iff k j).mp h
        simp only [e]
        lia))
      simp [weightedIncidence_apply, hk]
    · simp
  · rw [dite_eq_right hj]
    let o : Fin (2 * n + 1) := ⟨2 * j.val - 1, by have := j.isLt; lia⟩
    have ho : derivativeContractionBlock n o = j :=
      (derivativeContractionBlock_eq_iff o j).mpr (Or.inr (by simp only [o]; lia))
    have hwo : derivativeContractionWeight κ o = (j.val : ℝ) := by
      have hp : (2 * j.val - 1) % 2 ≠ 0 := by lia
      have hq : (2 * j.val - 1 + 1) / 2 = j.val := by lia
      simp [derivativeContractionWeight, o, hp, hq]
    have hoe : o ≠ e := by
      intro h
      have hv := congrArg Fin.val h
      simp only [o, e] at hv
      lia
    have hsum : (∑ k, U i k * weightedIncidence (derivativeContractionBlock n)
        (derivativeContractionWeight κ) k j) =
        ∑ k ∈ ({o, e} : Finset (Fin (2 * n + 1))),
          U i k * weightedIncidence (derivativeContractionBlock n)
            (derivativeContractionWeight κ) k j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      have hkblock : derivativeContractionBlock n k ≠ j := fun h => hk (by
        have hkv := (derivativeContractionBlock_eq_iff k j).mp h
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hkv with hkv | hkv
        · exact Or.inr (Fin.ext hkv)
        · exact Or.inl (Fin.ext (by simp only [o]; lia)))
      simp [weightedIncidence_apply, hkblock]
    rw [hsum]
    simp only [Finset.sum_pair hoe, weightedIncidence_apply, he, ho, ite_true, hwe, hwo]
    exact add_comm _ _

end RealRooted.BrandenLeite
