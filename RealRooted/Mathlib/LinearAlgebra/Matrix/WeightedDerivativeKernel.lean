module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
public import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularRankDeficient
import Mathlib.Tactic

/-! Weighted derivative kernels and their ordered incidence contractions. -/

@[expose] public section

namespace Matrix

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
  have he : derivativeContractionBlock n e = j := by
    apply Fin.ext
    simp only [derivativeContractionBlock, e]
    lia
  have hwe : derivativeContractionWeight κ e = κ := by
    simp [derivativeContractionWeight, e]
  rw [Matrix.mul_apply]
  change (∑ k, U i k * weightedIncidence (derivativeContractionBlock n)
    (derivativeContractionWeight κ) k j) = _
  by_cases hj : j.val = 0
  · rw [dite_eq_left hj]
    rw [Finset.sum_eq_single e]
    · simp only [weightedIncidence_apply, he, ite_true, hwe, add_zero]
      rfl
    · intro k _ hke
      have hk : derivativeContractionBlock n k ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        have hkv : k.val = 0 := by
          change (k.val + 1) / 2 = j.val at hv
          lia
        apply hke
        apply Fin.ext
        simp only [e]
        lia
      simp [weightedIncidence_apply, hk]
    · simp
  · rw [dite_eq_right hj]
    let o : Fin (2 * n + 1) := ⟨2 * j.val - 1, by have := j.isLt; lia⟩
    have ho : derivativeContractionBlock n o = j := by
      apply Fin.ext
      simp only [derivativeContractionBlock, o]
      lia
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
      have hkblock : derivativeContractionBlock n k ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        change (k.val + 1) / 2 = j.val at hv
        have hcases : k = o ∨ k = e := by
          have hkv : k.val = 2 * j.val - 1 ∨ k.val = 2 * j.val := by lia
          rcases hkv with hkv | hkv
          · exact Or.inl (Fin.ext hkv)
          · exact Or.inr (Fin.ext hkv)
        exact hk (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hcases)
      simp [weightedIncidence_apply, hkblock]
    rw [hsum]
    simp only [Finset.sum_pair hoe, weightedIncidence_apply, he, ho, ite_true, hwe, hwo]
    exact add_comm _ _


end Matrix
