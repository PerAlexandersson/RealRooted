import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite elementary-symmetric algebra

The elementary symmetric functions of a finite initial segment and its leading
partial products. This discrete layer is independent of roots and logarithms.
-/

namespace RealRooted.CoefficientDominance.Symmetric

open Finset

/-- The `j`-th elementary symmetric function of `x 0, ..., x (n - 1)`. -/
noncomputable def esym (x : ℕ → ℝ) (n j : ℕ) : ℝ :=
  ∑ S ∈ (range n).powersetCard j, ∏ i ∈ S, x i

/-- The leading partial product `x 0 ⋯ x (j - 1)`. -/
noncomputable def topProd (x : ℕ → ℝ) (j : ℕ) : ℝ := ∏ i ∈ range j, x i

theorem topProd_pos {x : ℕ → ℝ} (hpos : ∀ i, 0 < x i) (j : ℕ) :
    0 < topProd x j :=
  prod_pos (fun i _ => hpos i)

/-- The leading product is one nonnegative summand of the elementary symmetric
function. -/
theorem topProd_le_esym {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {n j : ℕ} (hj : j ≤ n) :
    topProd x j ≤ esym x n j := by
  refine single_le_sum (f := fun S => ∏ i ∈ S, x i)
    (fun S _ => prod_nonneg (fun i _ => hx i)) ?_
  rw [mem_powersetCard]
  refine ⟨?_, card_range j⟩
  intro i hi
  simp only [mem_range] at hi ⊢
  lia

theorem esym_pos {x : ℕ → ℝ} (hpos : ∀ i, 0 < x i) {n j : ℕ} (hj : j ≤ n) :
    0 < esym x n j := by
  have h1 : 0 < topProd x j := topProd_pos hpos j
  have h2 : topProd x j ≤ esym x n j :=
    topProd_le_esym (x := x) (fun i => (hpos i).le) hj
  linarith

/-- The second difference of leading products records a consecutive ratio. -/
theorem topProd_sq {x : ℕ → ℝ} (hpos : ∀ i, 0 < x i) (j : ℕ) :
    (topProd x (j + 1)) ^ 2
      = topProd x j * topProd x (j + 2) * (x j / x (j + 1)) := by
  have h1 : topProd x (j + 1) = topProd x j * x j := by
    simp [topProd, prod_range_succ]
  have h2 : topProd x (j + 2) = topProd x j * x j * x (j + 1) := by
    simp [topProd, prod_range_succ]
  rw [h1, h2]
  have hne : x (j + 1) ≠ 0 := ne_of_gt (hpos (j + 1))
  field_simp

/-- The elementary symmetric functions satisfy the usual add-one-variable
recurrence. -/
theorem esym_succ (x : ℕ → ℝ) (n j : ℕ) :
    esym x (n + 1) (j + 1) = esym x n (j + 1) + x n * esym x n j := by
  classical
  have hins : range (n + 1) = insert n (range n) := by
    ext y
    simp only [mem_range, Finset.mem_insert]
    lia
  have hnot : n ∉ range n := by simp
  have hdisj : Disjoint (powersetCard (j + 1) (range n))
      ((powersetCard j (range n)).image (insert n)) := by
    refine Finset.disjoint_left.mpr (fun S hS hT => ?_)
    rw [mem_powersetCard] at hS
    rw [Finset.mem_image] at hT
    obtain ⟨U, _, rfl⟩ := hT
    exact hnot (hS.1 (Finset.mem_insert_self n U))
  have hinj : ∀ S ∈ powersetCard j (range n), ∀ T ∈ powersetCard j (range n),
      insert n S = insert n T → S = T := by
    intro S hS T hT hEq
    rw [mem_powersetCard] at hS hT
    have hnS : n ∉ S := fun h => hnot (hS.1 h)
    have hnT : n ∉ T := fun h => hnot (hT.1 h)
    have h := congrArg (fun U => Finset.erase U n) hEq
    simpa [Finset.erase_insert hnS, Finset.erase_insert hnT] using h
  rw [esym, hins, Finset.powersetCard_succ_insert hnot, Finset.sum_union hdisj,
    Finset.sum_image hinj, esym, esym, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [mem_powersetCard] at hS
  have hnS : n ∉ S := fun h => hnot (hS.1 h)
  rw [Finset.prod_insert hnS]

@[simp] theorem esym_zero (x : ℕ → ℝ) (n : ℕ) : esym x n 0 = 1 := by
  rw [esym, Finset.powersetCard_zero]
  simp

/-- The generating-function expansion of finite elementary symmetric values. -/
theorem prod_one_add_eq_sum (x : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    ∏ i ∈ range n, (1 + x i * t) = ∑ k ∈ range (n + 1), esym x n k * t ^ k := by
  have h1 : ∏ i ∈ range n, (1 + x i * t)
      = ∑ U ∈ (range n).powerset, ∏ i ∈ U, (x i * t) := by
    rw [show ∏ i ∈ range n, (1 + x i * t) = ∏ i ∈ range n, (x i * t + 1) from
      Finset.prod_congr rfl (fun i _ => by ring), Finset.prod_add]
    exact Finset.sum_congr rfl (fun U _ => by simp)
  rw [h1, Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  rw [card_range]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [esym, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun U hU => ?_)
  rw [mem_powersetCard] at hU
  rw [Finset.prod_mul_distrib, Finset.prod_const, hU.2]

end RealRooted.CoefficientDominance.Symmetric
