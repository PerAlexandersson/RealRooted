import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import RealRooted.JacobiDeformation.AppellJacobiDifferential
import RealRooted.JacobiDeformation.AppellSummandCoordinates

/-!
# Appell coordinates and the finite Jacobi deformation polynomial

The finite triangular reindexing converts the released scalar Appell-coordinate
identity into an equality of the actual polynomial evaluations.
-/

open Finset Polynomial
open scoped BigOperators

namespace RealRooted.JacobiDeformation

private theorem sum_antidiagonal_triangle (m : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l, f ij.1 ij.2 (m - l)) =
      ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
        if i + j ≤ m then f i j (m - i - j) else 0 := by
  calc
    (∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l, f ij.1 ij.2 (m - l)) =
        ∑ x ∈ (range (m + 1)).sigma antidiagonal,
          f x.2.1 x.2.2 (m - x.1) := by
      rw [Finset.sum_sigma']
    _ = ∑ ij ∈ ((range (m + 1) ×ˢ range (m + 1)).filter fun ij => ij.1 + ij.2 ≤ m),
          f ij.1 ij.2 (m - ij.1 - ij.2) := by
      refine Finset.sum_bij (fun x _ => x.2) ?_ ?_ ?_ ?_
      · rintro ⟨l, ij⟩ h
        rcases Finset.mem_sigma.mp h with ⟨hl, hij⟩
        have hl' := Finset.mem_range.mp hl
        have hsum := Finset.mem_antidiagonal.mp hij
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩
        · lia
        · lia
        · lia
      · rintro ⟨l, ij⟩ h ⟨l', ij'⟩ h' heq
        rcases Finset.mem_sigma.mp h with ⟨_, hij⟩
        rcases Finset.mem_sigma.mp h' with ⟨_, hij'⟩
        dsimp at heq
        subst ij'
        have hsum := Finset.mem_antidiagonal.mp hij
        have hsum' := Finset.mem_antidiagonal.mp hij'
        have hll : l = l' := by lia
        subst l'
        rfl
      · intro ij hij
        rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
        refine ⟨⟨ij.1 + ij.2, ij⟩, Finset.mem_sigma.mpr ?_, rfl⟩
        refine ⟨Finset.mem_range.mpr ?_, Finset.mem_antidiagonal.mpr rfl⟩
        exact by lia
      · rintro ⟨l, ij⟩ h
        rcases Finset.mem_sigma.mp h with ⟨_, hij⟩
        have hsum := Finset.mem_antidiagonal.mp hij
        dsimp
        congr 1
        lia
    _ = ∑ ij ∈ range (m + 1) ×ˢ range (m + 1),
          if ij.1 + ij.2 ≤ m then f ij.1 ij.2 (m - ij.1 - ij.2) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
          if i + j ≤ m then f i j (m - i - j) else 0 := by
      rw [Finset.sum_product]

private theorem sum_range_reverse_antidiagonal (m : ℕ) (xi : ℝ)
    (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ range (m + 1), ∑ ij ∈ antidiagonal (m - k), f ij.1 ij.2 * xi ^ k) =
      ∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l, f ij.1 ij.2 * xi ^ (m - l) := by
  let g : ℕ → ℝ := fun l => ∑ ij ∈ antidiagonal l, f ij.1 ij.2 * xi ^ (m - l)
  calc
    (∑ k ∈ range (m + 1), ∑ ij ∈ antidiagonal (m - k), f ij.1 ij.2 * xi ^ k) =
        ∑ k ∈ range (m + 1), g (m - k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp only [g]
      have hkm : k ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
      rw [Nat.sub_sub_self hkm]
    _ = ∑ l ∈ range (m + 1), g l := by
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect g (m + 1)
    _ = ∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l, f ij.1 ij.2 * xi ^ (m - l) := by
      rfl

/-- The actual Jacobi deformation evaluated at `xi` is the actual Appell
Jacobi kernel at the scalar coordinate substitution. -/
theorem polynomial_eval_eq_appellJacobiKernel_coordinates (m : ℕ)
    (δ c d U V xi r z : ℝ) (hU : xi * r * z = -U)
    (hV : xi * (1 - r) * (1 - z) = -V) :
    (polynomial m δ c d U V).eval xi =
      (-1 : ℝ) ^ m * xi ^ m *
        (appellJacobiKernel m ((m : ℝ) + c + d - 1 + δ) c d z).eval r := by
  calc
    (polynomial m δ c d U V).eval xi =
        ∑ k ∈ range (m + 1), ∑ ij ∈ antidiagonal (m - k),
          summand m δ c d U V ij.1 ij.2 * xi ^ k := by
      unfold polynomial
      rw [eval_finsetSum]
      refine Finset.sum_congr rfl ?_
      intro k _
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      rw [Finset.sum_mul]
    _ = ∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l,
          summand m δ c d U V ij.1 ij.2 * xi ^ (m - l) :=
      sum_range_reverse_antidiagonal m xi (summand m δ c d U V)
    _ = ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
          if i + j ≤ m then summand m δ c d U V i j * xi ^ (m - i - j) else 0 :=
      sum_antidiagonal_triangle m (fun i j k => summand m δ c d U V i j * xi ^ k)
    _ = (-1 : ℝ) ^ m * xi ^ m *
          appellKernelValue m ((m : ℝ) + c + d - 1 + δ) c d
            (r * z) ((1 - r) * (1 - z)) := by
      unfold appellKernelValue
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hij : i + j ≤ m
      · rw [ite_eq_left hij]
        have h := appellKernelCoefficient_coordinate_eq_summand
          m i j δ c d U V xi r z hij hU hV
        ring_nf at h ⊢
        exact h.symm
      · rw [ite_eq_right hij, appellKernelCoefficient, ite_eq_right hij]
        ring
    _ = (-1 : ℝ) ^ m * xi ^ m *
          (appellJacobiKernel m ((m : ℝ) + c + d - 1 + δ) c d z).eval r := by
      rw [eval_appellJacobiKernel]

end RealRooted.JacobiDeformation
