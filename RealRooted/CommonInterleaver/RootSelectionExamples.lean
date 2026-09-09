import RealRooted.CommonInterleaver.RootSelectionTree
import RealRooted.WagnerX.AffineFactors

/-!
# Examples for MSS root selection

These exact low-degree examples exercise positive selection, zero weights,
singleton trees, and the necessity of a common interlacer rather than mere
real-rootedness of the sum.
-/

open Polynomial

noncomputable section

namespace RealRooted

open LiuOppositeSigns

private theorem prec_X_X_mul_X_sub_C (r : ℝ) :
    Prec X (X * (X - C r) : ℝ[X]) := by
  have hbase : Prec (1 : ℝ[X]) (X - C r) :=
    (interlaces_one_linear (by simp)).toPrec
  simpa using prec_mul_X_sub_C_both (0 : ℝ) hbase

private theorem natDegree_X_mul_X_sub_C (r : ℝ) :
    (X * (X - C r) : ℝ[X]).natDegree = 2 := by
  rw [Polynomial.natDegree_mul isRealRooted_X.1 (isRealRooted_X_sub_C r).1]
  simp

private theorem posLeading_X_mul_X_sub_C (r : ℝ) :
    HasPosLeadingCoeff (X * (X - C r) : ℝ[X]) := by
  rw [mul_comm]
  exact hasPosLeadingCoeff_X_sub_C_mul (by simp [HasPosLeadingCoeff])

private theorem largestRoot_X_mul_X_sub_C {r : ℝ} (hr : 0 ≤ r) :
    IsLargestRoot (X * (X - C r) : ℝ[X]) r := by
  refine ⟨by simp [Polynomial.IsRoot.def], ?_⟩
  intro s hs
  rw [Polynomial.roots_mul
    (mul_ne_zero isRealRooted_X.1 (isRealRooted_X_sub_C r).1)] at hs
  simp only [Polynomial.roots_X, Polynomial.roots_X_sub_C,
    Multiset.mem_add, Multiset.mem_singleton] at hs
  rcases hs with rfl | rfl <;> linarith

private theorem largestRoot_two_linear {a b : ℝ} (hab : a ≤ b) :
    IsLargestRoot ((X - C a) * (X - C b) : ℝ[X]) b := by
  refine ⟨by simp [Polynomial.IsRoot.def], ?_⟩
  intro s hs
  rw [Polynomial.roots_mul
    (mul_ne_zero (isRealRooted_X_sub_C a).1 (isRealRooted_X_sub_C b).1)] at hs
  simp only [Polynomial.roots_X_sub_C, Multiset.mem_add, Multiset.mem_singleton] at hs
  rcases hs with rfl | rfl <;> linarith

/-- The first polynomial in this pair has largest root `1`, below the largest
root `2` of the sum; the second member has largest root `3`. -/
theorem rootSelection_quadratic_example :
    let f := X * (X - C 1 : ℝ[X])
    let g := X * (X - C 3 : ℝ[X])
    ∃ rf rsum, IsLargestRoot f rf ∧ IsLargestRoot (f + g) rsum ∧ rf ≤ rsum := by
  dsimp
  refine ⟨1, 2, largestRoot_X_mul_X_sub_C (by norm_num), ?_, by norm_num⟩
  have hsum :
      (X * (X - C 1) + X * (X - C 3) : ℝ[X]) =
        C 2 * (X * (X - C 2)) := by
    norm_num [map_ofNat]
    ring
  rw [hsum]
  exact (largestRoot_X_mul_X_sub_C (by norm_num)).C_mul (by norm_num)

/-- The quadratic pair satisfies the explicit common-left degree-gap
hypothesis used by the selector theorem. -/
theorem quadratic_example_commonLeftInterlacer :
    HasCommonLeftInterlacerOfDegree
      [X * (X - C 1 : ℝ[X]), X * (X - C 3 : ℝ[X])] 2 := by
  refine ⟨X, by simp, ?_⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact prec_X_X_mul_X_sub_C 1
  · exact prec_X_X_mul_X_sub_C 3

/-- Appending a zero-weight member still returns a member of strictly positive
support. -/
theorem rootSelection_zero_weight_example :
    ∃ ap ∈ [((0 : ℝ), X * (X - C 3 : ℝ[X])),
        ((1 : ℝ), X * (X - C 1 : ℝ[X]))],
      0 < ap.1 ∧ ∃ rp rsum,
        IsLargestRoot ap.2 rp ∧
          IsLargestRoot (weightedSum
            [((0 : ℝ), X * (X - C 3 : ℝ[X])),
              ((1 : ℝ), X * (X - C 1 : ℝ[X]))]) rsum ∧
          rp ≤ rsum := by
  apply exists_mem_largestRoot_le_weightedSum (h := X) (d := 2)
  · simp
  · norm_num
  · intro ap hap
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
    rcases hap with rfl | rfl
    · simpa only [Prod.snd] using prec_X_X_mul_X_sub_C 3
    · simpa only [Prod.snd, Polynomial.C_1] using prec_X_X_mul_X_sub_C 1
  · intro ap hap
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
    rcases hap with rfl | rfl
    · simpa only [Prod.snd] using natDegree_X_mul_X_sub_C 3
    · simpa only [Prod.snd, Polynomial.C_1] using natDegree_X_mul_X_sub_C 1
  · intro ap hap
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
    rcases hap with rfl | rfl
    · simpa only [Prod.snd] using posLeading_X_mul_X_sub_C 3
    · simpa only [Prod.snd, Polynomial.C_1] using posLeading_X_mul_X_sub_C 1
  · exact ⟨((1 : ℝ), X * (X - C 1 : ℝ[X])), by simp⟩

/-- A singleton leaf is a valid positive-degree tree and selects itself. -/
theorem rootSelection_singleton_tree_example :
    ∃ p ∈ (RootSelectionTree.leaf (X - C 1 : ℝ[X])).leaves,
      ∃ rp rt, IsLargestRoot p rp ∧
        IsLargestRoot (RootSelectionTree.leaf (X - C 1 : ℝ[X])).polynomial rt ∧
          rp ≤ rt := by
  apply RootSelectionTree.Valid.exists_leaf_largestRoot_le
    (d := 1) (t := .leaf (X - C 1))
  · exact .leaf (natDegree_X_sub_C 1) (isRealRooted_X_sub_C 1).2
      (hasPosLeadingCoeff_X_sub_C 1)
  · norm_num

/-- A two-child tree packages the quadratic common-interlacing example. -/
theorem rootSelection_two_child_tree_example :
    let t := RootSelectionTree.node
      [.leaf (X * (X - C 1 : ℝ[X])), .leaf (X * (X - C 3 : ℝ[X]))]
    ∃ p ∈ t.leaves, ∃ rp rt,
      IsLargestRoot p rp ∧ IsLargestRoot t.polynomial rt ∧ rp ≤ rt := by
  dsimp
  apply RootSelectionTree.Valid.exists_leaf_largestRoot_le (d := 2)
  · apply RootSelectionTree.Valid.node (by simp)
    · intro child hchild
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl
      · exact .leaf (natDegree_X_mul_X_sub_C 1)
          (prec_X_X_mul_X_sub_C 1).2.1.2 (posLeading_X_mul_X_sub_C 1)
      · exact .leaf (natDegree_X_mul_X_sub_C 3)
          (prec_X_X_mul_X_sub_C 3).2.1.2 (posLeading_X_mul_X_sub_C 3)
    · simpa [RootSelectionTree.polynomial] using quadratic_example_commonLeftInterlacer
  · norm_num

/-- The first polynomial in the exact guardrail against selection from
real-rootedness of a sum alone. -/
def rootSelectionGuardF : ℝ[X] := C 14 * (X * (X - C 1))

/-- The second polynomial in the exact guardrail against selection from
real-rootedness of a sum alone. -/
def rootSelectionGuardG : ℝ[X] := (X - C 2) * (X - C 3)

private theorem rootSelection_guard_sum :
    rootSelectionGuardF + rootSelectionGuardG =
      C 15 * ((X - C (3 / 5 : ℝ)) * (X - C (2 / 3 : ℝ))) := by
  apply Polynomial.funext
  intro x
  simp only [rootSelectionGuardF, rootSelectionGuardG, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  ring

/-- Real-rootedness of the members and their sum alone does not imply the MSS
selection conclusion: the sum's largest root is `2/3`, below both member
largest roots `1` and `3`. -/
theorem realRooted_sum_not_enough_for_rootSelection :
    rootSelectionGuardF.Splits ∧ rootSelectionGuardG.Splits ∧
      (rootSelectionGuardF + rootSelectionGuardG).Splits ∧
      ¬ ∃ p ∈ [rootSelectionGuardF, rootSelectionGuardG],
        ∃ rp rsum, IsLargestRoot p rp ∧
          IsLargestRoot (rootSelectionGuardF + rootSelectionGuardG) rsum ∧
            rp ≤ rsum := by
  have hf_rr : rootSelectionGuardF ≠ 0 ∧ rootSelectionGuardF.Splits := by
    unfold rootSelectionGuardF
    exact isRealRooted_C_mul_of_isRealRooted
      (isRealRooted_X_mul_of_isRealRooted (isRealRooted_X_sub_C 1)) (by norm_num)
  have hg_rr : rootSelectionGuardG ≠ 0 ∧ rootSelectionGuardG.Splits := by
    unfold rootSelectionGuardG
    exact isRealRooted_mul (isRealRooted_X_sub_C 2).1 (isRealRooted_X_sub_C 2).2
      (isRealRooted_X_sub_C 3).1 (isRealRooted_X_sub_C 3).2
  have hsum_rr :
      rootSelectionGuardF + rootSelectionGuardG ≠ 0 ∧
        (rootSelectionGuardF + rootSelectionGuardG).Splits := by
    rw [rootSelection_guard_sum]
    exact isRealRooted_C_mul_of_isRealRooted
      (isRealRooted_mul (isRealRooted_X_sub_C (3 / 5 : ℝ)).1
        (isRealRooted_X_sub_C (3 / 5 : ℝ)).2
        (isRealRooted_X_sub_C (2 / 3 : ℝ)).1
        (isRealRooted_X_sub_C (2 / 3 : ℝ)).2) (by norm_num)
  refine ⟨hf_rr.2, hg_rr.2, hsum_rr.2, ?_⟩
  rintro ⟨p, hp, rp, rsum, hrp, hrsum, hrp_le⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  have hf_largest : IsLargestRoot rootSelectionGuardF 1 := by
    unfold rootSelectionGuardF
    exact (largestRoot_X_mul_X_sub_C (by norm_num)).C_mul (by norm_num)
  have hg_largest : IsLargestRoot rootSelectionGuardG 3 := by
    unfold rootSelectionGuardG
    exact largestRoot_two_linear (by norm_num)
  have hsum_largest :
      IsLargestRoot (rootSelectionGuardF + rootSelectionGuardG) (2 / 3 : ℝ) := by
    rw [rootSelection_guard_sum]
    exact (largestRoot_two_linear (by norm_num)).C_mul (by norm_num)
  have hrsum_eq : rsum = (2 / 3 : ℝ) :=
    hrsum.unique hsum_rr.1 hsum_largest
  rcases hp with rfl | rfl
  · have hrp_eq : rp = 1 := hrp.unique hf_rr.1 hf_largest
    norm_num [hrp_eq, hrsum_eq] at hrp_le
  · have hrp_eq : rp = 3 := hrp.unique hg_rr.1 hg_largest
    norm_num [hrp_eq, hrsum_eq] at hrp_le

end RealRooted
