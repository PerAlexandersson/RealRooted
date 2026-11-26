/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Mesh
import RealRooted.CombinatorialExamples.LongCycleDescents.FiniteData
public import RealRooted.CombinatorialExamples.LongCycleDescents.Boundary
import RealRooted.CombinatorialExamples.LongCycleDescents.Exceptions
import RealRooted.CombinatorialExamples.LongCycleDescents.Mixtures
import Mathlib.Tactic

/-!
# The descent and mixture conclusions through size seventeen

The universal coefficient identities are proved in the preceding modules.
The finite certificates supply only integer-checked signs on small dyadic grids.
The structural transfer for sizes at least eighteen is separate from these checks.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

namespace RealRooted.LongCycleDescents.Finite

open Polynomial Finset Necklace

private theorem representative_checked {n k : ℕ} (hk : 3 ≤ k)
    {nodes : Array Necklace.Dyadic}
    (checked : ∀ i : Fin (lastRepresentative n - 2),
      descentMesh n (i.val + 3) nodes = true) :
    descentMesh n (min k (lastRepresentative n)) nodes = true := by
  let i : Fin (lastRepresentative n - 2) := ⟨min k (lastRepresentative n) - 3,
    (Nat.sub_le_sub_right (min_le_right ..) 3).trans_lt
      (Nat.sub_lt_sub_left (by exact (by decide : 2 < 3).trans_le (le_max_left ..))
        (by decide))⟩
  have eq : i.val + 3 = min k (lastRepresentative n) :=
    Nat.sub_add_cancel (le_min hk (le_max_left ..))
  simpa only [eq] using checked i

/-- A single negative grid isolates the roots of every quotient at each nonexceptional size. -/
theorem common_isolating_intervals {n : ℕ} (hn : 3 ≤ n) (hi : n ≤ 17) (five : n ≠ 5) :
    ∃ nodes : Array Necklace.Dyadic, nodes.size = n - 2 ∧
      StrictMono (fun i : Fin nodes.size ↦ (nodes.getD i.val Necklace.Dyadic.zero).value) ∧
      (∀ i : Fin nodes.size, (nodes.getD i.val Necklace.Dyadic.zero).value < 0) ∧
      ∀ k, 3 ≤ k → k ≤ n →
        ∃ q : ℝ[X], realDescentPolynomial n k = X * q ∧
          ∃ r : Fin (nodes.size - 1) → ℝ, StrictMono r ∧
            (∀ i, (nodes.getD i.val Necklace.Dyadic.zero).value < r i ∧
              r i < (nodes.getD (i.val + 1) Necklace.Dyadic.zero).value ∧ q.IsRoot (r i)) ∧
            ∀ z ∈ q.roots, ∃ i, z = r i := by
  obtain ⟨nodes, size, checked⟩ := exists_descentMesh hn hi five
  have cert := representative_checked (k := 3) (by decide) checked
  have mesh := (Bool.and_eq_true_iff.mp cert).2
  have count : nodes.size = nodes.size - 1 + 1 :=
    (Nat.sub_add_cancel (negativeMesh_size mesh).1).symm
  refine ⟨nodes, size, ?_, ?_, ?_⟩
  · intro i j hij
    exact negativeMesh_strictMono mesh
      (show Fin.cast count i < Fin.cast count j from hij)
  · intro i
    exact negativeMesh_node_neg mesh i.isLt
  · intro k hk kn
    have rowCert := representative_checked hk checked
    refine ⟨coefficientPolynomial (quotientCoefficients n (min k (lastRepresentative n))), ?_,
      negativeMesh_ordered_roots (Bool.and_eq_true_iff.mp rowCert).2⟩
    rw [realDescentPolynomial, row_eq_representative hk kn]
    exact row_eq_of_checkedCoeffs (by lia) (descentMesh_coefficients rowCert)

/-- Every long-cycle descent polynomial through size seventeen splits over the reals. -/
theorem realDescentPolynomial_splits {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n) (hi : n ≤ 17) :
    (realDescentPolynomial n k).Splits := by
  by_cases five : n = 5
  · subst n
    exact realDescentPolynomial_five_splits hk kn
  · obtain ⟨nodes, _, checked⟩ := exists_descentMesh (hk.trans kn) hi five
    rw [realDescentPolynomial, row_eq_representative hk kn]
    exact (descentMesh_splits (by lia) (representative_checked hk checked)).1

/-- Every original cutoff through size seventeen splits, including the classical endpoints. -/
theorem all_cutoffs_splits {n k : ℕ} (hk : 1 ≤ k) (kn : k ≤ n) (hi : n ≤ 17) :
    (realDescentPolynomial n k).Splits := by
  by_cases one : k = 1
  · subst k
    exact realDescentPolynomial_one_splits (by lia)
  · by_cases two : k = 2
    · subst k
      exact realDescentPolynomial_two_splits kn
    · exact realDescentPolynomial_splits (by lia) kn hi

/-- Away from size five, every such row has a simple zero and all remaining roots simple. -/
theorem realDescentPolynomial_roots {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n)
    (hi : n ≤ 17) (five : n ≠ 5) :
    (realDescentPolynomial n k).roots.Nodup ∧
      0 ∈ (realDescentPolynomial n k).roots ∧
      (realDescentPolynomial n k).natDegree = n - 2 ∧
      (∀ z ∈ (realDescentPolynomial n k).roots, z ≤ 0) := by
  obtain ⟨nodes, size, checked⟩ := exists_descentMesh (hk.trans kn) hi five
  rw [realDescentPolynomial, row_eq_representative hk kn]
  have result := (descentMesh_splits (by lia) (representative_checked hk checked)).2
  simpa only [size] using result

/-- Apart from zero, a nonexceptional row has exactly `n - 3` negative roots. -/
theorem card_negative_roots {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n)
    (hi : n ≤ 17) (five : n ≠ 5) :
    ((realDescentPolynomial n k).roots.filter (· < 0)).card = n - 3 := by
  classical
  have data := realDescentPolynomial_roots hk kn hi five
  have total := (splits_iff_card_roots.mp (realDescentPolynomial_splits hk kn hi))
  have zeros : ((realDescentPolynomial n k).roots.filter (fun z ↦ ¬z < 0)) = {0} := by
    have eq : ((realDescentPolynomial n k).roots.filter (fun z ↦ ¬z < 0)) =
        (realDescentPolynomial n k).roots.filter (0 = ·) := by
      apply Multiset.filter_congr
      intro z hz
      have nonpos := data.2.2.2 z hz
      constructor
      · intro h
        exact (le_antisymm nonpos (le_of_not_gt h)).symm
      · rintro rfl
        exact lt_irrefl _
    rw [eq, Multiset.filter_eq, Multiset.count_eq_one_of_mem data.1 data.2.1]
    rfl
  have partition := Multiset.filter_add_not (fun z : ℝ ↦ z < 0)
    (realDescentPolynomial n k).roots
  have count := congrArg Multiset.card partition
  rw [Multiset.card_add, zeros, Multiset.card_singleton, total, data.2.2.1] at count
  lia

/-- Nonzero nonnegative long-cutoff mixtures share the simple-root conclusion through size 17. -/
theorem mixture_splits {n : ℕ} (hn : 3 ≤ n) (hi : n ≤ 17) (five : n ≠ 5)
    (w : ℕ → ℝ) (hw : ∀ k ∈ Icc 3 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 3 n, 0 < w k) :
    let p := ∑ k ∈ Icc 3 n, C (w k) * realDescentPolynomial n k
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ (∀ z ∈ p.roots, z ≤ 0) := by
  obtain ⟨nodes, _, checked⟩ := exists_descentMesh hn hi five
  have cert k (hk : k ∈ Icc 3 n) :=
    representative_checked (mem_Icc.mp hk).1 checked
  have result := descentMesh_sum_splits (by lia : 0 < n) cert hw pos
  have eq : (∑ k ∈ Icc 3 n, C (w k) * realDescentPolynomial n k) =
      ∑ k ∈ Icc 3 n, C (w k) *
        (descentPolynomial n (min k (lastRepresentative n))).map (Int.castRingHom ℝ) := by
    apply sum_congr rfl
    intro k hk
    rw [realDescentPolynomial, row_eq_representative (mem_Icc.mp hk).1 (mem_Icc.mp hk).2]
  simpa only [eq] using result

end RealRooted.LongCycleDescents.Finite
