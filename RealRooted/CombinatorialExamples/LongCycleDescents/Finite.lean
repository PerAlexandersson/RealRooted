/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Boundary
public import RealRooted.CombinatorialExamples.LongCycleDescents.Counting
import Mathlib.Tactic

/-!
# Finite long-cycle descent certificates

Kernel-checked integer tables and common negative grids cover sizes through seventeen.
All root conclusions refer to the original permutation sums.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

@[expose] public noncomputable section

namespace RealRooted.LongCycleDescents.Finite

open Necklace

/-- A common negative quotient grid at size 3. -/
private def nodes3 : Array Necklace.Dyadic :=
#[
  ⟨-1, 0⟩
]

private theorem checked3 (k : Fin (3 - 2)) :
    descentMesh 3 (k.val + 3) nodes3 = true := by
  fin_cases k; decide +kernel

/-- A common negative quotient grid at size 4. -/
private def nodes4 : Array Necklace.Dyadic :=
#[
  ⟨-11640527, 22⟩,
  ⟨-6045151, 24⟩
]

private theorem checked4 (k : Fin (3 - 2)) :
    descentMesh 4 (k.val + 3) nodes4 = true := by
  fin_cases k; decide +kernel

/-- A common negative quotient grid at size 6. -/
private def nodes6 : Array Necklace.Dyadic :=
#[
  ⟨-12842623, 20⟩,
  ⟨-4295759, 21⟩,
  ⟨-4095245, 23⟩,
  ⟨-10958625, 27⟩
]

private theorem checked6 (k : Fin (4 - 2)) :
    descentMesh 6 (k.val + 3) nodes6 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 7. -/
private def nodes7 : Array Necklace.Dyadic :=
#[
  ⟨-12132387, 19⟩,
  ⟨-481563, 17⟩,
  ⟨-1, 0⟩,
  ⟨-4566429, 24⟩,
  ⟨-2900037, 26⟩
]

private theorem checked7 (k : Fin (4 - 2)) :
    descentMesh 7 (k.val + 3) nodes7 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 8. -/
private def nodes8 : Array Necklace.Dyadic :=
#[
  ⟨-11080015, 18⟩,
  ⟨-12863317, 21⟩,
  ⟨-14597089, 23⟩,
  ⟨-2410369, 22⟩,
  ⟨-10940995, 26⟩,
  ⟨-6350961, 28⟩
]

private theorem checked8 (k : Fin (5 - 2)) :
    descentMesh 8 (k.val + 3) nodes8 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 9. -/
private def nodes9 : Array Necklace.Dyadic :=
#[
  ⟨-9894933, 17⟩,
  ⟨-2569315, 18⟩,
  ⟨-11640527, 22⟩,
  ⟨-1, 0⟩,
  ⟨-6045151, 24⟩,
  ⟨-13694067, 27⟩,
  ⟨-14223187, 30⟩
]

private theorem checked9 (k : Fin (5 - 2)) :
    descentMesh 9 (k.val + 3) nodes9 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 10. -/
private def nodes10 : Array Necklace.Dyadic :=
#[
  ⟨-4349717, 15⟩,
  ⟨-15952867, 20⟩,
  ⟨-2201201, 19⟩,
  ⟨-6589123, 22⟩,
  ⟨-10679531, 24⟩,
  ⟨-7992085, 25⟩,
  ⟨-8822081, 27⟩,
  ⟨-1011111, 27⟩
]

private theorem checked10 (k : Fin (6 - 2)) :
    descentMesh 10 (k.val + 3) nodes10 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 11. -/
private def nodes11 : Array Necklace.Dyadic :=
#[
  ⟨-3780847, 14⟩,
  ⟨-12132387, 19⟩,
  ⟨-12863317, 21⟩,
  ⟨-9732927, 22⟩,
  ⟨-1, 0⟩,
  ⟨-14459935, 25⟩,
  ⟨-10940995, 26⟩,
  ⟨-2900037, 26⟩,
  ⟨-4652975, 30⟩
]

private theorem checked11 (k : Fin (6 - 2)) :
    descentMesh 11 (k.val + 3) nodes11 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 12. -/
private def nodes12 : Array Necklace.Dyadic :=
#[
  ⟨-13033225, 15⟩,
  ⟨-1136351, 15⟩,
  ⟨-4584911, 19⟩,
  ⟨-13807009, 22⟩,
  ⟨-12284435, 23⟩,
  ⟨-5728285, 23⟩,
  ⟨-1274149, 22⟩,
  ⟨-15347897, 27⟩,
  ⟨-15481297, 29⟩,
  ⟨-10798363, 32⟩
]

private theorem checked12 (k : Fin (7 - 2)) :
    descentMesh 12 (k.val + 3) nodes12 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 13. -/
private def nodes13 : Array Necklace.Dyadic :=
#[
  ⟨-5578875, 13⟩,
  ⟨-1683929, 15⟩,
  ⟨-12842623, 20⟩,
  ⟨-1190115, 18⟩,
  ⟨-4295759, 21⟩,
  ⟨-1, 0⟩,
  ⟨-4095245, 23⟩,
  ⟨-14781921, 26⟩,
  ⟨-10958625, 27⟩,
  ⟨-10447107, 29⟩,
  ⟨-12613429, 33⟩
]

private theorem checked13 (k : Fin (7 - 2)) :
    descentMesh 13 (k.val + 3) nodes13 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 14. -/
private def nodes14 : Array Necklace.Dyadic :=
#[
  ⟨-9502315, 13⟩,
  ⟨-9894933, 17⟩,
  ⟨-554549, 15⟩,
  ⟨-12863317, 21⟩,
  ⟨-11640527, 22⟩,
  ⟨-5835279, 22⟩,
  ⟨-12059191, 24⟩,
  ⟨-6045151, 24⟩,
  ⟨-10940995, 26⟩,
  ⟨-7930853, 27⟩,
  ⟨-14223187, 30⟩,
  ⟨-925679, 30⟩
]

private theorem checked14 (k : Fin (8 - 2)) :
    descentMesh 14 (k.val + 3) nodes14 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 15. -/
private def nodes15 : Array Necklace.Dyadic :=
#[
  ⟨-16117061, 13⟩,
  ⟨-7217943, 16⟩,
  ⟨-12132387, 19⟩,
  ⟨-8555533, 20⟩,
  ⟨-481563, 17⟩,
  ⟨-15670441, 23⟩,
  ⟨-1, 0⟩,
  ⟨-1122635, 21⟩,
  ⟨-4566429, 24⟩,
  ⟨-16449881, 27⟩,
  ⟨-2900037, 26⟩,
  ⟨-9749141, 30⟩,
  ⟨-4366103, 33⟩
]

private theorem checked15 (k : Fin (8 - 2)) :
    descentMesh 15 (k.val + 3) nodes15 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 16. -/
private def nodes16 : Array Necklace.Dyadic :=
#[
  ⟨-6810693, 11⟩,
  ⟨-5235925, 15⟩,
  ⟨-8226015, 18⟩,
  ⟨-5622107, 19⟩,
  ⟨-10023251, 21⟩,
  ⟨-10253177, 22⟩,
  ⟨-11223233, 23⟩,
  ⟨-12539835, 24⟩,
  ⟨-1715779, 22⟩,
  ⟨-7020551, 25⟩,
  ⟨-3129109, 25⟩,
  ⟨-8554415, 28⟩,
  ⟨-6719801, 30⟩,
  ⟨-5166049, 34⟩
]

private theorem checked16 (k : Fin (9 - 2)) :
    descentMesh 16 (k.val + 3) nodes16 = true := by
  fin_cases k <;> decide +kernel

/-- A common negative quotient grid at size 17. -/
private def nodes17 : Array Necklace.Dyadic :=
#[
  ⟨-11479505, 11⟩,
  ⟨-3780847, 14⟩,
  ⟨-11080015, 18⟩,
  ⟨-7318425, 19⟩,
  ⟨-12863317, 21⟩,
  ⟨-13159891, 22⟩,
  ⟨-14597089, 23⟩,
  ⟨-1, 0⟩,
  ⟨-2410369, 22⟩,
  ⟨-10694427, 25⟩,
  ⟨-10940995, 26⟩,
  ⟨-4807643, 26⟩,
  ⟨-6350961, 28⟩,
  ⟨-4652975, 30⟩,
  ⟨-12259891, 36⟩
]

private theorem checked17 (k : Fin (9 - 2)) :
    descentMesh 17 (k.val + 3) nodes17 = true := by
  fin_cases k <;> decide +kernel

/-- Every nonexceptional size through seventeen has one checked grid for its cutoff rows. -/
theorem exists_descentMesh {n : ℕ} (hn : 3 ≤ n) (hi : n ≤ 17) (five : n ≠ 5) :
    ∃ nodes : Array Necklace.Dyadic, nodes.size = n - 2 ∧
      ∀ k : Fin (lastRepresentative n - 2), descentMesh n (k.val + 3) nodes = true := by
  interval_cases n
  · exact ⟨nodes3, by decide, checked3⟩
  · exact ⟨nodes4, by decide, checked4⟩
  · exact (five rfl).elim
  · exact ⟨nodes6, by decide, checked6⟩
  · exact ⟨nodes7, by decide, checked7⟩
  · exact ⟨nodes8, by decide, checked8⟩
  · exact ⟨nodes9, by decide, checked9⟩
  · exact ⟨nodes10, by decide, checked10⟩
  · exact ⟨nodes11, by decide, checked11⟩
  · exact ⟨nodes12, by decide, checked12⟩
  · exact ⟨nodes13, by decide, checked13⟩
  · exact ⟨nodes14, by decide, checked14⟩
  · exact ⟨nodes15, by decide, checked15⟩
  · exact ⟨nodes16, by decide, checked16⟩
  · exact ⟨nodes17, by decide, checked17⟩

end RealRooted.LongCycleDescents.Finite

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
