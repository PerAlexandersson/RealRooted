import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram

/-!
# Further facts about conjugate partitions

This file supplies small connections between Mathlib's partition and Young
diagram APIs.
-/

namespace Nat.Partition

/-- Every part of the conjugate partition is at most the number of parts of
the original partition. -/
theorem le_card_parts_of_mem_conjugate_parts {N : ℕ} (mu : N.Partition)
    {k : ℕ} (hk : k ∈ mu.conjugate.parts) : k ≤ mu.parts.card := by
  let Y := YoungDiagram.ofPartition mu
  have hk' : k ∈ (Y.transpose.rowLens : Multiset ℕ) := by
    simpa only [conjugate, YoungDiagram.toPartition, Y] using hk
  rw [Multiset.mem_coe] at hk'
  rw [YoungDiagram.rowLens] at hk'
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk'
  rw [YoungDiagram.rowLen_transpose]
  calc
    Y.colLen i ≤ Y.colLen 0 := Y.colLen_anti 0 i (Nat.zero_le i)
    _ = Y.rowLens.length := YoungDiagram.length_rowLens.symm
    _ = (mu.parts.sort (· ≥ ·)).length := by
      rw [YoungDiagram.rowLens_ofPartition_eq_sort_parts]
    _ = mu.parts.card := by simp

end Nat.Partition
