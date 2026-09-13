import RealRooted.ParkingFunctions.Descents.CompositionBlocks
import RealRooted.ParkingFunctions.Descents.DescentChains

/-!
# Descent-containment content enumerators

This module packages the contiguous runs determined by prescribed descent
positions as a Mathlib `Composition`.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The composition of the word length formed by the lengths of its
contiguous prescribed-descent runs. -/
def descentRunComposition {n : ℕ} (S : Finset (Fin n)) :
    Composition (n + 1) where
  blocks := (descentRuns S).map List.length
  blocks_pos := by
    intro k hk
    rw [List.mem_map] at hk
    obtain ⟨run, hrun, rfl⟩ := hk
    apply Nat.pos_of_ne_zero
    intro hzero
    have hnil : run = [] := by simpa using hzero
    subst run
    exact nil_not_mem_descentRuns S hrun
  blocks_sum := by
    calc
      ((descentRuns S).map List.length).sum =
          (descentRuns S).flatten.length := by simp
      _ = (List.ofFn (id : Fin (n + 1) → Fin (n + 1))).length := by
        rw [flatten_descentRuns]
      _ = n + 1 := by simp

@[simp]
theorem descentRunComposition_blocks {n : ℕ} (S : Finset (Fin n)) :
    (descentRunComposition S).blocks =
      (descentRuns S).map List.length := rfl

end

end RealRooted.ParkingFunctions
