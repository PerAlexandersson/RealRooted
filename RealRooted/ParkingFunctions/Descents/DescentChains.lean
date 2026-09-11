import RealRooted.ParkingFunctions.Descents.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.SplitBy

/-!
# Chains associated to a descent subset

This module partitions the ordered positions of a word into contiguous runs
whose adjacent edges are prescribed descents.  Reversing those runs produces
the strict increasing chains used in the parking-word transfer.
-/

namespace RealRooted.ParkingFunctions

/-- The ordered adjacent edge from `i` to `j` is selected by `S`. -/
def isDescentStep {n : ℕ} (S : Finset (Fin n))
    (i j : Fin (n + 1)) : Bool :=
  decide (∃ k : Fin n, k ∈ S ∧ i = k.castSucc ∧ j = k.succ)

/-- Contiguous increasing runs connected by the descent edges in `S`. -/
def descentRuns {n : ℕ} (S : Finset (Fin n)) : List (List (Fin (n + 1))) :=
  (List.ofFn id).splitBy (isDescentStep S)

/-- The runs partition the positions in their original order. -/
theorem flatten_descentRuns {n : ℕ} (S : Finset (Fin n)) :
    (descentRuns S).flatten = List.ofFn id :=
  List.flatten_splitBy _ _

/-- No contiguous descent run is empty. -/
theorem nil_not_mem_descentRuns {n : ℕ} (S : Finset (Fin n)) :
    [] ∉ descentRuns S :=
  List.nil_notMem_splitBy _ _

/-- Consecutive positions inside a descent run are selected descent edges. -/
theorem isChain_of_mem_descentRuns {n : ℕ} (S : Finset (Fin n))
    {l : List (Fin (n + 1))} (hl : l ∈ descentRuns S) :
    l.IsChain fun i j => isDescentStep S i j :=
  List.isChain_of_mem_splitBy hl

/-- Reverse each increasing run so strict increase along a chain represents a
strict descent along the original word positions. -/
def descentChains {n : ℕ} (S : Finset (Fin n)) : List (List (Fin (n + 1))) :=
  (descentRuns S).map List.reverse

end RealRooted.ParkingFunctions
