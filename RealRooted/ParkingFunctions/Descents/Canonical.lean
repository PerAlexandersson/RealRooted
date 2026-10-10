import RealRooted.Mathlib.Combinatorics.Enumerative.Descent
import RealRooted.Mathlib.Combinatorics.Enumerative.Peak
import RealRooted.Mathlib.Combinatorics.Enumerative.ParkingFunction
import RealRooted.ParkingFunctions.Descents.Basic
import RealRooted.ParkingFunctions.Descents.WeakLeftPeak

/-!
# Bridges for parking-function word statistics

The parking-function API indexes adjacent positions by `Fin`, whereas the
canonical list API uses natural-number positions.  The theorems below record
the conversion through `Fin.valEmbedding`.
-/

namespace RealRooted.ParkingFunctions

/- The local definitions have only `[LT α]`; the canonical list definitions
   require `[LinearOrder α]`. -/

/-- The natural-number image of the local descent set is the canonical list
descent set. -/
theorem descentSet_map_valEmbedding_eq_list {n : ℕ} {α : Type*}
    [LinearOrder α] (w : Fin (n + 1) → α) :
    (descentSet w).map Fin.valEmbedding = (List.ofFn w).descentSet := by
  exact (List.descentSet_ofFn w).symm

/-- The same position conversion handles the local empty-word convention. -/
theorem wordDescentSet_map_valEmbedding_eq_list {n : ℕ} {α : Type*}
    [LinearOrder α] (w : Fin n → α) :
    (wordDescentSet w).map Fin.valEmbedding = (List.ofFn w).descentSet := by
  cases n with
  | zero => simp [wordDescentSet, List.descentSet_nil]
  | succ n =>
      simpa only [wordDescentSet] using descentSet_map_valEmbedding_eq_list w

/- The weak left-peak statistic is not the canonical strict `leftPeakSet`:
   it omits position zero and allows equality at the preceding edge. -/
end RealRooted.ParkingFunctions
