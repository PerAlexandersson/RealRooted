import RealRooted.Mathlib.Combinatorics.Enumerative.Descent
import RealRooted.Mathlib.Combinatorics.Enumerative.Peak
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

private theorem descentSet_eq_map_valEmbedding_aux {n : ℕ} {α : Type*}
    [LinearOrder α] (w : Fin (n + 1) → α) :
    (descentSet w).map Fin.valEmbedding = (List.ofFn w).descentSet := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    have hdesc : w j.succ < w j.castSucc := mem_descentSet_iff w j |>.1 hj
    rw [List.mem_descentSet]
    refine ⟨?_, ?_⟩
    · simpa only [List.length_ofFn] using
        (show Fin.valEmbedding j + 1 < n + 1 by
          change j.val + 1 < n + 1
          lia)
    · have hsucc : j.succ = ⟨Fin.valEmbedding j + 1, by
          change j.val + 1 < n + 1
          lia⟩ := by
        apply Fin.ext
        rfl
      have hcast : j.castSucc = ⟨Fin.valEmbedding j, by
          change j.val < n + 1
          lia⟩ := by
        apply Fin.ext
        rfl
      simpa only [List.getElem_ofFn, hsucc, hcast] using hdesc
  · intro hi
    rw [List.mem_descentSet] at hi
    obtain ⟨hbound, hdesc⟩ := hi
    have hbound' : i + 1 < n + 1 := by
      simpa only [List.length_ofFn] using hbound
    let j : Fin n := ⟨i, by lia⟩
    refine Finset.mem_map.2 ⟨j, ?_, rfl⟩
    apply mem_descentSet_iff w j |>.2
    have hdesc' : w ⟨i + 1, by lia⟩ < w ⟨i, by lia⟩ := by
      simpa only [List.getElem_ofFn] using hdesc
    have hsucc : j.succ = ⟨i + 1, by lia⟩ := by
      apply Fin.ext
      rfl
    have hcast : j.castSucc = ⟨i, by lia⟩ := by
      apply Fin.ext
      rfl
    simpa only [hsucc, hcast] using hdesc'

/-- The natural-number image of the local descent set is the canonical list
descent set. -/
theorem descentSet_map_valEmbedding_eq_list {n : ℕ} {α : Type*}
    [LinearOrder α] (w : Fin (n + 1) → α) :
    (descentSet w).map Fin.valEmbedding = (List.ofFn w).descentSet := by
  exact descentSet_eq_map_valEmbedding_aux w

/-- Cardinalities are unchanged by the position conversion. -/
theorem descentNumber_eq_list_descentCount {n : ℕ} {α : Type*}
    [LinearOrder α] (w : Fin (n + 1) → α) :
    descentNumber w = (List.ofFn w).descentCount := by
  rw [descentNumber, List.descentCount]
  rw [← descentSet_map_valEmbedding_eq_list w, Finset.card_map]

/-- The same position conversion handles the local empty-word convention. -/
theorem wordDescentSet_map_valEmbedding_eq_list {n : ℕ} {α : Type*}
    [LinearOrder α] (w : Fin n → α) :
    (wordDescentSet w).map Fin.valEmbedding = (List.ofFn w).descentSet := by
  cases n with
  | zero => simp [wordDescentSet, List.descentSet_nil]
  | succ n =>
      simpa only [wordDescentSet] using descentSet_map_valEmbedding_eq_list w

/-- The zero-based local word statistic agrees with the canonical list count. -/
theorem wordDescentNumber_eq_list_descentCount {n : ℕ} {α : Type*}
    [LinearOrder α] (w : Fin n → α) :
    wordDescentNumber w = (List.ofFn w).descentCount := by
  cases n with
  | zero => simp [wordDescentNumber, List.descentCount]
  | succ n =>
      simpa only [wordDescentNumber, List.descentCount] using
        descentNumber_eq_list_descentCount w

/- The weak left-peak statistic is not the canonical strict `leftPeakSet`:
   it omits position zero and allows equality at the preceding edge. -/
end RealRooted.ParkingFunctions
