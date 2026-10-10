import RealRooted.Mathlib.Combinatorics.Enumerative.Peak
import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
import RealRooted.CombinatorialExamples.PeakValues

/-!
# Peak positions and the canonical peak set

The interior peak positions of `RealRooted.CombinatorialExamples.PeakValues` are the canonical
`Equiv.Perm.peakSet` read in `Fin n`; here the two are compared as finsets, and the number of
peak positions is the canonical peak count.
-/

namespace RealRooted

/-- Local peak positions map to the canonical permutation peak set. -/
theorem peakPositions_map_valEmbedding_eq_peakSet {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    (peakPositions π).map Fin.valEmbedding = π.peakSet := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_map.mp hi
    subst i
    exact mem_peakPositions_iff.mp hj
  · intro hi
    let j : Fin n := ⟨i, by
      have h := List.mem_peakSet.mp hi
      have hbound : i + 1 < n := by
        simpa only [List.length_ofFn] using h.2.1
      lia⟩
    refine Finset.mem_map.mpr ⟨j, ?_, rfl⟩
    exact mem_peakPositions_iff.mpr hi

/-- Local and canonical peak-position counts agree. -/
theorem peakPositions_card_eq_peakCount {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (peakPositions π).card = π.peakCount := by
  change (peakPositions π).card = π.peakSet.card
  rw [← Finset.card_map]
  rw [peakPositions_map_valEmbedding_eq_peakSet]

/-- The local peak-value set is the image of local peak positions under `π`. -/
theorem peakValues_eq_image_peakPositions {n : ℕ} (π : Equiv.Perm (Fin n)) :
    peakValues π = (peakPositions π).image π :=
  rfl

/-- The local peak-value count agrees with the canonical peak count. -/
theorem peakValues_card_eq_peakCount {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (peakValues π).card = π.peakCount := by
  rw [peakValues, Finset.card_image_of_injective]
  · exact peakPositions_card_eq_peakCount π
  · exact π.injective

end RealRooted
