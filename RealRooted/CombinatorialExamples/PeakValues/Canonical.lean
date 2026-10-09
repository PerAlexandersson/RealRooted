import RealRooted.Mathlib.Combinatorics.Enumerative.Peak
import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
import RealRooted.CombinatorialExamples.PeakValues

/-!
# Peak positions and the canonical peak set

The interior peak positions of `RealRooted.CombinatorialExamples.PeakValues` are the canonical
`Equiv.Perm.peakSet` (after `Fin.val`), and the number of peak values is the canonical peak
count.
-/

namespace RealRooted

private theorem isPeakPosition_iff_mem_peakSet {n : ℕ}
    (π : Equiv.Perm (Fin n)) (j : Fin n) :
    IsPeakPosition π j ↔ j.val ∈ (List.ofFn π).peakSet := by
  rw [List.mem_peakSet]
  constructor
  · rintro ⟨i, k, hij, hjk, hleft, hright⟩
    refine ⟨?_, ?_, ?_⟩
    · lia
    · have hklt : k.val < n := k.isLt
      simpa only [List.length_ofFn] using (show j.val + 1 < n by lia)
    · constructor
      · rw [List.getElem_ofFn, List.getElem_ofFn]
        have hi_eq : i = ⟨j.val - 1, by lia⟩ := Fin.ext (by lia)
        rw [hi_eq] at hleft
        simpa using hleft
      · rw [List.getElem_ofFn, List.getElem_ofFn]
        have hk_eq : k = ⟨j.val + 1, by lia⟩ := Fin.ext (by lia)
        rw [hk_eq] at hright
        simpa using hright
  · rintro ⟨hi, h, hleft, hright⟩
    have hjlt : j.val < n := j.isLt
    have hbound : j.val + 1 < n := by
      simpa only [List.length_ofFn] using h
    let i : Fin n := ⟨j.val - 1, by lia⟩
    let k : Fin n := ⟨j.val + 1, by lia⟩
    refine ⟨i, k, ?_, ?_, ?_, ?_⟩
    · dsimp [i]
      lia
    · dsimp [k]
    · rw [List.getElem_ofFn, List.getElem_ofFn] at hleft
      simpa using hleft
    · rw [List.getElem_ofFn, List.getElem_ofFn] at hright
      simpa using hright

/-- Local peak positions map to the canonical permutation peak set. -/
theorem peakPositions_map_valEmbedding_eq_peakSet {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    (peakPositions π).map Fin.valEmbedding = π.peakSet := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_map.mp hi
    subst i
    exact (isPeakPosition_iff_mem_peakSet π j).mp
      (mem_peakPositions_iff.mp hj)
  · intro hi
    let j : Fin n := ⟨i, by
      have h := List.mem_peakSet.mp hi
      have hbound : i + 1 < n := by
        simpa only [List.length_ofFn] using h.2.1
      lia⟩
    refine Finset.mem_map.mpr ⟨j, ?_, rfl⟩
    exact mem_peakPositions_iff.mpr
      ((isPeakPosition_iff_mem_peakSet π j).mpr hi)

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
