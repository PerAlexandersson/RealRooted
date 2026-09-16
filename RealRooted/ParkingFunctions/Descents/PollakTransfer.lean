import RealRooted.Mathlib.Algebra.BigOperators.Finset.Unique
import RealRooted.ParkingFunctions.Descents.Pollak
import RealRooted.ParkingFunctions.Descents.WordContent

/-!
# Weighted Pollak orbit transfer

This module specializes weighted unique-index double counting to Pollak's
cyclic action on words over an alphabet with one extra letter.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The parking part of a finite family of words on the extra alphabet. -/
def parkingPart {n : ℕ}
    (words : Finset (Fin n → Fin (n + 1))) :
    Finset (Fin n → Fin (n + 1)) := by
  classical
  exact words.filter IsParkingWord

@[simp]
theorem mem_parkingPart_iff {n : ℕ}
    {words : Finset (Fin n → Fin (n + 1))}
    {w : Fin n → Fin (n + 1)} :
    w ∈ parkingPart words ↔ w ∈ words ∧ IsParkingWord w := by
  simp [parkingPart]

/-- All parking words on the alphabet with one extra letter. -/
def parkingWords (n : ℕ) : Finset (Fin n → Fin (n + 1)) :=
  parkingPart Finset.univ

@[simp]
theorem mem_parkingWords_iff {n : ℕ} {w : Fin n → Fin (n + 1)} :
    w ∈ parkingWords n ↔ IsParkingWord w := by
  simp [parkingWords]

/-- Cyclic value shift is the corresponding alphabet relabeling. -/
theorem cyclicValueShift_eq_relabelWord {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) :
    cyclicValueShift c w = relabelWord (finCycle c) w := rfl

/-- Members of a finite word family whose shift by `c` is parking. -/
def cyclicParkingPreimage {n : ℕ}
    (words : Finset (Fin n → Fin (n + 1))) (c : Fin (n + 1)) :
    Finset (Fin n → Fin (n + 1)) := by
  classical
  exact words.filter fun w => IsParkingWord (cyclicValueShift c w)

/-- Weighted Pollak double counting. A supplied calculation of every shifted
parking fiber turns Pollak's unique successful shift into the exact factor
`n + 1`. -/
theorem sum_eq_succ_nsmul_of_cyclicValueShift_filter_sum
    {M : Type*} [AddCommMonoid M] {n : ℕ}
    (words : Finset (Fin n → Fin (n + 1)))
    (weight : (Fin n → Fin (n + 1)) → M) (fiberSum : M)
    (hfiber : ∀ c : Fin (n + 1),
      ∑ w ∈ cyclicParkingPreimage words c, weight w = fiberSum) :
    ∑ w ∈ words, weight w = (n + 1) • fiberSum := by
  classical
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.sum_eq_card_nsmul_of_existsUnique_mem_and_filter_sum
      words (Finset.univ : Finset (Fin (n + 1)))
      (fun c w => IsParkingWord (cyclicValueShift c w)) weight fiberSum
      (by
        intro w _
        simpa using existsUnique_isParkingWord_cyclicValueShift w)
      (by
        intro c _
        exact hfiber c)

end

end RealRooted.ParkingFunctions
