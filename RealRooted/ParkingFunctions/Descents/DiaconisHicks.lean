import RealRooted.ParkingFunctions.Descents.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cyclic value action for parking-function descents

This low finite-action layer records the cyclic value shifts used in the
Diaconis--Hicks comparison between parking functions and words on an alphabet
of size one larger.  It proves only the orbit facts; sorting values along
chains and selecting the unique parking representative are later work.
-/

namespace RealRooted.ParkingFunctions

/-- Cyclically shift every value of a word on `Fin (n + 1)`. -/
def cyclicValueShiftEquiv (n : ℕ) (c : Fin (n + 1)) :
    (Fin n → Fin (n + 1)) ≃ (Fin n → Fin (n + 1)) :=
  Equiv.piCongrRight fun _ => finCycle c

/-- The word obtained by cyclically shifting all values by `c`. -/
def cyclicValueShift {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) : Fin n → Fin (n + 1) :=
  cyclicValueShiftEquiv n c w

@[simp]
theorem cyclicValueShift_apply {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) (i : Fin n) :
    cyclicValueShift c w i = finCycle c (w i) := rfl

/-- Every fixed cyclic value shift is a bijection on words. -/
theorem cyclicValueShift_bijective {n : ℕ} (c : Fin (n + 1)) :
    Function.Bijective (cyclicValueShift c :
      (Fin n → Fin (n + 1)) → Fin n → Fin (n + 1)) :=
  (cyclicValueShiftEquiv n c).bijective

/-- Cyclic value shifts preserve equality relations between positions. -/
theorem cyclicValueShift_eq_iff {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) (i j : Fin n) :
    cyclicValueShift c w i = cyclicValueShift c w j ↔ w i = w j := by
  change finCycle c (w i) = finCycle c (w j) ↔ w i = w j
  exact (finCycle c).injective.eq_iff

/-- For a nonempty word, distinct cyclic shifts produce distinct words. -/
theorem cyclicValueShift_injective_in_shift {n : ℕ} (hn : 0 < n)
    (w : Fin n → Fin (n + 1)) :
    Function.Injective (fun c : Fin (n + 1) => cyclicValueShift c w) := by
  intro c d h
  have hzero := congrFun h ⟨0, hn⟩
  change w ⟨0, hn⟩ + c = w ⟨0, hn⟩ + d at hzero
  exact add_left_cancel hzero

/-- The cyclic value orbit of a nonempty word has the full alphabet size. -/
theorem card_cyclicValueShift_orbit {n : ℕ} (hn : 0 < n)
    (w : Fin n → Fin (n + 1)) :
    (Finset.univ.image fun c => cyclicValueShift c w).card = n + 1 := by
  rw [Finset.card_image_of_injective _ (cyclicValueShift_injective_in_shift hn w)]
  simp

end RealRooted.ParkingFunctions
