import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.FinRange
import RealRooted.Mathlib.Combinatorics.Enumerative.Descent

/-!
# Parking functions

We use zero-based words `w : Fin n → Fin n`.  The parking condition is written
in its prefix-count form, which is definitionally the condition used by the
existing parking-function descent modules.
-/

namespace ParkingFunction

variable {n : ℕ}

/-- A zero-based word is a parking function when every prefix of the alphabet
contains at least as many entries as its size. -/
def IsParkingFunction (w : Fin n → Fin n) : Prop :=
  ∀ k : Fin (n + 1),
    k.val ≤ (Finset.univ.filter fun i => (w i).val < k.val).card

/-- The parking-function predicate is decidable by finite enumeration. -/
instance decidableIsParkingFunction (w : Fin n → Fin n) :
    Decidable (IsParkingFunction w) := by
  unfold IsParkingFunction
  infer_instance

/-- The finite-indexed predicate is equivalent to the usual bounded-natural
formulation used by the existing parking-function modules. -/
theorem isParkingFunction_iff_prefix {w : Fin n → Fin n} :
    IsParkingFunction w ↔
      ∀ k : ℕ, k ≤ n → k ≤ (Finset.univ.filter fun i => (w i).val < k).card := by
  constructor
  · intro h k hk
    exact h ⟨k, Nat.lt_succ_of_le hk⟩
  · intro h k
    exact h k.val (by lia)

/-- The finite set of zero-based parking functions of length `n`. -/
def parkingFunctions (n : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter IsParkingFunction

/-- Membership in `parkingFunctions` is the parking-function predicate. -/
@[simp] theorem mem_parkingFunctions_iff {w : Fin n → Fin n} :
    w ∈ parkingFunctions n ↔ IsParkingFunction w := by
  simp [parkingFunctions]

/-- The descent set of a parking function, read as a natural-indexed word. -/
def descentSet (w : Fin n → Fin n) : Finset ℕ :=
  (List.ofFn w).descentSet

/-- The descent count of a parking function. -/
def descentCount (w : Fin n → Fin n) : ℕ :=
  (descentSet w).card

/-- The staging descent set is the canonical descent set of `List.ofFn w`. -/
@[simp] theorem descentSet_eq_list (w : Fin n → Fin n) :
    descentSet w = (List.ofFn w).descentSet := rfl

/-- The staging descent count is the canonical descent count of `List.ofFn w`. -/
@[simp] theorem descentCount_eq_list (w : Fin n → Fin n) :
    descentCount w = (List.ofFn w).descentCount := by
  rfl

example : (parkingFunctions 0).card = 1 := by decide

example : (parkingFunctions 1).card = 1 := by decide

example : (parkingFunctions 2).card = 3 := by decide

example : (parkingFunctions 3).card = 16 := by decide

end ParkingFunction
