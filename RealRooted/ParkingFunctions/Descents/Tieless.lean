import RealRooted.BrandenVecchi.SmirnovChow
import RealRooted.ParkingFunctions.Descents.Pollak

/-!
# Tieless parking-function descents

This file defines the literal finite family of parking functions with no equal
adjacent entries.  Alphabet embedding identifies its tie condition with the
existing finite Smirnov-word predicate.  Content fibers and cyclic-orbit
counts belong to later layers.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

/-- A parking-function word has no tie when consecutive entries are distinct.
The empty word satisfies the condition. -/
def HasNoAdjacentTies {n : ℕ} (w : Fin n → Fin n) : Prop :=
  match n with
  | 0 => True
  | k + 1 => ∀ i : Fin k, w i.castSucc ≠ w i.succ

/-- A tieless parking function is a parking function with no equal adjacent
entries. -/
def IsTielessParkingFunction {n : ℕ} (w : Fin n → Fin n) : Prop :=
  IsParkingFunction w ∧ HasNoAdjacentTies w

/-- Alphabet embedding turns the no-tie condition into the existing Smirnov
condition. -/
theorem isSmirnovWord_parkingWordEmbed_iff {n : ℕ} (w : Fin n → Fin n) :
    BrandenVecchi.IsSmirnovWord n (parkingWordEmbed w) ↔
      HasNoAdjacentTies w := by
  cases n with
  | zero => simp [BrandenVecchi.IsSmirnovWord, HasNoAdjacentTies]
  | succ n =>
      simp only [BrandenVecchi.IsSmirnovWord, HasNoAdjacentTies]
      constructor
      · intro h i hi
        apply h i
        simpa only [parkingWordEmbed_apply] using congrArg Fin.castSucc hi
      · intro h i hi
        exact h i (Fin.castSucc_inj.mp hi)

/-- The literal finite family of tieless parking functions of length `n`. -/
def tielessParkingFunctions (n : ℕ) : Finset (Fin n → Fin n) := by
  classical
  exact Finset.univ.filter IsTielessParkingFunction

@[simp]
theorem mem_tielessParkingFunctions_iff {n : ℕ} {w : Fin n → Fin n} :
    w ∈ tielessParkingFunctions n ↔ IsTielessParkingFunction w := by
  simp [tielessParkingFunctions]

/-- Membership in the tieless family supplies both the embedded parking-word
and Smirnov-word conditions. -/
theorem parkingWordEmbed_conditions_of_mem {n : ℕ} {w : Fin n → Fin n}
    (hw : w ∈ tielessParkingFunctions n) :
    IsParkingWord (parkingWordEmbed w) ∧
      parkingWordEmbed w ∈ BrandenVecchi.smirnovWords (n + 1) n := by
  rw [mem_tielessParkingFunctions_iff] at hw
  exact ⟨(isParkingWord_parkingWordEmbed_iff w).2 hw.1,
    BrandenVecchi.mem_smirnovWords_iff.2
      ((isSmirnovWord_parkingWordEmbed_iff w).2 hw.2)⟩

/-- Tieless parking membership is exactly the conjunction of the two embedded
finite-word conditions. -/
theorem mem_tielessParkingFunctions_iff_embed {n : ℕ}
    {w : Fin n → Fin n} :
    w ∈ tielessParkingFunctions n ↔
      IsParkingWord (parkingWordEmbed w) ∧
        parkingWordEmbed w ∈ BrandenVecchi.smirnovWords (n + 1) n := by
  constructor
  · exact parkingWordEmbed_conditions_of_mem
  · rintro ⟨hparking, hsmirnov⟩
    rw [mem_tielessParkingFunctions_iff]
    exact ⟨(isParkingWord_parkingWordEmbed_iff w).1 hparking,
      (isSmirnovWord_parkingWordEmbed_iff w).1
        (BrandenVecchi.mem_smirnovWords_iff.1 hsmirnov)⟩

/-- The embedding preserves the descent monomial of a nonempty word. -/
theorem descentMonomial_parkingWordEmbed {R : Type*} [Semiring R]
    {n : ℕ} (w : Fin (n + 1) → Fin (n + 1)) :
    (X : R[X]) ^ BrandenVecchi.smirnovDescentNumber (parkingWordEmbed w) =
      X ^ descentNumber w := by
  simp only [BrandenVecchi.smirnovDescentNumber,
    descentNumber_parkingWordEmbed]

/-- The integral descent enumerator of tieless parking functions. -/
def tielessParkingDescentPolynomial : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => descentGeneratingPolynomial (R := ℤ)
      (tielessParkingFunctions (n + 1))

@[simp]
theorem tielessParkingDescentPolynomial_zero :
    tielessParkingDescentPolynomial 0 = 1 := rfl

@[simp]
theorem tielessParkingDescentPolynomial_one :
    tielessParkingDescentPolynomial 1 = 1 := by
  have hfamily :
      tielessParkingFunctions 1 = {(fun _ : Fin 1 => (0 : Fin 1))} := by
    ext w
    simp only [mem_tielessParkingFunctions_iff, Finset.mem_singleton]
    constructor
    · intro _
      funext i
      exact Subsingleton.elim _ _
    · intro hw
      subst w
      exact ⟨zeroParkingWord_isParkingFunction 1, by
        intro i
        exact Fin.elim0 i⟩
  rw [tielessParkingDescentPolynomial, hfamily]
  simp [descentGeneratingPolynomial, descentNumber, descentSet]

end

end RealRooted.ParkingFunctions
