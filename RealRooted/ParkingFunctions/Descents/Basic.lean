import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.Combinatorics.Enumerative.GenPoly
import RealRooted.Mathlib.Combinatorics.Enumerative.ParkingFunction

open Polynomial

/-!
# Parking-function descents

This low combinatorial core uses zero-based words `Fin n → Fin n`.  It records
the parking condition by its standard prefix-count criterion and defines the
descent statistic needed for the Diaconis--Hicks transfer.  The transfer and
its real-rootedness consequences are deliberately separate work.
-/

namespace RealRooted.ParkingFunctions

open ParkingFunction (IsParkingFunction parkingFunctions mem_parkingFunctions_iff
  isParkingFunction_iff_prefix)

/-- The all-zero word, defined uniformly even at length zero. -/
def zeroParkingWord (n : ℕ) : Fin n → Fin n := fun i =>
  ⟨0, Nat.zero_lt_of_lt i.isLt⟩

/-- The all-zero word is a parking function. -/
theorem zeroParkingWord_isParkingFunction (n : ℕ) :
    IsParkingFunction (zeroParkingWord n) := by
  rw [isParkingFunction_iff_prefix]
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hfilter :
        (Finset.univ.filter fun i : Fin n => (zeroParkingWord n i).val < k) =
          Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      simpa [zeroParkingWord] using hkpos
    rw [hfilter, Finset.card_univ]
    simpa using hk

theorem zeroParkingWord_mem_parkingFunctions (n : ℕ) :
    zeroParkingWord n ∈ parkingFunctions n :=
  mem_parkingFunctions_iff.mpr (zeroParkingWord_isParkingFunction n)

theorem parkingFunctions_nonempty (n : ℕ) : (parkingFunctions n).Nonempty :=
  ⟨zeroParkingWord n, zeroParkingWord_mem_parkingFunctions n⟩

/-- The descent set of a word of length `n + 1`, indexed by its adjacent
positions. -/
def descentSet {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin (n + 1) → α) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i.succ < w i.castSucc

@[simp]
theorem mem_descentSet_iff {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin (n + 1) → α) (i : Fin n) :
    i ∈ descentSet w ↔ w i.succ < w i.castSucc := by
  simp [descentSet]

/-- The condition that every adjacent position in `S` is a descent of a word. -/
def HasDescentsAt {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (S : Finset (Fin n))
    (w : Fin (n + 1) → α) : Prop :=
  S ⊆ descentSet w

/-- A descent-subset condition is exactly the corresponding family of strict
adjacent inequalities. -/
theorem hasDescentsAt_iff {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (S : Finset (Fin n))
    (w : Fin (n + 1) → α) :
    HasDescentsAt S w ↔ ∀ i ∈ S, w i.succ < w i.castSucc := by
  simp only [HasDescentsAt, Finset.subset_iff, mem_descentSet_iff]

/-- Requiring descents at more positions implies every weaker descent-subset
condition. -/
theorem HasDescentsAt.mono {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] {S T : Finset (Fin n)}
    {w : Fin (n + 1) → α} (hST : S ⊆ T) (hT : HasDescentsAt T w) :
    HasDescentsAt S w :=
  hST.trans hT

/-- Appending a final letter preserves every earlier descent. -/
theorem mem_descentSet_snoc_castSucc_iff {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin (n + 1) → α) (x : α)
    (i : Fin n) :
    i.castSucc ∈ descentSet (Fin.snoc w x) ↔ i ∈ descentSet w := by
  simp only [mem_descentSet_iff]
  simp only [Fin.succ_castSucc, Fin.snoc_castSucc]

/-- The new final position after appending a letter is a descent exactly when
the appended letter is smaller than the old final letter. -/
theorem mem_descentSet_snoc_last_iff {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin (n + 1) → α) (x : α) :
    Fin.last n ∈ descentSet (Fin.snoc w x) ↔ x < w (Fin.last n) := by
  simp only [mem_descentSet_iff]
  simp

/-- The descent set after appending a final letter consists of the embedded
old descent set and, optionally, the new final position. -/
theorem descentSet_snoc {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin (n + 1) → α) (x : α) :
    descentSet (Fin.snoc w x) =
      (descentSet w).map Fin.castSuccEmb ∪
        if x < w (Fin.last n) then {Fin.last n} else ∅ := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [mem_descentSet_snoc_last_iff]
    by_cases h : x < w (Fin.last n)
    · simp [h]
    · simp [h]
  · simp only [mem_descentSet_snoc_castSucc_iff]
    by_cases h : x < w (Fin.last n)
    · simp [h]
    · simp [h]

/-- The descent set of a finite word, including the empty word. -/
def wordDescentSet {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] :
    {n : ℕ} → (Fin n → α) → Finset (Fin (n - 1))
  | 0, _ => ∅
  | _ + 1, word => descentSet word

@[simp]
theorem wordDescentSet_zero {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (word : Fin 0 → α) :
    wordDescentSet word = ∅ := rfl

@[simp]
theorem wordDescentSet_succ {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (word : Fin (n + 1) → α) :
    wordDescentSet word = descentSet word := rfl

/-- The Fin-indexed descent set has as many elements as the canonical descent set of the word
(`List.descentSet_ofFn`). -/
theorem card_descentSet {n : ℕ} {α : Type*} [LinearOrder α] (w : Fin (n + 1) → α) :
    (descentSet w).card = (List.ofFn w).descentCount := by
  rw [List.descentCount, List.descentSet_ofFn, Finset.card_map]
  rfl

/-- Appending a letter multiplies the descent monomial by `X` precisely when
it creates the new final descent. -/
theorem descentWeight_snoc {R : Type*} [Semiring R] {n : ℕ}
    (w : Fin (n + 1) → Fin m) (x : Fin m) :
    (X : R[X]) ^ (List.ofFn (Fin.snoc w x : Fin (n + 2) → Fin m)).descentCount =
      (if x < w (Fin.last n) then X else 1) * X ^ (List.ofFn w).descentCount := by
  rw [List.descentCount_ofFn_snoc]
  by_cases h : x < w (Fin.last n)
  · simp only [ite_eq_left h, pow_succ]
    rw [Polynomial.X_mul]
  · simp [h]

/-- The descent generating polynomial of zero-based parking functions. -/
noncomputable def parkingDescentPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (parkingFunctions (n + 1)).genPoly fun w => (List.ofFn w).descentCount

end RealRooted.ParkingFunctions
