import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Polynomial

/-!
# Parking-function descents

This low combinatorial core uses zero-based words `Fin n → Fin n`.  It records
the parking condition by its standard prefix-count criterion and defines the
descent statistic needed for the Diaconis--Hicks transfer.  The transfer and
its real-rootedness consequences are deliberately separate work.
-/

namespace RealRooted.ParkingFunctions

/-- A zero-based word is a parking function when, for every prefix of the
alphabet, at least that many entries lie in the prefix. -/
def IsParkingFunction {n : ℕ} (w : Fin n → Fin n) : Prop :=
  ∀ k : ℕ, k ≤ n →
    k ≤ (Finset.univ.filter fun i => (w i).val < k).card

/-- The all-zero word, defined uniformly even at length zero. -/
def zeroParkingWord (n : ℕ) : Fin n → Fin n := fun i =>
  ⟨0, Nat.zero_lt_of_lt i.isLt⟩

/-- The all-zero word is a parking function. -/
theorem zeroParkingWord_isParkingFunction (n : ℕ) :
    IsParkingFunction (zeroParkingWord n) := by
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

/-- The finite set of zero-based parking-function words of length `n`. -/
noncomputable def parkingFunctions (n : ℕ) : Finset (Fin n → Fin n) := by
  classical
  exact Finset.univ.filter IsParkingFunction

@[simp]
theorem mem_parkingFunctions_iff {n : ℕ} {w : Fin n → Fin n} :
    w ∈ parkingFunctions n ↔ IsParkingFunction w := by
  simp [parkingFunctions]

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

/-- Number of descents of a finite word. -/
def descentNumber {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin (n + 1) → α) : ℕ :=
  (descentSet w).card

/-- Appending a final letter increments the descent number precisely when it
is smaller than the old final letter. -/
theorem descentNumber_snoc {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin (n + 1) → α) (x : α) :
    descentNumber (Fin.snoc w x) =
      descentNumber w + if x < w (Fin.last n) then 1 else 0 := by
  unfold descentNumber
  rw [descentSet_snoc]
  by_cases h : x < w (Fin.last n)
  · rw [if_pos h]
    have hdisjoint : Disjoint ((descentSet w).map Fin.castSuccEmb) {Fin.last n} := by
      rw [Finset.disjoint_singleton_right]
      simp
    rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_map,
      Finset.card_singleton]
    simp [h]
  · rw [if_neg h]
    simp [h]

/-- Appending a letter multiplies the descent monomial by `X` precisely when
it creates the new final descent. -/
theorem descentWeight_snoc {R : Type*} [Semiring R] {n : ℕ}
    (w : Fin (n + 1) → Fin m) (x : Fin m) :
    (X : R[X]) ^ descentNumber (Fin.snoc w x) =
      (if x < w (Fin.last n) then X else 1) * X ^ descentNumber w := by
  rw [descentNumber_snoc]
  by_cases h : x < w (Fin.last n)
  · simp only [if_pos h, pow_succ]
    rw [Polynomial.X_mul]
  · simp [h]

theorem descentNumber_le {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin (n + 1) → α) :
    descentNumber w ≤ n := by
  change (descentSet w).card ≤ n
  simpa using Finset.card_le_card (Finset.subset_univ (descentSet w))

/-- The descent generating polynomial of a finite family of words. -/
noncomputable def descentGeneratingPolynomial {R : Type*} [Semiring R] {n : ℕ} {α : Type*}
    [LT α] [DecidableRel (fun a b : α => a < b)]
    (words : Finset (Fin (n + 1) → α)) : R[X] :=
  ∑ w ∈ words, X ^ descentNumber w

/-- The descent generating polynomial of zero-based parking functions. -/
noncomputable def parkingDescentPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => descentGeneratingPolynomial (R := ℝ) (parkingFunctions (n + 1))

end RealRooted.ParkingFunctions
