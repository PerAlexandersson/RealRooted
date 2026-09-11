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

/-- The finite set of zero-based parking-function words of length `n`. -/
noncomputable def parkingFunctions (n : ℕ) : Finset (Fin n → Fin n) := by
  classical
  exact Finset.univ.filter IsParkingFunction

@[simp]
theorem mem_parkingFunctions_iff {n : ℕ} {w : Fin n → Fin n} :
    w ∈ parkingFunctions n ↔ IsParkingFunction w := by
  simp [parkingFunctions]

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

/-- Number of descents of a finite word. -/
def descentNumber {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin (n + 1) → α) : ℕ :=
  (descentSet w).card

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
