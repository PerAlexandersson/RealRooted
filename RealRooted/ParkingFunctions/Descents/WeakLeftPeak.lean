import RealRooted.ParkingFunctions.Descents.ExactDescentTransfer

/-!
# Weak left peaks

Weak left peaks are encoded directly from descent sets, so the generic exact
descent-set Pollak transfer applies without another orbit argument.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The preceding position in the same nonempty finite index type. Its value
at zero is irrelevant for weak-left-peak membership. -/
def previousPosition {n : ℕ} (i : Fin n) : Fin n :=
  ⟨i.val - 1, by lia⟩

@[simp]
theorem previousPosition_val {n : ℕ} (i : Fin n) :
    (previousPosition i).val = i.val - 1 := rfl

/-- The weak left peaks encoded by a descent set: a positive descent position
whose preceding position is not a descent. -/
def weakLeftPeakSetFromDescentSet {n : ℕ}
    (D : Finset (Fin n)) : Finset (Fin n) :=
  D.filter fun i => 0 < i.val ∧ previousPosition i ∉ D

@[simp]
theorem mem_weakLeftPeakSetFromDescentSet_iff {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n) :
    i ∈ weakLeftPeakSetFromDescentSet D ↔
      i ∈ D ∧ 0 < i.val ∧ previousPosition i ∉ D := by
  simp [weakLeftPeakSetFromDescentSet]

/-- The number of weak left peaks encoded by a descent set. -/
def weakLeftPeakNumberFromDescentSet {n : ℕ}
    (D : Finset (Fin n)) : ℕ :=
  (weakLeftPeakSetFromDescentSet D).card

/-- Weak left peaks of a nonempty word. -/
def weakLeftPeakSet {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)]
    (w : Fin (n + 1) → α) : Finset (Fin n) :=
  weakLeftPeakSetFromDescentSet (descentSet w)

@[simp]
theorem mem_weakLeftPeakSet_iff {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)]
    (w : Fin (n + 1) → α) (i : Fin n) :
    i ∈ weakLeftPeakSet w ↔
      i ∈ descentSet w ∧
        0 < i.val ∧ previousPosition i ∉ descentSet w := by
  exact mem_weakLeftPeakSetFromDescentSet_iff (descentSet w) i

/-- The total weak-left-peak statistic on finite words. -/
def wordWeakLeftPeakNumber {n : ℕ} {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)]
    (w : Fin n → α) : ℕ :=
  weakLeftPeakNumberFromDescentSet (wordDescentSet w)

@[simp]
theorem wordWeakLeftPeakNumber_zero {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin 0 → α) :
    wordWeakLeftPeakNumber w = 0 := by
  simp [wordWeakLeftPeakNumber, weakLeftPeakNumberFromDescentSet,
    weakLeftPeakSetFromDescentSet]

@[simp]
theorem wordWeakLeftPeakNumber_one {α : Type*} [LT α]
    [DecidableRel (fun a b : α => a < b)] (w : Fin 1 → α) :
    wordWeakLeftPeakNumber w = 0 := by
  simp [wordWeakLeftPeakNumber, weakLeftPeakNumberFromDescentSet,
    weakLeftPeakSetFromDescentSet, descentSet]

/-- Integral weak-left-peak enumerator of all words on the extra alphabet. -/
def literalWordWeakLeftPeakPolynomialInt (n : ℕ) : ℤ[X] :=
  ∑ w : Fin n → Fin (n + 1), X ^ wordWeakLeftPeakNumber w

/-- Integral weak-left-peak enumerator of ordinary parking functions. -/
def parkingWeakLeftPeakPolynomialInt (n : ℕ) : ℤ[X] :=
  ∑ w ∈ parkingFunctions n, X ^ wordWeakLeftPeakNumber w

@[simp]
theorem literalWordWeakLeftPeakPolynomialInt_zero :
    literalWordWeakLeftPeakPolynomialInt 0 = 1 := by
  simp [literalWordWeakLeftPeakPolynomialInt]

@[simp]
theorem parkingWeakLeftPeakPolynomialInt_zero :
    parkingWeakLeftPeakPolynomialInt 0 = 1 := by
  simp [parkingWeakLeftPeakPolynomialInt, parkingFunctions,
    IsParkingFunction]

/-- Exact integral weak-left-peak transfer from ordinary parking functions to
all words. -/
theorem succ_nsmul_parkingWeakLeftPeakPolynomialInt_eq_literalWord
    (n : ℕ) :
    (n + 1) • parkingWeakLeftPeakPolynomialInt n =
      literalWordWeakLeftPeakPolynomialInt n := by
  unfold parkingWeakLeftPeakPolynomialInt
    literalWordWeakLeftPeakPolynomialInt wordWeakLeftPeakNumber
  exact (sum_wordDescentSetWeight_words_eq_succ_nsmul_parkingFunctions n
    (fun D => X ^ weakLeftPeakNumberFromDescentSet D)).symm

end

end RealRooted.ParkingFunctions
