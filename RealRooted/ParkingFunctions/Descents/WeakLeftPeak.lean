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

@[simp]
theorem previousPosition_castSucc {n : ℕ} (i : Fin n) :
    previousPosition i.castSucc = (previousPosition i).castSucc := by
  apply Fin.ext
  rfl

@[simp]
theorem previousPosition_last {r : ℕ} :
    previousPosition (Fin.last (r + 1)) = (Fin.last r).castSucc := by
  apply Fin.ext
  simp [previousPosition]

@[simp]
theorem mem_map_castSuccEmb_iff {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n) :
    i.castSucc ∈ D.map Fin.castSuccEmb ↔ i ∈ D := by
  simp

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

/-- Extending a positive-width descent set at the right preserves its old
weak left peaks and adds the new final position precisely after a non-descent. -/
theorem weakLeftPeakSetFromDescentSet_extend_last {r : ℕ}
    (D : Finset (Fin (r + 1))) (h : Prop) [Decidable h] :
    weakLeftPeakSetFromDescentSet
        (D.map Fin.castSuccEmb ∪
          if h then {Fin.last (r + 1)} else ∅) =
      (weakLeftPeakSetFromDescentSet D).map Fin.castSuccEmb ∪
        if h ∧ Fin.last r ∉ D then {Fin.last (r + 1)} else ∅ := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · by_cases hh : h <;>
      by_cases hD : Fin.last r ∈ D <;>
        simp [hh, hD, mem_weakLeftPeakSetFromDescentSet_iff,
          previousPosition_last]
  · by_cases hh : h <;>
      by_cases hD : Fin.last r ∈ D <;>
        simp [hh, hD, mem_weakLeftPeakSetFromDescentSet_iff,
          previousPosition_castSucc, Fin.castSucc_ne_last]

/-- The cardinal form of extending a positive-width descent set at the right. -/
theorem weakLeftPeakNumberFromDescentSet_extend_last {r : ℕ}
    (D : Finset (Fin (r + 1))) (h : Prop) [Decidable h] :
    weakLeftPeakNumberFromDescentSet
        (D.map Fin.castSuccEmb ∪
          if h then {Fin.last (r + 1)} else ∅) =
      weakLeftPeakNumberFromDescentSet D +
        if h ∧ Fin.last r ∉ D then 1 else 0 := by
  unfold weakLeftPeakNumberFromDescentSet
  rw [weakLeftPeakSetFromDescentSet_extend_last]
  by_cases hnew : h ∧ Fin.last r ∉ D
  · simp only [ite_eq_left hnew]
    have hdisjoint : Disjoint
        ((weakLeftPeakSetFromDescentSet D).map Fin.castSuccEmb)
        {Fin.last (r + 1)} := by
      rw [Finset.disjoint_singleton_right]
      simp [Fin.castSucc_ne_last]
    rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_map,
      Finset.card_singleton]
  · simp only [ite_eq_right hnew, Finset.union_empty, Finset.card_map,
      Nat.add_zero]

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

/-- Appending a second letter creates a weak left peak exactly when the new
edge descends and the preceding edge does not. -/
theorem wordWeakLeftPeakNumber_snoc_snoc
    {r m : ℕ} (w : Fin (r + 1) → Fin m) (i j : Fin m) :
    wordWeakLeftPeakNumber (Fin.snoc (Fin.snoc w i) j) =
      wordWeakLeftPeakNumber (Fin.snoc w i) +
        if j < i ∧ ¬ i < w (Fin.last r) then 1 else 0 := by
  classical
  change weakLeftPeakNumberFromDescentSet
      (descentSet (Fin.snoc (Fin.snoc w i) j)) =
    weakLeftPeakNumberFromDescentSet (descentSet (Fin.snoc w i)) +
      if j < i ∧ ¬ i < w (Fin.last r) then 1 else 0
  rw [descentSet_snoc,
    weakLeftPeakNumberFromDescentSet_extend_last]
  simp only [Fin.snoc_last, mem_descentSet_snoc_last_iff]

/-- Integral weak-left-peak enumerator of all words of length `n` on an
alphabet of size `m`. -/
def literalWordWeakLeftPeakPolynomialIntOfAlphabet (m n : ℕ) : ℤ[X] :=
  ∑ w : Fin n → Fin m, X ^ wordWeakLeftPeakNumber w

/-- The all-word weak-left-peak enumerator on the extra alphabet used by the
parking-function transfer. -/
def literalWordWeakLeftPeakPolynomialInt (n : ℕ) : ℤ[X] :=
  literalWordWeakLeftPeakPolynomialIntOfAlphabet (n + 1) n

/-- Integral weak-left-peak enumerator of ordinary parking functions. -/
def parkingWeakLeftPeakPolynomialInt (n : ℕ) : ℤ[X] :=
  ∑ w ∈ parkingFunctions n, X ^ wordWeakLeftPeakNumber w

@[simp]
theorem literalWordWeakLeftPeakPolynomialInt_zero :
    literalWordWeakLeftPeakPolynomialInt 0 = 1 := by
  simp [literalWordWeakLeftPeakPolynomialInt,
    literalWordWeakLeftPeakPolynomialIntOfAlphabet]

@[simp]
theorem literalWordWeakLeftPeakPolynomialIntOfAlphabet_zero (m : ℕ) :
    literalWordWeakLeftPeakPolynomialIntOfAlphabet m 0 = 1 := by
  simp [literalWordWeakLeftPeakPolynomialIntOfAlphabet]

@[simp]
theorem literalWordWeakLeftPeakPolynomialIntOfAlphabet_one (m : ℕ) :
    literalWordWeakLeftPeakPolynomialIntOfAlphabet m 1 = C (m : ℤ) := by
  simp [literalWordWeakLeftPeakPolynomialIntOfAlphabet]

/-- The diagonal literal enumerator is the fixed-alphabet enumerator evaluated
at the extra alphabet size. -/
theorem literalWordWeakLeftPeakPolynomialInt_eq_ofAlphabet (n : ℕ) :
    literalWordWeakLeftPeakPolynomialInt n =
      literalWordWeakLeftPeakPolynomialIntOfAlphabet (n + 1) n :=
  rfl

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
