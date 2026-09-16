import RealRooted.ParkingFunctions.Descents.Basic

/-!
# Finite signed words

This file gives the finite combinatorial domain in Brändén--Vecchi
Theorem 8.11.  An alphabet with `q` negative and `p` positive letters is
ordered as

`-q < ... < -1 < 1 < ... < p`.

Equal adjacent letters are allowed exactly for negative letters.  We define
the literal finite set of admissible words and its descent and collision
statistics, but no weighted enumerator or Chow polynomial.
-/

namespace RealRooted.BrandenVecchi

/-- A finite signed alphabet with `q` negative and `p` positive letters.

The first `q` elements represent `-q, ..., -1`; the remaining `p` elements
represent `1, ..., p`. -/
abbrev SignedLetter (q p : ℕ) := Fin (q + p)

namespace SignedLetter

/-- The negative letter `-(i + 1)`. -/
def negative {q p : ℕ} (i : Fin q) : SignedLetter q p :=
  Fin.castAdd p i.rev

/-- The positive letter `i + 1`. -/
def positive {q p : ℕ} (i : Fin p) : SignedLetter q p :=
  Fin.natAdd q i

/-- Recover the absolute-value index of a negative letter. -/
def negativeIndex? {q p : ℕ} : SignedLetter q p → Option (Fin q) :=
  Fin.addCases (fun i => some i.rev) (fun _ => none)

/-- Recover the zero-based index of a positive letter. -/
def positiveIndex? {q p : ℕ} : SignedLetter q p → Option (Fin p) :=
  Fin.addCases (fun _ => none) some

/-- A signed letter is negative when it lies in the negative block. -/
def IsNegative {q p : ℕ} (a : SignedLetter q p) : Prop :=
  ∃ i, negativeIndex? a = some i

/-- A signed letter is positive when it lies in the positive block. -/
def IsPositive {q p : ℕ} (a : SignedLetter q p) : Prop :=
  ∃ i, positiveIndex? a = some i

@[simp]
theorem negativeIndex?_negative {q p : ℕ} (i : Fin q) :
    negativeIndex? (negative (p := p) i) = some i := by
  simp [negativeIndex?, negative]

@[simp]
theorem negativeIndex?_positive {q p : ℕ} (i : Fin p) :
    negativeIndex? (positive (q := q) i) = none := by
  simp [negativeIndex?, positive]

@[simp]
theorem positiveIndex?_negative {q p : ℕ} (i : Fin q) :
    positiveIndex? (negative (p := p) i) = none := by
  simp [positiveIndex?, negative]

@[simp]
theorem positiveIndex?_positive {q p : ℕ} (i : Fin p) :
    positiveIndex? (positive (q := q) i) = some i := by
  simp [positiveIndex?, positive]

@[simp]
theorem isNegative_negative {q p : ℕ} (i : Fin q) :
    IsNegative (negative (p := p) i) := by
  simp [IsNegative]

@[simp]
theorem not_isNegative_positive {q p : ℕ} (i : Fin p) :
    ¬IsNegative (positive (q := q) i) := by
  simp [IsNegative]

@[simp]
theorem not_isPositive_negative {q p : ℕ} (i : Fin q) :
    ¬IsPositive (negative (p := p) i) := by
  simp [IsPositive]

@[simp]
theorem isPositive_positive {q p : ℕ} (i : Fin p) :
    IsPositive (positive (q := q) i) := by
  simp [IsPositive]

/-- Every finite signed letter belongs to one of the two sign blocks. -/
theorem isNegative_or_isPositive {q p : ℕ} (a : SignedLetter q p) :
    IsNegative a ∨ IsPositive a := by
  refine Fin.addCases ?_ ?_ a
  · intro i
    exact Or.inl (by simp [IsNegative, negativeIndex?])
  · intro i
    exact Or.inr (by simp [IsPositive, positiveIndex?])

/-- No finite signed letter belongs to both sign blocks. -/
theorem not_isNegative_and_isPositive {q p : ℕ} (a : SignedLetter q p) :
    ¬(IsNegative a ∧ IsPositive a) := by
  refine Fin.addCases ?_ ?_ a
  · intro i
    simp [IsPositive, positiveIndex?]
  · intro i
    simp [IsNegative, negativeIndex?]

/-- The negative block is the initial interval of the finite alphabet. -/
theorem isNegative_iff_val_lt {q p : ℕ} (a : SignedLetter q p) :
    IsNegative a ↔ a.val < q := by
  refine Fin.addCases ?_ ?_ a
  · intro i
    simp [IsNegative, negativeIndex?]
  · intro i
    change IsNegative (positive (q := q) i) ↔ _
    constructor
    · intro h
      exact (not_isNegative_positive i h).elim
    · intro h
      exact (Nat.not_lt_of_ge (Nat.le_add_right q i.val) h).elim

/-- The positive block is the final interval of the finite alphabet. -/
theorem isPositive_iff_le_val {q p : ℕ} (a : SignedLetter q p) :
    IsPositive a ↔ q ≤ a.val := by
  refine Fin.addCases ?_ ?_ a
  · intro i
    simp [IsPositive, positiveIndex?]
  · intro i
    change IsPositive (positive (q := q) i) ↔ _
    constructor
    · intro _
      exact Nat.le_add_right q i.val
    · intro _
      exact isPositive_positive i

/-- Every finite signed letter is a negative or positive constructor. -/
theorem exists_negative_or_positive {q p : ℕ} (a : SignedLetter q p) :
    (∃ i : Fin q, a = negative (p := p) i) ∨
      ∃ i : Fin p, a = positive (q := q) i := by
  refine Fin.addCases ?_ ?_ a
  · intro i
    left
    exact ⟨i.rev, by simp [negative]⟩
  · intro i
    right
    exact ⟨i, rfl⟩

/-- Negative letters are ordered by their signed values. -/
@[simp]
theorem negative_lt_negative_iff {q p : ℕ} {i j : Fin q} :
    negative (p := p) i < negative (p := p) j ↔ j < i := by
  change i.rev < j.rev ↔ j < i
  exact Fin.rev_lt_rev

/-- Every negative letter precedes every positive letter. -/
@[simp]
theorem negative_lt_positive {q p : ℕ} (i : Fin q) (j : Fin p) :
    negative (p := p) i < positive (q := q) j := by
  change i.rev.val < q + j.val
  exact lt_of_lt_of_le i.rev.isLt (Nat.le_add_right q j.val)

/-- Positive letters retain their natural order. -/
@[simp]
theorem positive_lt_positive_iff {q p : ℕ} {i j : Fin p} :
    positive (q := q) i < positive (q := q) j ↔ i < j := by
  simp [positive]

end SignedLetter

/-- The local adjacency rule for the signed words in Theorem 8.11. -/
def SignedAdjacent {q p : ℕ} (a b : SignedLetter q p) : Prop :=
  a ≠ b ∨ a.IsNegative

theorem signedAdjacent_iff_eq_imp_isNegative {q p : ℕ}
    (a b : SignedLetter q p) :
    SignedAdjacent a b ↔ a = b → a.IsNegative := by
  constructor
  · intro h hab
    rcases h with hne | hneg
    · exact (hne hab).elim
    · exact hneg
  · intro h
    by_cases hab : a = b
    · exact Or.inr (h hab)
    · exact Or.inl hab

@[simp]
theorem signedAdjacent_self_iff {q p : ℕ} (a : SignedLetter q p) :
    SignedAdjacent a a ↔ a.IsNegative := by
  simp [SignedAdjacent]

theorem signedAdjacent_comm {q p : ℕ} (a b : SignedLetter q p) :
    SignedAdjacent a b ↔ SignedAdjacent b a := by
  by_cases hab : a = b
  · subst b
    rfl
  · simp [SignedAdjacent, hab, Ne.symm hab]

/-- Admissibility of a finite signed word. -/
def IsSignedWord {q p : ℕ} :
    (n : ℕ) → (Fin n → SignedLetter q p) → Prop
  | 0, _ => True
  | n + 1, w => ∀ i : Fin n, SignedAdjacent (w i.castSucc) (w i.succ)

@[simp]
theorem isSignedWord_zero {q p : ℕ} (w : Fin 0 → SignedLetter q p) :
    IsSignedWord 0 w := by
  simp [IsSignedWord]

theorem isSignedWord_succ_iff {q p n : ℕ}
    (w : Fin (n + 1) → SignedLetter q p) :
    IsSignedWord (n + 1) w ↔
      ∀ i : Fin n, SignedAdjacent (w i.castSucc) (w i.succ) := by
  rfl

@[simp]
theorem isSignedWord_one {q p : ℕ} (w : Fin 1 → SignedLetter q p) :
    IsSignedWord 1 w := by
  rw [isSignedWord_succ_iff]
  intro i
  exact Fin.elim0 i

/-- Appending a letter preserves admissibility exactly when the old word is
admissible and the new final pair is admissible. -/
theorem isSignedWord_snoc_iff {q p n : ℕ}
    (w : Fin (n + 1) → SignedLetter q p) (x : SignedLetter q p) :
    IsSignedWord (n + 2) (Fin.snoc w x) ↔
      IsSignedWord (n + 1) w ∧ SignedAdjacent (w (Fin.last n)) x := by
  rw [isSignedWord_succ_iff, isSignedWord_succ_iff]
  constructor
  · intro h
    constructor
    · intro i
      simpa only [Fin.succ_castSucc, Fin.snoc_castSucc] using h i.castSucc
    · simpa using h (Fin.last n)
  · rintro ⟨hw, hx⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hx
    · simpa only [Fin.succ_castSucc, Fin.snoc_castSucc] using hw j

/-- The literal finite set of admissible signed words. -/
noncomputable def signedWords (q p n : ℕ) :
    Finset (Fin n → SignedLetter q p) := by
  classical
  exact Finset.univ.filter (IsSignedWord n)

@[simp]
theorem mem_signedWords_iff {q p n : ℕ}
    {w : Fin n → SignedLetter q p} :
    w ∈ signedWords q p n ↔ IsSignedWord n w := by
  simp [signedWords]

/-- The positions at which two adjacent letters collide. -/
def collisionSet {q p n : ℕ}
    (w : Fin (n + 1) → SignedLetter q p) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i.castSucc = w i.succ

@[simp]
theorem mem_collisionSet_iff {q p n : ℕ}
    (w : Fin (n + 1) → SignedLetter q p) (i : Fin n) :
    i ∈ collisionSet w ↔ w i.castSucc = w i.succ := by
  simp [collisionSet]

/-- Appending a letter preserves the old collision positions and adds the
new final position exactly when the two final letters agree. -/
theorem collisionSet_snoc {q p n : ℕ}
    (w : Fin (n + 1) → SignedLetter q p) (x : SignedLetter q p) :
    collisionSet (Fin.snoc w x) =
      (collisionSet w).map Fin.castSuccEmb ∪
        if w (Fin.last n) = x then {Fin.last n} else ∅ := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [mem_collisionSet_iff]
    by_cases h : w (Fin.last n) = x
    · simp [h]
    · simp [h]
  · simp only [mem_collisionSet_iff, Fin.succ_castSucc, Fin.snoc_castSucc]
    by_cases h : w (Fin.last n) = x
    · simp [h]
    · simp [h]

/-- Number of collisions in a finite signed word, including the empty word. -/
def signedCollisionNumber {q p : ℕ} :
    {n : ℕ} → (Fin n → SignedLetter q p) → ℕ
  | 0, _ => 0
  | _ + 1, w => (collisionSet w).card

/-- Number of descents in a finite signed word, including the empty word. -/
def signedDescentNumber {q p : ℕ} :
    {n : ℕ} → (Fin n → SignedLetter q p) → ℕ
  | 0, _ => 0
  | _ + 1, w => RealRooted.ParkingFunctions.descentNumber w

@[simp]
theorem signedCollisionNumber_zero {q p : ℕ}
    (w : Fin 0 → SignedLetter q p) : signedCollisionNumber w = 0 := rfl

@[simp]
theorem signedCollisionNumber_succ {q p n : ℕ}
    (w : Fin (n + 1) → SignedLetter q p) :
    signedCollisionNumber w = (collisionSet w).card := rfl

@[simp]
theorem signedDescentNumber_zero {q p : ℕ}
    (w : Fin 0 → SignedLetter q p) : signedDescentNumber w = 0 := rfl

@[simp]
theorem signedDescentNumber_succ {q p n : ℕ}
    (w : Fin (n + 1) → SignedLetter q p) :
    signedDescentNumber w =
      RealRooted.ParkingFunctions.descentNumber w := rfl

@[simp]
theorem signedCollisionNumber_one {q p : ℕ}
    (w : Fin 1 → SignedLetter q p) : signedCollisionNumber w = 0 := by
  simp [collisionSet]

@[simp]
theorem signedDescentNumber_one {q p : ℕ}
    (w : Fin 1 → SignedLetter q p) : signedDescentNumber w = 0 := by
  simp [RealRooted.ParkingFunctions.descentNumber,
    RealRooted.ParkingFunctions.descentSet]

/-- Appending a letter increments the collision number exactly when it agrees
with the old final letter. -/
theorem signedCollisionNumber_snoc {q p n : ℕ}
    (w : Fin (n + 1) → SignedLetter q p) (x : SignedLetter q p) :
    signedCollisionNumber (Fin.snoc w x) =
      signedCollisionNumber w + if w (Fin.last n) = x then 1 else 0 := by
  simp only [signedCollisionNumber_succ]
  rw [collisionSet_snoc]
  by_cases h : w (Fin.last n) = x
  · rw [if_pos h]
    have hdisjoint :
        Disjoint ((collisionSet w).map Fin.castSuccEmb) {Fin.last n} := by
      rw [Finset.disjoint_singleton_right]
      simp
    rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_map,
      Finset.card_singleton]
    simp [h]
  · rw [if_neg h]
    simp [h]

/-- Appending a letter increments the descent number exactly when the new
letter is smaller than the old final letter. -/
theorem signedDescentNumber_snoc {q p n : ℕ}
    (w : Fin (n + 1) → SignedLetter q p) (x : SignedLetter q p) :
    signedDescentNumber (Fin.snoc w x) =
      signedDescentNumber w + if x < w (Fin.last n) then 1 else 0 := by
  simpa only [signedDescentNumber_succ] using
    RealRooted.ParkingFunctions.descentNumber_snoc w x

theorem signedCollisionNumber_le {q p n : ℕ}
    (w : Fin n → SignedLetter q p) : signedCollisionNumber w ≤ n - 1 := by
  cases n with
  | zero => simp
  | succ n =>
      change (collisionSet w).card ≤ n
      simpa using Finset.card_le_card (Finset.subset_univ (collisionSet w))

theorem signedDescentNumber_le {q p n : ℕ}
    (w : Fin n → SignedLetter q p) : signedDescentNumber w ≤ n - 1 := by
  cases n with
  | zero => simp
  | succ n =>
      simpa using RealRooted.ParkingFunctions.descentNumber_le w

/-- Every collision in an admissible signed word occurs at a negative letter. -/
theorem IsSignedWord.isNegative_of_mem_collisionSet {q p n : ℕ}
    {w : Fin (n + 1) → SignedLetter q p} (hw : IsSignedWord (n + 1) w)
    {i : Fin n} (hi : i ∈ collisionSet w) :
    (w i.castSucc).IsNegative := by
  exact (signedAdjacent_iff_eq_imp_isNegative _ _).mp
    ((isSignedWord_succ_iff w).mp hw i) (mem_collisionSet_iff w i |>.mp hi)

end RealRooted.BrandenVecchi
