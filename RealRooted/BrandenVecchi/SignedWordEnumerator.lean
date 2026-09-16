import RealRooted.BrandenVecchi.SignedWords
import Mathlib.Algebra.BigOperators.Fin

/-!
# Weighted finite signed-word enumerators

This file defines the literal finite sum in Brändén--Vecchi Theorem 8.11.
The Chow-polynomial identification and the negative-run compression argument
are separate later layers.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- Product of the letter weights along a finite signed word. -/
def signedWordWeight {q p n : ℕ} (weight : SignedLetter q p → R)
    (w : Fin n → SignedLetter q p) : R :=
  ∏ i, weight (w i)

/-- The literal weighted polynomial over admissible signed words.

The factors are exactly `t^des(w)`, `(1+t)^col(w)`, and the product of
letter weights. -/
def signedWordEnumerator {q p : ℕ} (weight : SignedLetter q p → R)
    (n : ℕ) : R[X] :=
  ∑ w ∈ signedWords q p n,
    C (signedWordWeight weight w) *
      X ^ signedDescentNumber w *
      (1 + X) ^ signedCollisionNumber w

/-- The weight function coming from finite positive and negative lists. -/
def finiteSignedLetterWeight (xs ys : List R) :
    SignedLetter ys.length xs.length → R :=
  Fin.addCases (fun i => ys.get i.rev) (fun i => xs.get i)

/-- The literal finite-variable signed-word enumerator. -/
def finiteSignedWordEnumerator (xs ys : List R) (n : ℕ) : R[X] :=
  signedWordEnumerator (finiteSignedLetterWeight xs ys) n

omit [CommSemiring R] in
@[simp]
theorem finiteSignedLetterWeight_negative (xs ys : List R)
    (i : Fin ys.length) :
    finiteSignedLetterWeight xs ys
      (SignedLetter.negative (p := xs.length) i) = ys.get i := by
  rw [finiteSignedLetterWeight, SignedLetter.negative, Fin.addCases_left]
  rw [Fin.rev_rev]

omit [CommSemiring R] in
@[simp]
theorem finiteSignedLetterWeight_positive (xs ys : List R)
    (i : Fin xs.length) :
    finiteSignedLetterWeight xs ys
      (SignedLetter.positive (q := ys.length) i) = xs.get i := by
  simp [finiteSignedLetterWeight, SignedLetter.positive]

@[simp]
theorem signedWordWeight_zero {q p : ℕ}
    (weight : SignedLetter q p → R)
    (w : Fin 0 → SignedLetter q p) :
    signedWordWeight weight w = 1 := by
  simp [signedWordWeight]

/-- Appending a letter multiplies the word weight by its weight. -/
theorem signedWordWeight_snoc {q p n : ℕ}
    (weight : SignedLetter q p → R)
    (w : Fin n → SignedLetter q p) (x : SignedLetter q p) :
    signedWordWeight weight (Fin.snoc w x) =
      signedWordWeight weight w * weight x := by
  unfold signedWordWeight
  simpa using
    (Fin.prod_univ_castSucc
      (fun i : Fin (n + 1) =>
        weight (@Fin.snoc n (fun _ => SignedLetter q p) w x i)))

/-- A zero-weight letter makes the whole word monomial vanish. -/
theorem signedWordWeight_eq_zero_of_exists {q p n : ℕ}
    (weight : SignedLetter q p → R)
    (w : Fin n → SignedLetter q p) {i : Fin n}
    (hi : weight (w i) = 0) :
    signedWordWeight weight w = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- Pointwise equal weight functions give equal word weights. -/
theorem signedWordWeight_congr {q p n : ℕ}
    {weight weight' : SignedLetter q p → R}
    (h : ∀ a, weight a = weight' a)
    (w : Fin n → SignedLetter q p) :
    signedWordWeight weight w = signedWordWeight weight' w := by
  apply Finset.prod_congr rfl
  intro i _
  exact h (w i)

/-- Pointwise equal weight functions give equal literal enumerators. -/
theorem signedWordEnumerator_congr {q p : ℕ}
    {weight weight' : SignedLetter q p → R}
    (h : ∀ a, weight a = weight' a) (n : ℕ) :
    signedWordEnumerator weight n = signedWordEnumerator weight' n := by
  unfold signedWordEnumerator
  apply Finset.sum_congr rfl
  intro w _
  rw [signedWordWeight_congr h w]

@[simp]
theorem signedWordEnumerator_zero {q p : ℕ}
    (weight : SignedLetter q p → R) :
    signedWordEnumerator weight 0 = 1 := by
  simp [signedWordEnumerator, signedWords, IsSignedWord]

@[simp]
theorem finiteSignedWordEnumerator_zero (xs ys : List R) :
    finiteSignedWordEnumerator xs ys 0 = 1 := by
  simp [finiteSignedWordEnumerator]

/-- The length-one enumerator is the sum of the letter weights. -/
theorem signedWordEnumerator_one {q p : ℕ}
    (weight : SignedLetter q p → R) :
    signedWordEnumerator weight 1 = ∑ a, C (weight a) := by
  classical
  have hwords : signedWords q p 1 = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro w _
    exact isSignedWord_one w
  rw [signedWordEnumerator, hwords]
  simpa [signedWordWeight, signedDescentNumber, signedCollisionNumber,
    collisionSet, RealRooted.ParkingFunctions.descentNumber,
    RealRooted.ParkingFunctions.descentSet] using
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) (SignedLetter q p))
      (fun w => C (weight (w 0))) (fun a => C (weight a)) (fun _ => rfl)

/-- Extensionality of the list-valued specialization. -/
theorem finiteSignedWordEnumerator_congr {xs xs' ys ys' : List R}
    (hxs : xs = xs') (hys : ys = ys') (n : ℕ) :
    finiteSignedWordEnumerator xs ys n =
      finiteSignedWordEnumerator xs' ys' n := by
  subst xs'
  subst ys'
  rfl

/-! ## Alphabet embeddings -/

/-- Map every letter of a word through an embedding. -/
def mapSignedWord {q p q' p' n : ℕ}
    (e : SignedLetter q p ↪ SignedLetter q' p')
    (w : Fin n → SignedLetter q p) : Fin n → SignedLetter q' p' :=
  fun i => e (w i)

theorem mapSignedWord_injective {q p q' p' n : ℕ}
    (e : SignedLetter q p ↪ SignedLetter q' p') :
    Function.Injective (mapSignedWord (n := n) e) := by
  intro u v huv
  funext i
  exact e.injective (congrFun huv i)

/-- Order embeddings preserve the descent statistic of a word. -/
theorem signedDescentNumber_map {q p q' p' n : ℕ}
    (e : SignedLetter q p ↪o SignedLetter q' p')
    (w : Fin n → SignedLetter q p) :
    signedDescentNumber (mapSignedWord e.toEmbedding w) =
      signedDescentNumber w := by
  cases n with
  | zero => simp
  | succ n =>
      unfold signedDescentNumber RealRooted.ParkingFunctions.descentNumber
      apply congrArg Finset.card
      ext i
      simp [RealRooted.ParkingFunctions.mem_descentSet_iff, mapSignedWord]

/-- Embeddings preserve the collision statistic of a word. -/
theorem signedCollisionNumber_map {q p q' p' n : ℕ}
    (e : SignedLetter q p ↪ SignedLetter q' p')
    (w : Fin n → SignedLetter q p) :
    signedCollisionNumber (mapSignedWord e w) = signedCollisionNumber w := by
  cases n with
  | zero => simp
  | succ n =>
      unfold signedCollisionNumber
      apply congrArg Finset.card
      ext i
      simp [mem_collisionSet_iff, mapSignedWord]

/-- A sign-preserving order embedding preserves and reflects signed-word
admissibility. -/
theorem isSignedWord_map_iff {q p q' p' n : ℕ}
    (e : SignedLetter q p ↪o SignedLetter q' p')
    (hneg : ∀ a, (e a).IsNegative ↔ a.IsNegative)
    (w : Fin n → SignedLetter q p) :
    IsSignedWord n (mapSignedWord e.toEmbedding w) ↔ IsSignedWord n w := by
  cases n with
  | zero => simp
  | succ n =>
      rw [isSignedWord_succ_iff, isSignedWord_succ_iff]
      constructor
      · intro hw i
        rcases hw i with hne | hnegative
        · left
          intro heq
          exact hne (congrArg e heq)
        · exact Or.inr ((hneg _).mp hnegative)
      · intro hw i
        rcases hw i with hne | hnegative
        · exact Or.inl (fun heq => hne (e.injective heq))
        · exact Or.inr ((hneg _).mpr hnegative)

/-- Mapping a word and transporting every letter weight preserves its word
weight. -/
theorem signedWordWeight_map {q p q' p' n : ℕ}
    (e : SignedLetter q p ↪ SignedLetter q' p')
    (weight : SignedLetter q p → R)
    (weight' : SignedLetter q' p' → R)
    (hweight : ∀ a, weight' (e a) = weight a)
    (w : Fin n → SignedLetter q p) :
    signedWordWeight weight' (mapSignedWord e w) =
      signedWordWeight weight w := by
  apply Finset.prod_congr rfl
  intro i _
  exact hweight (w i)

/-- Extend weights along an embedding, assigning weight zero away from its
image. -/
def extendSignedLetterWeight {q p q' p' : ℕ}
    (e : SignedLetter q p ↪ SignedLetter q' p')
    (weight : SignedLetter q p → R) (b : SignedLetter q' p') : R :=
  if h : ∃ a, e a = b then weight (Classical.choose h) else 0

@[simp]
theorem extendSignedLetterWeight_apply {q p q' p' : ℕ}
    (e : SignedLetter q p ↪ SignedLetter q' p')
    (weight : SignedLetter q p → R) (a : SignedLetter q p) :
    extendSignedLetterWeight e weight (e a) = weight a := by
  rw [extendSignedLetterWeight, dif_pos ⟨a, rfl⟩]
  apply congrArg weight
  exact e.injective (Classical.choose_spec (show ∃ c, e c = e a from ⟨a, rfl⟩))

theorem extendSignedLetterWeight_eq_zero_of_not_mem_range
    {q p q' p' : ℕ} (e : SignedLetter q p ↪ SignedLetter q' p')
    (weight : SignedLetter q p → R) {b : SignedLetter q' p'}
    (hb : b ∉ Set.range e) :
    extendSignedLetterWeight e weight b = 0 := by
  rw [extendSignedLetterWeight, dif_neg]
  simpa [Set.mem_range] using hb

/-- Adding zero-weight letters along a sign-preserving order embedding does
not change the literal signed-word enumerator. -/
theorem signedWordEnumerator_extend {q p q' p' : ℕ}
    (e : SignedLetter q p ↪o SignedLetter q' p')
    (hneg : ∀ a, (e a).IsNegative ↔ a.IsNegative)
    (weight : SignedLetter q p → R) (n : ℕ) :
    signedWordEnumerator weight n =
      signedWordEnumerator (extendSignedLetterWeight e.toEmbedding weight) n := by
  classical
  let wordEmbedding :
      (Fin n → SignedLetter q p) ↪ (Fin n → SignedLetter q' p') :=
    ⟨mapSignedWord e.toEmbedding, mapSignedWord_injective e.toEmbedding⟩
  let sourceWords := signedWords q p n
  let targetWords := signedWords q' p' n
  let mappedWords := sourceWords.map wordEmbedding
  let sourceTerm : (Fin n → SignedLetter q p) → R[X] := fun w =>
    C (signedWordWeight weight w) * X ^ signedDescentNumber w *
      (1 + X) ^ signedCollisionNumber w
  let targetTerm : (Fin n → SignedLetter q' p') → R[X] := fun w =>
    C (signedWordWeight (extendSignedLetterWeight e.toEmbedding weight) w) *
      X ^ signedDescentNumber w * (1 + X) ^ signedCollisionNumber w
  have hmapped : mappedWords ⊆ targetWords := by
    intro w hw
    simp only [mappedWords, Finset.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [mem_signedWords_iff]
    change IsSignedWord n (mapSignedWord e.toEmbedding v)
    rw [isSignedWord_map_iff e hneg]
    exact mem_signedWords_iff.mp hv
  have hterm (w : Fin n → SignedLetter q p) :
      targetTerm (wordEmbedding w) = sourceTerm w := by
    change targetTerm (mapSignedWord e.toEmbedding w) = sourceTerm w
    dsimp only [targetTerm, sourceTerm]
    rw [signedWordWeight_map e.toEmbedding weight
        (extendSignedLetterWeight e.toEmbedding weight)
        (extendSignedLetterWeight_apply e.toEmbedding weight) w,
      signedDescentNumber_map e w,
      signedCollisionNumber_map e.toEmbedding w]
  have houtside : ∀ w ∈ targetWords, w ∉ mappedWords → targetTerm w = 0 := by
    intro w hw hnot
    have hexists : ∃ i, w i ∉ Set.range e := by
      by_contra hall
      have hall' : ∀ i, ∃ a, e a = w i := by
        intro i
        by_contra hi
        exact hall ⟨i, by simpa [Set.mem_range] using hi⟩
      let v : Fin n → SignedLetter q p := fun i => Classical.choose (hall' i)
      have hmap : mapSignedWord e.toEmbedding v = w := by
        funext i
        exact Classical.choose_spec (hall' i)
      have hv : v ∈ sourceWords := by
        rw [mem_signedWords_iff]
        rw [← isSignedWord_map_iff e hneg, hmap]
        exact mem_signedWords_iff.mp hw
      apply hnot
      exact Finset.mem_map.mpr ⟨v, hv, hmap⟩
    obtain ⟨i, hi⟩ := hexists
    have hzero : extendSignedLetterWeight e.toEmbedding weight (w i) = 0 :=
      extendSignedLetterWeight_eq_zero_of_not_mem_range e.toEmbedding weight hi
    have hwordzero :
        signedWordWeight (extendSignedLetterWeight e.toEmbedding weight) w = 0 :=
      signedWordWeight_eq_zero_of_exists _ w hzero
    simp [targetTerm, hwordzero]
  calc
    signedWordEnumerator weight n = ∑ w ∈ sourceWords, sourceTerm w := by
      rfl
    _ = ∑ w ∈ mappedWords, targetTerm w := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro w _
      exact (hterm w).symm
    _ = ∑ w ∈ targetWords, targetTerm w :=
      Finset.sum_subset hmapped houtside
    _ = signedWordEnumerator
        (extendSignedLetterWeight e.toEmbedding weight) n := by
      rfl

/-- Embed an alphabet by adding `r` new outer negative letters and `s` new
largest positive letters. -/
def signedLetterExtend (q p r s : ℕ) :
    SignedLetter q p ↪o SignedLetter (r + q) (p + s) where
  toFun a := ⟨r + a.val, by lia⟩
  inj' a b h := by
    apply Fin.ext
    exact Nat.add_left_cancel (Fin.ext_iff.mp h)
  map_rel_iff' := by
    intro a b
    simp

/-- The concrete alphabet extension preserves the negative block. -/
theorem signedLetterExtend_isNegative_iff (q p r s : ℕ)
    (a : SignedLetter q p) :
    ((signedLetterExtend q p r s) a).IsNegative ↔ a.IsNegative := by
  rw [SignedLetter.isNegative_iff_val_lt,
    SignedLetter.isNegative_iff_val_lt]
  simp [signedLetterExtend]

/-- Adjoining zero-weight outer negative and positive letters leaves the
enumerator unchanged. -/
theorem signedWordEnumerator_add_zero_letters {q p : ℕ}
    (weight : SignedLetter q p → R) (r s n : ℕ) :
    signedWordEnumerator weight n =
      signedWordEnumerator
        (extendSignedLetterWeight (signedLetterExtend q p r s).toEmbedding weight) n := by
  exact signedWordEnumerator_extend (signedLetterExtend q p r s)
    (signedLetterExtend_isNegative_iff q p r s) weight n

end

end RealRooted.BrandenVecchi
