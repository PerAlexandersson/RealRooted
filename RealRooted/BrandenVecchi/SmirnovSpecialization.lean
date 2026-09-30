import RealRooted.BrandenVecchi.ChowSignedWords

/-!
# Positive specialization of finite signed words

This module identifies the positive-alphabet specialization of the finite
Brändén--Vecchi signed-word enumerator with the literal Smirnov-word descent
polynomial. It records the survivor condition before passing to the alphabet
with no negative letters.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The zero/one specialization of a finite signed alphabet: negative letters
have weight zero and positive letters have weight one. -/
def zeroOneSignedLetterWeight {q p : ℕ} (letter : SignedLetter q p) : ℝ := by
  classical
  exact if letter.IsNegative then 0 else 1

@[simp]
theorem zeroOneSignedLetterWeight_negative {q p : ℕ} (i : Fin q) :
    zeroOneSignedLetterWeight (SignedLetter.negative (p := p) i) = 0 := by
  simp [zeroOneSignedLetterWeight]

@[simp]
theorem zeroOneSignedLetterWeight_positive {q p : ℕ} (i : Fin p) :
    zeroOneSignedLetterWeight (SignedLetter.positive (q := q) i) = 1 := by
  simp [zeroOneSignedLetterWeight]

/-- The finite list specialization with zero negative parameters and unit
positive parameters is exactly `zeroOneSignedLetterWeight`. -/
theorem finiteSignedLetterWeight_replicate_one_zero
    (q p : ℕ)
    (letter : SignedLetter (List.replicate q (0 : ℝ)).length
      (List.replicate p 1).length) :
    finiteSignedLetterWeight (List.replicate p (1 : ℝ))
        (List.replicate q 0) letter =
      zeroOneSignedLetterWeight letter := by
  rcases letter.exists_negative_or_positive with
    ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [hi, finiteSignedLetterWeight_negative]
    simp
  · rw [hi, finiteSignedLetterWeight_positive]
    simp

/-- Under the zero/one specialization, a word with nonzero letter-weight
contains only positive letters. -/
theorem isPositive_of_signedWordWeight_zeroOne_ne_zero
    {q p n : ℕ} (w : Fin n → SignedLetter q p)
    (hweight : signedWordWeight zeroOneSignedLetterWeight w ≠ 0)
    (i : Fin n) : (w i).IsPositive := by
  rcases (w i).exists_negative_or_positive with
    ⟨j, hj⟩ | ⟨j, hj⟩
  · exfalso
    apply hweight
    apply signedWordWeight_eq_zero_of_exists _ w (i := i)
    simp [hj]
  · rw [hj]
    exact SignedLetter.isPositive_positive j

/-- In the literal finite list specialization, every nonzero word monomial
contains only positive letters. -/
theorem isPositive_of_finiteSignedWordWeight_replicate_ne_zero
    {q p n : ℕ}
    (w : Fin n → SignedLetter (List.replicate q (0 : ℝ)).length
      (List.replicate p 1).length)
    (hweight : signedWordWeight
      (finiteSignedLetterWeight (List.replicate p (1 : ℝ))
        (List.replicate q 0)) w ≠ 0)
    (i : Fin n) : (w i).IsPositive := by
  apply isPositive_of_signedWordWeight_zeroOne_ne_zero w
  rw [← signedWordWeight_congr
    (finiteSignedLetterWeight_replicate_one_zero q p) w]
  exact hweight

/-- Remove the vacuous zero-sized negative block from the signed alphabet. -/
def positiveLetterOrderIso (m : ℕ) : SignedLetter 0 m ≃o Fin m :=
  Fin.castOrderIso (Nat.zero_add m)

/-- Apply `positiveLetterOrderIso` coordinatewise to a finite word. -/
def positiveWordEquiv (m n : ℕ) :
    (Fin n → SignedLetter 0 m) ≃ (Fin n → Fin m) where
  toFun w i := positiveLetterOrderIso m (w i)
  invFun w i := (positiveLetterOrderIso m).symm (w i)
  left_inv w := by
    funext i
    simp
  right_inv w := by
    funext i
    simp

/-- With no negative letters, signed admissibility is exactly the Smirnov
adjacent-inequality condition. -/
theorem isSignedWord_zero_negative_iff_isSmirnovWord
    {m n : ℕ} (w : Fin n → SignedLetter 0 m) :
    IsSignedWord n w ↔ IsSmirnovWord n (positiveWordEquiv m n w) := by
  cases n with
  | zero => simp [IsSmirnovWord]
  | succ n =>
      rw [isSignedWord_succ_iff]
      change
        (∀ i : Fin n,
          w i.castSucc ≠ w i.succ ∨ (w i.castSucc).IsNegative) ↔ _
      simp only [SignedLetter.isNegative_iff_val_lt, Nat.not_lt_zero,
        or_false]
      simp [IsSmirnovWord, positiveWordEquiv]

/-- The admissible words on a purely positive signed alphabet and the literal
Smirnov words are canonically equivalent. -/
def positiveSignedWordEquiv (m n : ℕ) :
    {w : Fin n → SignedLetter 0 m // IsSignedWord n w} ≃
      {w : Fin n → Fin m // IsSmirnovWord n w} where
  toFun w :=
    ⟨positiveWordEquiv m n w.1,
      (isSignedWord_zero_negative_iff_isSmirnovWord w.1).mp w.2⟩
  invFun w :=
    ⟨(positiveWordEquiv m n).symm w.1,
      (isSignedWord_zero_negative_iff_isSmirnovWord
        ((positiveWordEquiv m n).symm w.1)).mpr (by simpa using w.2)⟩
  left_inv w := by
    ext i
    simp
  right_inv w := by
    ext i
    simp

/-- The collision statistic vanishes on an admissible word over a purely
positive signed alphabet. -/
theorem signedCollisionNumber_eq_zero_of_isSignedWord_zero_negative
    {m n : ℕ} {w : Fin n → SignedLetter 0 m}
    (hw : IsSignedWord n w) : signedCollisionNumber w = 0 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [signedCollisionNumber_succ]
      apply Finset.card_eq_zero.mpr
      ext i
      constructor
      · intro hi
        have hnegative := hw.isNegative_of_mem_collisionSet hi
        exact ((Nat.not_lt_zero (w i.castSucc).val)
          ((SignedLetter.isNegative_iff_val_lt _).mp hnegative)).elim
      · simp

/-- The signed and Smirnov descent statistics agree under the canonical
positive-alphabet word equivalence, including the empty word. -/
theorem signedDescentNumber_eq_smirnovDescentNumber_positiveWordEquiv
    {m n : ℕ} (w : Fin n → SignedLetter 0 m) :
    signedDescentNumber w =
      smirnovDescentNumber (positiveWordEquiv m n w) := by
  cases n with
  | zero => rfl
  | succ n =>
      change RealRooted.ParkingFunctions.descentNumber w =
        RealRooted.ParkingFunctions.descentNumber
          (positiveWordEquiv m (n + 1) w)
      unfold RealRooted.ParkingFunctions.descentNumber
      apply congrArg Finset.card
      ext i
      simp [RealRooted.ParkingFunctions.mem_descentSet_iff,
        positiveWordEquiv]

/-- The all-one word weight is one on every purely positive word. -/
theorem signedWordWeight_one
    {m n : ℕ} (w : Fin n → SignedLetter 0 m) :
    signedWordWeight (fun _ => (1 : ℝ)) w = 1 := by
  simp [signedWordWeight]

/-- The all-one positive signed-word enumerator is the literal unweighted
Smirnov descent polynomial, with the empty-alphabet and empty-word cases
included. -/
theorem signedWordEnumerator_one_zero_negative_eq_smirnov
    (m n : ℕ) :
    signedWordEnumerator (fun _ : SignedLetter 0 m => (1 : ℝ)) n =
      weightedSmirnovPolynomial (fun _ : Fin m => (1 : ℝ)) n := by
  classical
  unfold signedWordEnumerator signedWords weightedSmirnovPolynomial smirnovWords
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (positiveWordEquiv m n)
  intro w
  by_cases hw : IsSignedWord n w
  · rw [ite_eq_left hw]
    rw [ite_eq_left ((isSignedWord_zero_negative_iff_isSmirnovWord w).mp hw)]
    rw [signedWordWeight_one]
    rw [signedCollisionNumber_eq_zero_of_isSignedWord_zero_negative hw]
    rw [signedDescentNumber_eq_smirnovDescentNumber_positiveWordEquiv]
    simp [smirnovWordWeight]
  · rw [ite_eq_right hw]
    rw [ite_eq_right (by
      simpa [isSignedWord_zero_negative_iff_isSmirnovWord] using hw)]

/-- The list-based all-one positive specialization agrees with the literal
Smirnov enumerator on its definitionally indexed alphabet. -/
theorem finiteSignedWordEnumerator_replicate_one_nil_eq_smirnov_length
    (m n : ℕ) :
    finiteSignedWordEnumerator (List.replicate m (1 : ℝ)) [] n =
      weightedSmirnovPolynomial
        (fun _ : Fin (List.replicate m (1 : ℝ)).length => (1 : ℝ)) n := by
  unfold finiteSignedWordEnumerator
  calc
    signedWordEnumerator
          (finiteSignedLetterWeight (List.replicate m (1 : ℝ)) []) n =
        signedWordEnumerator
          (fun _ : SignedLetter 0 (List.replicate m (1 : ℝ)).length =>
            (1 : ℝ)) n := by
      apply signedWordEnumerator_congr
      intro letter
      rcases letter.exists_negative_or_positive with
        ⟨i, hi⟩ | ⟨i, hi⟩
      · exact Fin.elim0 i
      · rw [hi, finiteSignedLetterWeight_positive]
        simp
    _ = weightedSmirnovPolynomial
          (fun _ : Fin (List.replicate m (1 : ℝ)).length => (1 : ℝ)) n :=
      signedWordEnumerator_one_zero_negative_eq_smirnov _ n

/-- The all-one Smirnov enumerator depends only on the cardinality of its
finite alphabet, not on a chosen equality witness for that cardinality. -/
theorem weightedSmirnovPolynomial_one_congr_card
    {m m' : ℕ} (h : m = m') (n : ℕ) :
    weightedSmirnovPolynomial (fun _ : Fin m => (1 : ℝ)) n =
      weightedSmirnovPolynomial (fun _ : Fin m' => (1 : ℝ)) n := by
  subst m'
  rfl

/-- The finite all-one positive signed-word enumerator is the literal
unweighted Smirnov descent polynomial. -/
theorem finiteSignedWordEnumerator_replicate_one_nil_eq_smirnov
    (m n : ℕ) :
    finiteSignedWordEnumerator (List.replicate m (1 : ℝ)) [] n =
      weightedSmirnovPolynomial (fun _ : Fin m => (1 : ℝ)) n := by
  calc
    finiteSignedWordEnumerator (List.replicate m (1 : ℝ)) [] n =
        weightedSmirnovPolynomial
          (fun _ : Fin (List.replicate m (1 : ℝ)).length => (1 : ℝ)) n :=
      finiteSignedWordEnumerator_replicate_one_nil_eq_smirnov_length m n
    _ = weightedSmirnovPolynomial (fun _ : Fin m => (1 : ℝ)) n :=
      weightedSmirnovPolynomial_one_congr_card (by simp) n

/-- Positive specialization of finite Brändén--Vecchi Theorem 8.11: the
finite supersymmetric Chow polynomial is the literal Smirnov descent
polynomial. -/
theorem finiteSupersymmetricChow_replicate_one_nil_eq_smirnov
    (m n : ℕ) :
    finiteSupersymmetricChow (List.replicate m (1 : ℝ)) [] n =
      weightedSmirnovPolynomial (fun _ : Fin m => (1 : ℝ)) n := by
  rw [finiteSupersymmetricChow_eq_finiteSignedWordEnumerator]
  exact finiteSignedWordEnumerator_replicate_one_nil_eq_smirnov m n

end

end RealRooted.BrandenVecchi
