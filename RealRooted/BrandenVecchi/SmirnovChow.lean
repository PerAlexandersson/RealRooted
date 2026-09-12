import RealRooted.BrandenVecchi.ChowToeplitz
import RealRooted.ParkingFunctions.Descents.Basic

/-!
# Weighted Smirnov words and Toeplitz Chow polynomials

This module gives the finite weighted form of Stanley's Smirnov-word identity.
The alphabet is `Fin m`, adjacent equal letters are forbidden, and a descent
contributes the polynomial variable `X`.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

variable {R : Type*} [CommRing R]

private theorem sum_fin_val_lt_succ {A : Type*} [AddCommMonoid A]
    {m k : ℕ} (hk : k < m) (f : Fin m → A) :
    (∑ i, if i.val < k + 1 then f i else 0) =
      (∑ i, if i.val < k then f i else 0) + f ⟨k, hk⟩ := by
  let kfin : Fin m := ⟨k, hk⟩
  rw [show f kfin = ∑ i, if i = kfin then f i else 0 by simp]
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro i
  by_cases hik : i.val < k
  · have hisucc : i.val < k + 1 := hik.trans_le (Nat.le_add_right k 1)
    have hine : i ≠ kfin := by
      intro h
      subst i
      exact (Nat.lt_irrefl k) hik
    simp [hik, hisucc, hine]
  · by_cases hieq : i = kfin
    · subst i
      simp [kfin]
    · have hisucc : ¬i.val < k + 1 := by
        intro hi
        have hle : i.val ≤ k := Nat.lt_succ_iff.mp (by simpa using hi)
        have hge : k ≤ i.val := Nat.le_of_not_gt hik
        apply hieq
        exact Fin.ext (le_antisymm hle hge)
      simp [hik, hieq, hisucc]

private theorem sum_fin_succ_le_val {A : Type*} [AddCommMonoid A]
    {m k : ℕ} (hk : k < m) (f : Fin m → A) :
    (∑ i, if k ≤ i.val then f i else 0) =
      f ⟨k, hk⟩ + ∑ i, if k + 1 ≤ i.val then f i else 0 := by
  let kfin : Fin m := ⟨k, hk⟩
  rw [show f kfin = ∑ i, if i = kfin then f i else 0 by simp]
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro i
  by_cases hik : k + 1 ≤ i.val
  · have hki : k ≤ i.val := le_trans (Nat.le_add_right k 1) hik
    have hine : i ≠ kfin := by
      intro h
      subst i
      exact (Nat.not_succ_le_self k) hik
    simp [hik, hki, hine]
  · by_cases hieq : i = kfin
    · subst i
      simp [kfin]
    · have hki : ¬k ≤ i.val := by
        intro hle
        have heq : i.val = k := by
          have hupper : i.val ≤ k :=
            Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hik)
          exact le_antisymm hupper hle
        exact hieq (Fin.ext heq)
      simp [hik, hieq, hki]

private theorem prod_fin_val_lt_succ {A : Type*} [CommMonoid A]
    {m k : ℕ} (hk : k < m) (f : Fin m → A) :
    (∏ i, if i.val < k + 1 then f i else 1) =
      (∏ i, if i.val < k then f i else 1) * f ⟨k, hk⟩ := by
  let kfin : Fin m := ⟨k, hk⟩
  rw [show f kfin = ∏ i, if i = kfin then f i else 1 by simp]
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_congr
  intro i
  by_cases hik : i.val < k
  · have hisucc : i.val < k + 1 := hik.trans_le (Nat.le_add_right k 1)
    have hine : i ≠ kfin := by
      intro h
      subst i
      exact (Nat.lt_irrefl k) hik
    simp [hik, hisucc, hine]
  · by_cases hieq : i = kfin
    · subst i
      simp [kfin]
    · have hisucc : ¬i.val < k + 1 := by
        intro hi
        have hle : i.val ≤ k := Nat.lt_succ_iff.mp (by simpa using hi)
        have hge : k ≤ i.val := Nat.le_of_not_gt hik
        apply hieq
        exact Fin.ext (le_antisymm hle hge)
      simp [hik, hieq, hisucc]

/-- A finite word is Smirnov when adjacent letters are distinct. -/
def IsSmirnovWord {m : ℕ} :
    (n : ℕ) → (Fin n → Fin m) → Prop
  | 0, _ => True
  | n + 1, word => ∀ i : Fin n,
      word i.castSucc ≠ word i.succ

/-- The literal finite set of length-`n` Smirnov words on `Fin m`. -/
def smirnovWords (m n : ℕ) : Finset (Fin n → Fin m) := by
  classical
  exact Finset.univ.filter (IsSmirnovWord n)

@[simp]
theorem mem_smirnovWords_iff {m n : ℕ} {word : Fin n → Fin m} :
    word ∈ smirnovWords m n ↔ IsSmirnovWord n word := by
  simp [smirnovWords]

/-- Appending a letter preserves the Smirnov condition exactly when the
prefix is Smirnov and its final letter differs from the appended letter. -/
theorem isSmirnovWord_snoc_iff {m n : ℕ}
    (word : Fin (n + 1) → Fin m) (i : Fin m) :
    IsSmirnovWord (n + 2) (Fin.snoc word i) ↔
      IsSmirnovWord (n + 1) word ∧ word (Fin.last n) ≠ i := by
  simp only [IsSmirnovWord]
  constructor
  · intro h
    constructor
    · intro j
      simpa only [Fin.succ_castSucc, Fin.snoc_castSucc] using h j.castSucc
    · simpa using h (Fin.last n)
  · rintro ⟨hword, hi⟩ j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa using hi
    · simpa only [Fin.succ_castSucc, Fin.snoc_castSucc] using hword k

/-- Product of the letter weights along a Smirnov word. -/
def smirnovWordWeight {m n : ℕ} (weight : Fin m → R)
    (word : Fin n → Fin m) : R :=
  ∏ i, weight (word i)

@[simp]
theorem smirnovWordWeight_zero {m : ℕ} (weight : Fin m → R)
    (word : Fin 0 → Fin m) :
    smirnovWordWeight weight word = 1 := by
  simp [smirnovWordWeight]

@[simp]
theorem smirnovWordWeight_snoc {m n : ℕ} (weight : Fin m → R)
    (word : Fin n → Fin m) (i : Fin m) :
    smirnovWordWeight weight (Fin.snoc word i) =
      smirnovWordWeight weight word * weight i := by
  unfold smirnovWordWeight
  simpa using
    (Fin.prod_univ_castSucc
      (fun j : Fin (n + 1) =>
        weight (@Fin.snoc n (fun _ => Fin m) word i j)))

/-- A zero-weight letter makes the whole word weight vanish. -/
theorem smirnovWordWeight_eq_zero_of_exists {m n : ℕ}
    (weight : Fin m → R) (word : Fin n → Fin m) {i : Fin n}
    (hi : weight (word i) = 0) :
    smirnovWordWeight weight word = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- The descent number, extended to the empty word. -/
def smirnovDescentNumber {m : ℕ} :
    {n : ℕ} → (Fin n → Fin m) → ℕ
  | 0, _ => 0
  | _ + 1, word => RealRooted.ParkingFunctions.descentNumber word

@[simp]
theorem smirnovDescentNumber_zero {m : ℕ} (word : Fin 0 → Fin m) :
    smirnovDescentNumber word = 0 := by
  simp [smirnovDescentNumber]

@[simp]
theorem smirnovDescentNumber_one {m : ℕ} (word : Fin 1 → Fin m) :
    smirnovDescentNumber word = 0 := by
  simp [smirnovDescentNumber,
    RealRooted.ParkingFunctions.descentNumber,
    RealRooted.ParkingFunctions.descentSet]

@[simp]
theorem smirnovDescentNumber_snoc {m n : ℕ}
    (word : Fin (n + 1) → Fin m) (i : Fin m) :
    smirnovDescentNumber (Fin.snoc word i) =
      smirnovDescentNumber word +
        if i < word (Fin.last n) then 1 else 0 := by
  simpa only [smirnovDescentNumber] using
    RealRooted.ParkingFunctions.descentNumber_snoc word i

/-- Literal weighted descent enumerator of length-`n` Smirnov words. -/
def weightedSmirnovPolynomial {m : ℕ} (weight : Fin m → R)
    (n : ℕ) : R[X] :=
  ∑ word ∈ smirnovWords m n,
    C (smirnovWordWeight weight word) *
      X ^ smirnovDescentNumber word

@[simp]
theorem weightedSmirnovPolynomial_zero {m : ℕ}
    (weight : Fin m → R) :
    weightedSmirnovPolynomial weight 0 = 1 := by
  simp [weightedSmirnovPolynomial, smirnovWords, IsSmirnovWord]

@[simp]
theorem weightedSmirnovPolynomial_zeroWeights {m : ℕ} (n : ℕ) :
    weightedSmirnovPolynomial (R := R) (fun _ : Fin m => 0)
      (n + 1) = 0 := by
  classical
  unfold weightedSmirnovPolynomial
  apply Finset.sum_eq_zero
  intro word _
  have hweight :
      smirnovWordWeight (R := R) (fun _ : Fin m => 0) word = 0 :=
    smirnovWordWeight_eq_zero_of_exists _ word
      (i := (0 : Fin (n + 1))) rfl
  simp [hweight]

/-- Pointwise equal weights give equal literal enumerators. -/
theorem weightedSmirnovPolynomial_congr {m : ℕ}
    {weight weight' : Fin m → R} (h : ∀ i, weight i = weight' i)
    (n : ℕ) :
    weightedSmirnovPolynomial weight n =
      weightedSmirnovPolynomial weight' n := by
  have hweight : weight = weight' := funext h
  rw [hweight]

/-- The contribution of nonempty Smirnov words with prescribed final
letter.  The index `n` counts the letters before that final letter. -/
def weightedSmirnovEndingSummand {m n : ℕ}
    (weight : Fin m → R) (word : Fin n → Fin m) (i : Fin m) : R[X] := by
  classical
  exact if IsSmirnovWord (n + 1) (Fin.snoc word i) then
      C (smirnovWordWeight weight (Fin.snoc word i)) *
        X ^ smirnovDescentNumber (Fin.snoc word i)
    else 0

def weightedSmirnovEnding {m : ℕ} (weight : Fin m → R)
    (n : ℕ) (i : Fin m) : R[X] := by
  classical
  exact ∑ word : Fin n → Fin m,
    weightedSmirnovEndingSummand weight word i

@[simp]
theorem weightedSmirnovEnding_zero {m : ℕ}
    (weight : Fin m → R) (i : Fin m) :
    weightedSmirnovEnding weight 0 i = C (weight i) := by
  have hsnoc (word : Fin 0 → Fin m) :
      Fin.snoc word i = fun _ => i := by
    exact Fin.snoc_zero word i
  rw [weightedSmirnovEnding]
  unfold weightedSmirnovEndingSummand
  simp_rw [hsnoc]
  simp [IsSmirnovWord, smirnovWordWeight]

/-- Appending a prescribed final letter gives the local last-letter
transition, including the forbidden-equality case. -/
theorem weightedSmirnovEndingSummand_snoc {m n : ℕ}
    (weight : Fin m → R) (word : Fin n → Fin m) (j i : Fin m) :
    weightedSmirnovEndingSummand weight (Fin.snoc word j) i =
      if j = i then 0 else
        C (weight i) * (if i < j then X else 1) *
          weightedSmirnovEndingSummand weight word j := by
  classical
  by_cases hji : j = i
  · have hnot :
        ¬IsSmirnovWord (n + 2) (Fin.snoc (Fin.snoc word j) i) := by
      intro h
      have hlast := ((isSmirnovWord_snoc_iff _ _).mp h).2
      exact hlast (by simpa using hji)
    rw [if_pos hji]
    simp [weightedSmirnovEndingSummand, hnot]
  · rw [if_neg hji]
    by_cases hword : IsSmirnovWord (n + 1) (Fin.snoc word j)
    · have hfull :
          IsSmirnovWord (n + 2) (Fin.snoc (Fin.snoc word j) i) :=
        (isSmirnovWord_snoc_iff _ _).mpr ⟨hword, by simpa using hji⟩
      rw [weightedSmirnovEndingSummand, if_pos hfull,
        weightedSmirnovEndingSummand, if_pos hword,
        smirnovWordWeight_snoc, smirnovDescentNumber_snoc]
      simp only [Fin.snoc_last]
      by_cases hij : i < j
      · rw [if_pos hij, if_pos hij, pow_succ]
        simp
        ring
      · rw [if_neg hij, if_neg hij]
        simp
        ring
    · rw [weightedSmirnovEndingSummand,
        if_neg (fun h => hword ((isSmirnovWord_snoc_iff _ _).mp h).1),
        weightedSmirnovEndingSummand, if_neg hword]
      simp

/-- Last-letter recurrence for the refined weighted enumerators. -/
theorem weightedSmirnovEnding_succ {m : ℕ}
    (weight : Fin m → R) (n : ℕ) (i : Fin m) :
    weightedSmirnovEnding weight (n + 1) i =
      ∑ j : Fin m, if j = i then 0 else
        C (weight i) * (if i < j then X else 1) *
          weightedSmirnovEnding weight n j := by
  classical
  rw [weightedSmirnovEnding]
  rw [show (∑ word : Fin (n + 1) → Fin m,
      weightedSmirnovEndingSummand weight word i) =
      ∑ j : Fin m, ∑ word : Fin n → Fin m,
        weightedSmirnovEndingSummand weight (Fin.snoc word j) i by
    symm
    simpa only [Fintype.sum_prod_type] using
      Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin m)
        (fun pair : Fin m × (Fin n → Fin m) =>
          weightedSmirnovEndingSummand weight
          (Fin.snoc pair.2 pair.1) i)
        (fun word : Fin (n + 1) → Fin m =>
          weightedSmirnovEndingSummand weight word i)
        (fun _ => rfl)]
  apply Fintype.sum_congr
  intro j
  simp_rw [weightedSmirnovEndingSummand_snoc]
  by_cases hji : j = i
  · simp [hji]
  · simp only [if_neg hji]
    rw [weightedSmirnovEnding]
    rw [← Finset.mul_sum]

/-- Ordered form of the last-letter recurrence: smaller preceding letters
create no descent and larger preceding letters create one descent. -/
theorem weightedSmirnovEnding_succ_split {m : ℕ}
    (weight : Fin m → R) (n : ℕ) (i : Fin m) :
    weightedSmirnovEnding weight (n + 1) i =
      C (weight i) *
        ((∑ j ∈ Finset.Iio i, weightedSmirnovEnding weight n j) +
          X * ∑ j ∈ Finset.Ioi i,
            weightedSmirnovEnding weight n j) := by
  have hIio (f : Fin m → R[X]) :
      (∑ j ∈ Finset.Iio i, f j) =
        ∑ j, if j < i then f j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have hIoi (f : Fin m → R[X]) :
      (∑ j ∈ Finset.Ioi i, f j) =
        ∑ j, if i < j then f j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  rw [weightedSmirnovEnding_succ]
  rw [mul_add, Finset.mul_sum, ← mul_assoc, Finset.mul_sum]
  rw [hIio, hIoi]
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro j
  by_cases hlt : j < i
  · have hne : j ≠ i := ne_of_lt hlt
    have hnlt : ¬i < j := not_lt_of_ge (le_of_lt hlt)
    simp [hlt, hne, hnlt]
  · by_cases hgt : i < j
    · have hne : j ≠ i := ne_of_gt hgt
      simp [hlt, hgt, hne]
    · have heq : j = i := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
      simp [heq]

/-- Every nonempty Smirnov word belongs to exactly one final-letter
refinement. -/
theorem weightedSmirnovPolynomial_succ {m : ℕ}
    (weight : Fin m → R) (n : ℕ) :
    weightedSmirnovPolynomial weight (n + 1) =
      ∑ i : Fin m, weightedSmirnovEnding weight n i := by
  classical
  unfold weightedSmirnovPolynomial smirnovWords
  simp only [Finset.sum_filter]
  rw [show (∑ word : Fin (n + 1) → Fin m,
      if IsSmirnovWord (n + 1) word then
        C (smirnovWordWeight weight word) *
          X ^ smirnovDescentNumber word
      else 0) =
      ∑ i : Fin m, ∑ word : Fin n → Fin m,
        weightedSmirnovEndingSummand weight word i by
    symm
    simpa only [Fintype.sum_prod_type,
      weightedSmirnovEndingSummand] using
      Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin m)
        (fun pair : Fin m × (Fin n → Fin m) =>
          if IsSmirnovWord (n + 1) (Fin.snoc pair.2 pair.1) then
            C (smirnovWordWeight weight (Fin.snoc pair.2 pair.1)) *
              X ^ smirnovDescentNumber (Fin.snoc pair.2 pair.1)
          else 0)
        (fun word : Fin (n + 1) → Fin m =>
          if IsSmirnovWord (n + 1) word then
            C (smirnovWordWeight weight word) *
              X ^ smirnovDescentNumber word
          else 0)
        (fun _ => rfl)]
  apply Fintype.sum_congr
  intro i
  rw [weightedSmirnovEnding]

@[simp]
theorem weightedSmirnovPolynomial_empty_succ (n : ℕ) :
    weightedSmirnovPolynomial (R := R) (fun i : Fin 0 => Fin.elim0 i)
      (n + 1) = 0 := by
  rw [weightedSmirnovPolynomial_succ]
  simp

/-- Formal length-generating series of the literal weighted Smirnov
polynomials. -/
def weightedSmirnovSeries {m : ℕ}
    (weight : Fin m → R) : PowerSeries R[X] :=
  PowerSeries.mk fun n => weightedSmirnovPolynomial weight n

/-- Formal length-generating series for words ending in `i`. -/
def weightedSmirnovEndingSeries {m : ℕ}
    (weight : Fin m → R) (i : Fin m) : PowerSeries R[X] :=
  PowerSeries.X * PowerSeries.mk fun n => weightedSmirnovEnding weight n i

@[simp]
theorem coeff_weightedSmirnovSeries {m : ℕ}
    (weight : Fin m → R) (n : ℕ) :
    PowerSeries.coeff n (weightedSmirnovSeries weight) =
      weightedSmirnovPolynomial weight n := by
  simp [weightedSmirnovSeries]

@[simp]
theorem coeff_weightedSmirnovEndingSeries_zero {m : ℕ}
    (weight : Fin m → R) (i : Fin m) :
    PowerSeries.coeff 0 (weightedSmirnovEndingSeries weight i) = 0 := by
  simp [weightedSmirnovEndingSeries]

@[simp]
theorem constantCoeff_weightedSmirnovEndingSeries {m : ℕ}
    (weight : Fin m → R) (i : Fin m) :
    PowerSeries.constantCoeff (weightedSmirnovEndingSeries weight i) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_weightedSmirnovEndingSeries_zero weight i

@[simp]
theorem coeff_weightedSmirnovEndingSeries_succ {m : ℕ}
    (weight : Fin m → R) (i : Fin m) (n : ℕ) :
    PowerSeries.coeff (n + 1) (weightedSmirnovEndingSeries weight i) =
      weightedSmirnovEnding weight n i := by
  simp [weightedSmirnovEndingSeries]

/-- The total series is one plus the sum of its final-letter refinements. -/
theorem weightedSmirnovSeries_eq_one_add_sum_ending {m : ℕ}
    (weight : Fin m → R) :
    weightedSmirnovSeries weight =
      1 + ∑ i : Fin m, weightedSmirnovEndingSeries weight i := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n => simp [weightedSmirnovPolynomial_succ]

/-- Formal-series form of the ordered last-letter recurrence. -/
theorem weightedSmirnovEndingSeries_eq {m : ℕ}
    (weight : Fin m → R) (i : Fin m) :
    weightedSmirnovEndingSeries weight i =
      PowerSeries.X *
        (PowerSeries.C (C (weight i)) *
          (1 +
            (∑ j ∈ Finset.Iio i,
              weightedSmirnovEndingSeries weight j) +
            PowerSeries.C X *
              ∑ j ∈ Finset.Ioi i,
                weightedSmirnovEndingSeries weight j)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul]
      cases n with
      | zero => simp
      | succ n =>
          simp [weightedSmirnovEnding_succ_split]

/-- The length-one series monomial attached to a letter. -/
def smirnovLetterSeries {m : ℕ} (weight : Fin m → R)
    (i : Fin m) : PowerSeries R[X] :=
  PowerSeries.X * PowerSeries.C (C (weight i))

/-- The cut series used to telescope the final-letter recurrence.  Letters
below `k` have coefficient one and letters at least `k` have coefficient
`X` in the Chow variable. -/
def smirnovCutSeries {m : ℕ} (weight : Fin m → R)
    (k : ℕ) : PowerSeries R[X] :=
  1 +
    (∑ i, if i.val < k then
      weightedSmirnovEndingSeries weight i else 0) +
    PowerSeries.C X *
      ∑ i, if k ≤ i.val then
        weightedSmirnovEndingSeries weight i else 0

/-- At a valid cut, the refined series is the letter monomial times the
cut expression with that letter omitted. -/
theorem weightedSmirnovEndingSeries_eq_letter_mul_cutCore
    {m k : ℕ} (weight : Fin m → R) (hk : k < m) :
    weightedSmirnovEndingSeries weight ⟨k, hk⟩ =
      smirnovLetterSeries weight ⟨k, hk⟩ *
        (1 +
          (∑ i, if i.val < k then
            weightedSmirnovEndingSeries weight i else 0) +
          PowerSeries.C X *
            ∑ i, if k + 1 ≤ i.val then
              weightedSmirnovEndingSeries weight i else 0) := by
  let kfin : Fin m := ⟨k, hk⟩
  have hIio :
      (∑ i ∈ Finset.Iio kfin,
          weightedSmirnovEndingSeries weight i) =
        ∑ i, if i.val < k then
          weightedSmirnovEndingSeries weight i else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iio]
    rfl
  have hIoi :
      (∑ i ∈ Finset.Ioi kfin,
          weightedSmirnovEndingSeries weight i) =
        ∑ i, if k + 1 ≤ i.val then
          weightedSmirnovEndingSeries weight i else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ioi]
    exact Nat.lt_iff_add_one_le
  rw [weightedSmirnovEndingSeries_eq, hIio, hIoi]
  simp only [smirnovLetterSeries]
  ring

/-- One local factor moves the telescope cut past a letter. -/
theorem smirnovCutSeries_factor_step {m k : ℕ}
    (weight : Fin m → R) (hk : k < m) :
    (1 + PowerSeries.C X * smirnovLetterSeries weight ⟨k, hk⟩) *
        smirnovCutSeries weight (k + 1) =
      (1 + smirnovLetterSeries weight ⟨k, hk⟩) *
        smirnovCutSeries weight k := by
  rw [smirnovCutSeries, smirnovCutSeries,
    sum_fin_val_lt_succ hk, sum_fin_succ_le_val hk]
  rw [weightedSmirnovEndingSeries_eq_letter_mul_cutCore weight hk]
  ring

/-- Product of the rescaled letter factors below a cut. -/
def smirnovRescaledFactorProduct {m : ℕ}
    (weight : Fin m → R) (k : ℕ) : PowerSeries R[X] :=
  ∏ i, if i.val < k then
    1 + PowerSeries.C X * smirnovLetterSeries weight i else 1

/-- Product of the unscaled letter factors below a cut. -/
def smirnovFactorProduct {m : ℕ}
    (weight : Fin m → R) (k : ℕ) : PowerSeries R[X] :=
  ∏ i, if i.val < k then
    1 + smirnovLetterSeries weight i else 1

/-- The product identity accumulated up to an arbitrary valid cut. -/
theorem smirnovFactor_telescope_aux {m : ℕ}
    (weight : Fin m → R) (k : ℕ) (hk : k ≤ m) :
    smirnovRescaledFactorProduct weight k * smirnovCutSeries weight k =
      smirnovFactorProduct weight k * smirnovCutSeries weight 0 := by
  induction k with
  | zero => simp [smirnovRescaledFactorProduct, smirnovFactorProduct]
  | succ k ih =>
      have hklt : k < m := Nat.lt_of_succ_le hk
      rw [smirnovRescaledFactorProduct,
        prod_fin_val_lt_succ hklt,
        smirnovFactorProduct, prod_fin_val_lt_succ hklt]
      calc
        (smirnovRescaledFactorProduct weight k *
              (1 + PowerSeries.C X *
                smirnovLetterSeries weight ⟨k, hklt⟩)) *
            smirnovCutSeries weight (k + 1) =
          smirnovRescaledFactorProduct weight k *
            ((1 + PowerSeries.C X *
                smirnovLetterSeries weight ⟨k, hklt⟩) *
              smirnovCutSeries weight (k + 1)) := by
            ring
        _ = smirnovRescaledFactorProduct weight k *
            ((1 + smirnovLetterSeries weight ⟨k, hklt⟩) *
              smirnovCutSeries weight k) := by
            rw [smirnovCutSeries_factor_step weight hklt]
        _ = (1 + smirnovLetterSeries weight ⟨k, hklt⟩) *
            (smirnovRescaledFactorProduct weight k *
              smirnovCutSeries weight k) := by
            ring
        _ = (1 + smirnovLetterSeries weight ⟨k, hklt⟩) *
            (smirnovFactorProduct weight k *
              smirnovCutSeries weight 0) := by
            rw [ih (Nat.le_of_succ_le hk)]
        _ = (smirnovFactorProduct weight k *
              (1 + smirnovLetterSeries weight ⟨k, hklt⟩)) *
            smirnovCutSeries weight 0 := by
            ring

@[simp]
theorem smirnovCutSeries_zero {m : ℕ} (weight : Fin m → R) :
    smirnovCutSeries weight 0 =
      1 - PowerSeries.C X +
        PowerSeries.C X * weightedSmirnovSeries weight := by
  rw [weightedSmirnovSeries_eq_one_add_sum_ending]
  simp [smirnovCutSeries]
  ring

@[simp]
theorem smirnovCutSeries_card {m : ℕ} (weight : Fin m → R) :
    smirnovCutSeries weight m = weightedSmirnovSeries weight := by
  have hsuffix :
      (∑ i : Fin m, if m ≤ i.val then
          weightedSmirnovEndingSeries weight i else 0) = 0 := by
    apply Fintype.sum_eq_zero
    intro i
    simp [Nat.not_le_of_lt i.isLt]
  rw [weightedSmirnovSeries_eq_one_add_sum_ending]
  simp [smirnovCutSeries, hsuffix]

/-- The literal weighted Smirnov series satisfies Stanley's finite-product
denominator identity. -/
theorem weightedSmirnovSeries_product_identity {m : ℕ}
    (weight : Fin m → R) :
    (∏ i : Fin m,
        (1 + PowerSeries.C X * smirnovLetterSeries weight i)) *
        weightedSmirnovSeries weight =
      (∏ i : Fin m, (1 + smirnovLetterSeries weight i)) *
        (1 - PowerSeries.C X +
          PowerSeries.C X * weightedSmirnovSeries weight) := by
  simpa [smirnovRescaledFactorProduct, smirnovFactorProduct,
    Fin.isLt] using smirnovFactor_telescope_aux weight m le_rfl

/-- The finite elementary-product series attached to the alphabet weights. -/
def finiteElementarySeries {m : ℕ}
    (weight : Fin m → R) : PowerSeries R :=
  ∏ i : Fin m,
    (1 + PowerSeries.X * PowerSeries.C (weight i))

/-- Coefficients of the finite elementary product. -/
def finiteElementaryCoefficient {m : ℕ}
    (weight : Fin m → R) (n : ℕ) : R :=
  PowerSeries.coeff n (finiteElementarySeries weight)

@[simp]
theorem finiteElementaryCoefficient_zero {m : ℕ}
    (weight : Fin m → R) :
    finiteElementaryCoefficient weight 0 = 1 := by
  simp [finiteElementaryCoefficient, finiteElementarySeries]

/-- Embedding the elementary coefficients into the Chow coefficient ring
gives the product of the letter factors. -/
theorem toeplitzCoefficientSeries_finiteElementaryCoefficient {m : ℕ}
    (weight : Fin m → R) :
    toeplitzCoefficientSeries (finiteElementaryCoefficient weight) =
      ∏ i : Fin m, (1 + smirnovLetterSeries weight i) := by
  calc
    toeplitzCoefficientSeries (finiteElementaryCoefficient weight) =
        (finiteElementarySeries weight).map Polynomial.C := by
      apply PowerSeries.ext
      intro n
      simp [finiteElementaryCoefficient]
    _ = ∏ i : Fin m, (1 + smirnovLetterSeries weight i) := by
      simp [finiteElementarySeries, smirnovLetterSeries]

/-- Rescaling the length variable by the Chow variable rescales every
elementary letter factor. -/
theorem rescale_toeplitzCoefficientSeries_finiteElementaryCoefficient
    {m : ℕ} (weight : Fin m → R) :
    PowerSeries.rescale X
        (toeplitzCoefficientSeries (finiteElementaryCoefficient weight)) =
      ∏ i : Fin m,
        (1 + PowerSeries.C X * smirnovLetterSeries weight i) := by
  rw [toeplitzCoefficientSeries_finiteElementaryCoefficient]
  simp only [map_prod, map_add, map_one, map_mul,
    PowerSeries.rescale_X, smirnovLetterSeries]
  apply Finset.prod_congr rfl
  intro i _
  rw [show PowerSeries.rescale X (PowerSeries.C (C (weight i))) =
      PowerSeries.C (C (weight i)) by
    apply PowerSeries.ext
    intro n
    cases n <;> simp]
  ring

/-- The lower Toeplitz matrix whose symbol is the finite elementary product. -/
def finiteElementaryToeplitz {m : ℕ}
    (weight : Fin m → R) : LowerTriangularMatrix R :=
  RealRooted.toeplitz (finiteElementaryCoefficient weight)

/-- The literal weighted Smirnov series is the Chow series of the finite
elementary-product Toeplitz matrix. -/
theorem weightedSmirnovSeries_eq_toeplitzChowSeries {m : ℕ}
    (weight : Fin m → R) :
    weightedSmirnovSeries weight =
      toeplitzChowSeries (finiteElementaryCoefficient weight) := by
  let a := finiteElementaryCoefficient weight
  let denominator :=
    PowerSeries.rescale X (toeplitzCoefficientSeries a) -
      PowerSeries.C X * toeplitzCoefficientSeries a
  have hsmirnov := weightedSmirnovSeries_product_identity weight
  rw [← rescale_toeplitzCoefficientSeries_finiteElementaryCoefficient,
    ← toeplitzCoefficientSeries_finiteElementaryCoefficient] at hsmirnov
  have hsmirnovDenominator :
      denominator * weightedSmirnovSeries weight =
        (1 - PowerSeries.C X) * toeplitzCoefficientSeries a := by
    dsimp only [denominator, a]
    linear_combination hsmirnov
  have hchowDenominator :
      denominator * toeplitzChowSeries a =
        (1 - PowerSeries.C X) * toeplitzCoefficientSeries a := by
    exact toeplitzChowSeries_mul_denominator a
      (finiteElementaryCoefficient_zero weight)
  have hconstantCoefficient :
      PowerSeries.constantCoeff (toeplitzCoefficientSeries a) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [a]
  have hconstantRescale :
      PowerSeries.constantCoeff
          (PowerSeries.rescale X (toeplitzCoefficientSeries a)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [a]
  have hconstant :
      PowerSeries.constantCoeff denominator = 1 - X := by
    simp [denominator, hconstantCoefficient, hconstantRescale]
  have hregularConstant : IsRegular (1 - X : R[X]) := by
    have hleft : IsLeftRegular (1 - X : R[X]) := by
      intro p q hpq
      apply (monic_X_sub_C (1 : R)).isRegular.left
      calc
        (X - C 1) * p = -((1 - X) * p) := by
          simp only [C_1]
          ring
        _ = -((1 - X) * q) := congrArg Neg.neg hpq
        _ = (X - C 1) * q := by
          simp only [C_1]
          ring
    exact ⟨hleft, fun p q hpq => hleft (by simpa [mul_comm] using hpq)⟩
  apply (PowerSeries.isRegular_of_isRegular_constantCoeff
    (hconstant ▸ hregularConstant)).left
  change denominator * weightedSmirnovSeries weight =
    denominator * toeplitzChowSeries a
  exact hsmirnovDenominator.trans hchowDenominator.symm

/-- Finite weighted Stanley identity: the literal Smirnov descent enumerator
is the Chow polynomial of the elementary-product Toeplitz matrix. -/
theorem weightedSmirnovPolynomial_eq_chowPolynomial {m : ℕ}
    (weight : Fin m → R) (n : ℕ) :
    weightedSmirnovPolynomial weight n =
      chowPolynomial (finiteElementaryToeplitz weight) n := by
  have hseries := weightedSmirnovSeries_eq_toeplitzChowSeries weight
  have hcoeff := congrArg (PowerSeries.coeff n) hseries
  simpa [finiteElementaryToeplitz] using hcoeff

/-- Literal weighted Smirnov polynomials commute with change of coefficient
ring. -/
theorem map_weightedSmirnovPolynomial
    {S : Type*} [CommRing S] (φ : R →+* S) {m : ℕ}
    (weight : Fin m → R) (n : ℕ) :
    (weightedSmirnovPolynomial weight n).map φ =
      weightedSmirnovPolynomial (fun i => φ (weight i)) n := by
  classical
  unfold weightedSmirnovPolynomial
  simp only [Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  apply Finset.sum_congr rfl
  intro word _
  congr 2
  exact map_prod φ (fun i => weight (word i)) Finset.univ

/-- The elementary-product Toeplitz coefficients commute with change of
coefficient ring. -/
theorem map_finiteElementaryCoefficient
    {S : Type*} [CommRing S] (φ : R →+* S) {m : ℕ}
    (weight : Fin m → R) (n : ℕ) :
    φ (finiteElementaryCoefficient weight n) =
      finiteElementaryCoefficient (fun i => φ (weight i)) n := by
  rw [finiteElementaryCoefficient, finiteElementaryCoefficient,
    ← PowerSeries.coeff_map]
  congr 1
  simp [finiteElementarySeries]

end

end RealRooted.BrandenVecchi
