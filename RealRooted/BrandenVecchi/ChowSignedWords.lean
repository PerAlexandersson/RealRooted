import RealRooted.BrandenVecchi.ChowSupersymmetric
import RealRooted.BrandenVecchi.SmirnovSubstitutionSeries

/-!
# Finite supersymmetric Chow polynomials as signed-word enumerators

This module assembles the finite ingredients of Brändén--Vecchi, Theorem 8.11.
It first records the reusable one-letter formal-series identity behind the
positive/negative run substitution, then identifies the literal signed-word
enumerator with the finite supersymmetric Chow polynomial.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The unmarked length series associated with one signed letter. Positive
letters contribute `1 + w z`, while negative letters contribute
`(1 - w z)⁻¹`. -/
def signedLetterBaseSeries {R : Type*} [CommRing R] {q p : ℕ}
    (weight : SignedLetter q p → R) (letter : SignedLetter q p) :
    PowerSeries R[X] := by
  classical
  exact if letter.IsNegative then
    PowerSeries.rescale (C (weight letter)) (PowerSeries.mk 1)
  else 1 + PowerSeries.C (C (weight letter)) * PowerSeries.X

@[simp]
theorem signedLetterBaseSeries_negative {R : Type*} [CommRing R]
    {q p : ℕ} (weight : SignedLetter q p → R) {letter : SignedLetter q p}
    (hnegative : letter.IsNegative) :
    signedLetterBaseSeries weight letter =
      PowerSeries.rescale (C (weight letter)) (PowerSeries.mk 1) := by
  simp [signedLetterBaseSeries, hnegative]

@[simp]
theorem signedLetterBaseSeries_positive {R : Type*} [CommRing R]
    {q p : ℕ} (weight : SignedLetter q p → R) {letter : SignedLetter q p}
    (hpositive : letter.IsPositive) :
    signedLetterBaseSeries weight letter =
      1 + PowerSeries.C (C (weight letter)) * PowerSeries.X := by
  have hnotnegative : ¬letter.IsNegative := by
    intro hnegative
    exact letter.not_isNegative_and_isPositive ⟨hnegative, hpositive⟩
  simp [signedLetterBaseSeries, hnotnegative]

@[simp]
theorem constantCoeff_signedLetterBaseSeries {R : Type*} [CommRing R]
    {q p : ℕ} (weight : SignedLetter q p → R)
    (letter : SignedLetter q p) :
    PowerSeries.constantCoeff (signedLetterBaseSeries weight letter) = 1 := by
  rcases letter.isNegative_or_isPositive with hnegative | hpositive
  · rw [signedLetterBaseSeries_negative weight hnegative,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp
  · simp [signedLetterBaseSeries_positive weight hpositive]

private theorem geometricSeries_mul_one_sub
    {R : Type*} [CommRing R] (a : R[X]) :
    PowerSeries.rescale a (PowerSeries.mk 1) *
        (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale a)
    (PowerSeries.mk_one_mul_one_sub_eq_one R[X])
  simpa [map_sub, PowerSeries.rescale_X] using h

/-- The positive and negative one-letter factors obey the same marked/unmarked
cross identity. This is the local algebraic reason that the run substitution
produces the supersymmetric Toeplitz series. -/
theorem rescale_signedLetterBaseSeries_mul_one_add_run
    {R : Type*} [CommRing R] {q p : ℕ}
    (weight : SignedLetter q p → R) (letter : SignedLetter q p) :
    PowerSeries.rescale X (signedLetterBaseSeries weight letter) *
        (1 + signedRunSeries weight letter) =
      signedLetterBaseSeries weight letter *
        (1 + PowerSeries.C X * signedRunSeries weight letter) := by
  rcases letter.isNegative_or_isPositive with hnegative | hpositive
  · rw [signedLetterBaseSeries_negative weight hnegative]
    rw [show signedRunSeries weight letter =
        negativeRunSeries (weight letter) by
      simp [signedRunSeries, hnegative]]
    let a : R[X] := C (weight letter)
    let common : PowerSeries R[X] :=
      PowerSeries.rescale (a * (1 + X)) (PowerSeries.mk 1)
    have hcommon :
        common *
            (1 - PowerSeries.C (a * (1 + X)) * PowerSeries.X) = 1 := by
      exact geometricSeries_mul_one_sub (a * (1 + X))
    have hcommon' :
        (1 - PowerSeries.C (a * (1 + X)) * PowerSeries.X) *
            common = 1 := by
      simpa [mul_comm] using hcommon
    have hone :
        1 + negativeRunSeries (weight letter) =
          (1 - PowerSeries.C (a * X) * PowerSeries.X) * common := by
      rw [negativeRunSeries]
      change 1 + PowerSeries.C a * PowerSeries.X * common = _
      calc
        1 + PowerSeries.C a * PowerSeries.X * common =
            (1 - PowerSeries.C (a * (1 + X)) * PowerSeries.X) * common +
              PowerSeries.C a * PowerSeries.X * common := by
          rw [hcommon']
        _ = (1 - PowerSeries.C (a * X) * PowerSeries.X) * common := by
          simp only [map_mul, map_add, map_one]
          ring
    have hmarked :
        1 + PowerSeries.C X * negativeRunSeries (weight letter) =
          (1 - PowerSeries.C a * PowerSeries.X) * common := by
      rw [negativeRunSeries]
      change 1 + PowerSeries.C X *
          (PowerSeries.C a * PowerSeries.X * common) = _
      calc
        1 + PowerSeries.C X *
              (PowerSeries.C a * PowerSeries.X * common) =
            (1 - PowerSeries.C (a * (1 + X)) * PowerSeries.X) * common +
              PowerSeries.C X *
                (PowerSeries.C a * PowerSeries.X * common) := by
          rw [hcommon']
        _ = (1 - PowerSeries.C a * PowerSeries.X) * common := by
          simp only [map_mul, map_add, map_one]
          ring
    rw [hone, hmarked]
    have hrescale :
        PowerSeries.rescale X
            (PowerSeries.rescale a (PowerSeries.mk 1)) =
          PowerSeries.rescale (a * X) (PowerSeries.mk 1) := by
      apply PowerSeries.ext
      intro n
      simp [mul_pow, mul_comm]
    rw [hrescale]
    change PowerSeries.rescale (a * X) (PowerSeries.mk 1) *
          ((1 - PowerSeries.C (a * X) * PowerSeries.X) * common) =
        PowerSeries.rescale a (PowerSeries.mk 1) *
          ((1 - PowerSeries.C a * PowerSeries.X) * common)
    calc
      PowerSeries.rescale (a * X) (PowerSeries.mk 1) *
            ((1 - PowerSeries.C (a * X) * PowerSeries.X) * common) =
          (PowerSeries.rescale (a * X) (PowerSeries.mk 1) *
              (1 - PowerSeries.C (a * X) * PowerSeries.X)) * common := by
        ring
      _ = common := by rw [geometricSeries_mul_one_sub]; simp
      _ = (PowerSeries.rescale a (PowerSeries.mk 1) *
              (1 - PowerSeries.C a * PowerSeries.X)) * common := by
        rw [geometricSeries_mul_one_sub]
        simp
      _ = PowerSeries.rescale a (PowerSeries.mk 1) *
            ((1 - PowerSeries.C a * PowerSeries.X) * common) := by
        ring
  · rw [signedLetterBaseSeries_positive weight hpositive]
    rw [show signedRunSeries weight letter =
        positiveRunSeries (weight letter) by
      have hnotnegative : ¬letter.IsNegative := by
        intro hnegative
        exact letter.not_isNegative_and_isPositive ⟨hnegative, hpositive⟩
      simp [signedRunSeries, hnotnegative]]
    have hrescaleC :
        PowerSeries.rescale X
            (PowerSeries.C (C (weight letter))) =
          PowerSeries.C (C (weight letter)) := by
      apply PowerSeries.ext
      intro n
      cases n <;> simp
    simp [positiveRunSeries, map_add, PowerSeries.rescale_X,
      hrescaleC]
    ring

/-- Multiplying the one-letter cross identities gives the finite-alphabet
marked/unmarked product identity. -/
theorem rescale_prod_signedLetterBaseSeries_mul_prod_one_add_run
    {R : Type*} [CommRing R] {q p : ℕ}
    (weight : SignedLetter q p → R) :
    PowerSeries.rescale X
          (∏ letter : SignedLetter q p,
            signedLetterBaseSeries weight letter) *
        (∏ letter : SignedLetter q p,
          (1 + signedRunSeries weight letter)) =
      (∏ letter : SignedLetter q p,
          signedLetterBaseSeries weight letter) *
        (∏ letter : SignedLetter q p,
          (1 + PowerSeries.C X * signedRunSeries weight letter)) := by
  rw [map_prod]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Fintype.prod_congr
  intro letter
  exact rescale_signedLetterBaseSeries_mul_one_add_run weight letter

/-- The product multiplying the substituted Smirnov series has regular
constant coefficient, so it may be cancelled over an arbitrary commutative
coefficient ring. -/
theorem isRegular_prod_one_add_C_mul_signedRunSeries
    {R : Type*} [CommRing R] {q p : ℕ}
    (weight : SignedLetter q p → R) :
    IsRegular
      (∏ letter : SignedLetter q p,
        (1 + PowerSeries.C X * signedRunSeries weight letter)) := by
  have hzero (letter : SignedLetter q p) :
      PowerSeries.constantCoeff (signedRunSeries weight letter) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_signedRunSeries_zero weight letter
  apply PowerSeries.isRegular_of_isRegular_constantCoeff
  rw [map_prod]
  simpa [hzero] using (isRegular_one : IsRegular (1 : R[X]))

/-! ## Finite supersymmetric specialization -/

/-- The finite supersymmetric coefficient series after embedding each real
coefficient as a constant polynomial in the Chow variable. -/
def finiteSupersymmetricPolynomialSeries (xs ys : List ℝ) :
    PowerSeries ℝ[X] :=
  PowerSeries.map C (finiteSupersymmetricSeries xs ys)

@[simp]
theorem coeff_finiteSupersymmetricPolynomialSeries
    (xs ys : List ℝ) (n : ℕ) :
    PowerSeries.coeff n (finiteSupersymmetricPolynomialSeries xs ys) =
      C (finiteSupersymmetricCoeff xs ys n) := by
  simp [finiteSupersymmetricPolynomialSeries,
    finiteSupersymmetricCoeff]

/-- The polynomial-valued supersymmetric series is exactly the generic
Toeplitz coefficient series used by the Chow denominator theorem. -/
theorem finiteSupersymmetricPolynomialSeries_eq_toeplitzCoefficientSeries
    (xs ys : List ℝ) :
    finiteSupersymmetricPolynomialSeries xs ys =
      toeplitzCoefficientSeries (finiteSupersymmetricCoeff xs ys) := by
  apply PowerSeries.ext
  intro n
  simp

private theorem map_supersymmetricNumeratorFactor (x : ℝ) :
    PowerSeries.map C (supersymmetricNumeratorFactor x) =
      1 + PowerSeries.C (C x) * PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [supersymmetricNumeratorFactor]
  | succ n =>
      cases n with
      | zero => simp [supersymmetricNumeratorFactor]
      | succ n => simp [supersymmetricNumeratorFactor]

private theorem map_supersymmetricDenominatorFactor (y : ℝ) :
    PowerSeries.map C (supersymmetricDenominatorFactor y) =
      PowerSeries.rescale (C y) (PowerSeries.mk 1) := by
  apply PowerSeries.ext
  intro n
  simp [supersymmetricDenominatorFactor]

private theorem map_prod_supersymmetricNumeratorFactors (xs : List ℝ) :
    (xs.map
        (PowerSeries.map C ∘ supersymmetricNumeratorFactor)).prod =
      (xs.map fun x =>
        1 + PowerSeries.C (C x) * PowerSeries.X).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.prod_cons, Function.comp_apply]
      rw [map_supersymmetricNumeratorFactor, ih]

private theorem map_prod_supersymmetricDenominatorFactors (ys : List ℝ) :
    (ys.map
        (PowerSeries.map C ∘ supersymmetricDenominatorFactor)).prod =
      (ys.map fun y =>
        PowerSeries.rescale (C y) (PowerSeries.mk 1)).prod := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.prod_cons, Function.comp_apply]
      rw [map_supersymmetricDenominatorFactor, ih]

/-- The product of the unmarked one-letter series is the finite
supersymmetric coefficient series. The reversal built into the negative
alphabet affects its order but not this commutative product. -/
theorem prod_signedLetterBaseSeries_finiteSignedLetterWeight
    (xs ys : List ℝ) :
    (∏ letter : SignedLetter ys.length xs.length,
        signedLetterBaseSeries (finiteSignedLetterWeight xs ys) letter) =
      finiteSupersymmetricPolynomialSeries xs ys := by
  rw [Fin.prod_univ_add]
  have hnegative :
      (∏ i : Fin ys.length,
          signedLetterBaseSeries (finiteSignedLetterWeight xs ys)
            (Fin.castAdd xs.length i)) =
        (ys.map fun y =>
          PowerSeries.rescale (C y) (PowerSeries.mk 1)).prod := by
    calc
      (∏ i : Fin ys.length,
          signedLetterBaseSeries (finiteSignedLetterWeight xs ys)
            (Fin.castAdd xs.length i)) =
          ∏ i : Fin ys.length,
            PowerSeries.rescale (C (ys.get i.rev))
              (PowerSeries.mk 1) := by
        apply Fintype.prod_congr
        intro i
        have hi :
            SignedLetter.IsNegative
              (Fin.castAdd xs.length i :
                SignedLetter ys.length xs.length) := by
          rw [SignedLetter.isNegative_iff_val_lt]
          exact i.isLt
        rw [signedLetterBaseSeries_negative _ hi]
        simp [finiteSignedLetterWeight]
      _ = ∏ i : Fin ys.length,
            PowerSeries.rescale (C (ys.get i))
              (PowerSeries.mk 1) := by
        apply Fintype.prod_equiv Fin.revPerm
        intro i
        simp
      _ = (ys.map fun y =>
          PowerSeries.rescale (C y) (PowerSeries.mk 1)).prod := by
        simpa using Fin.prod_univ_fun_getElem ys
          (fun y => PowerSeries.rescale (C y) (PowerSeries.mk 1))
  have hpositive :
      (∏ i : Fin xs.length,
          signedLetterBaseSeries (finiteSignedLetterWeight xs ys)
            (Fin.natAdd ys.length i)) =
        (xs.map fun x =>
          1 + PowerSeries.C (C x) * PowerSeries.X).prod := by
    calc
      (∏ i : Fin xs.length,
          signedLetterBaseSeries (finiteSignedLetterWeight xs ys)
            (Fin.natAdd ys.length i)) =
          ∏ i : Fin xs.length,
            (1 + PowerSeries.C (C (xs.get i)) * PowerSeries.X) := by
        apply Fintype.prod_congr
        intro i
        change signedLetterBaseSeries (finiteSignedLetterWeight xs ys)
            (SignedLetter.positive i) = _
        rw [signedLetterBaseSeries_positive _
          (SignedLetter.isPositive_positive i)]
        rw [finiteSignedLetterWeight_positive]
      _ = (xs.map fun x =>
          1 + PowerSeries.C (C x) * PowerSeries.X).prod := by
        simpa using Fin.prod_univ_fun_getElem xs
          (fun x => 1 + PowerSeries.C (C x) * PowerSeries.X)
  rw [hnegative, hpositive, finiteSupersymmetricPolynomialSeries,
    finiteSupersymmetricSeries, map_mul, map_list_prod, map_list_prod]
  rw [List.map_map, List.map_map]
  rw [map_prod_supersymmetricNumeratorFactors,
    map_prod_supersymmetricDenominatorFactors]
  ring

/-- Adjoining zero parameters does not change the finite supersymmetric
coefficient series. -/
theorem finiteSupersymmetricSeries_append_zeros
    (xs ys : List ℝ) (r s : ℕ) :
    finiteSupersymmetricSeries (xs ++ List.replicate s 0)
        (ys ++ List.replicate r 0) =
      finiteSupersymmetricSeries xs ys := by
  simp [finiteSupersymmetricSeries, supersymmetricNumeratorFactor,
    supersymmetricDenominatorFactor]

/-- Adjoining zero parameters leaves every finite supersymmetric coefficient
unchanged. -/
theorem finiteSupersymmetricCoeff_append_zeros
    (xs ys : List ℝ) (r s n : ℕ) :
    finiteSupersymmetricCoeff (xs ++ List.replicate s 0)
        (ys ++ List.replicate r 0) n =
      finiteSupersymmetricCoeff xs ys n := by
  simp [finiteSupersymmetricCoeff,
    finiteSupersymmetricSeries_append_zeros]

/-- Adjoining zero parameters leaves the actual finite supersymmetric Chow
polynomial unchanged. -/
theorem finiteSupersymmetricChow_append_zeros
    (xs ys : List ℝ) (r s n : ℕ) :
    finiteSupersymmetricChow (xs ++ List.replicate s 0)
        (ys ++ List.replicate r 0) n =
      finiteSupersymmetricChow xs ys n := by
  unfold finiteSupersymmetricChow finiteSupersymmetricToeplitz
  congr 2
  funext k
  exact finiteSupersymmetricCoeff_append_zeros xs ys r s k

/-! ## Theorem 8.11 assembly -/

/-- The signed-run Smirnov series satisfies the generic Toeplitz Chow product
equation for the product of its unmarked one-letter series. -/
theorem signedRunSmirnovSeries_product_identity
    {R : Type*} [CommRing R] {q p : ℕ}
    (weight : SignedLetter q p → R) :
    PowerSeries.rescale X
          (∏ letter : SignedLetter q p,
            signedLetterBaseSeries weight letter) *
        smirnovSubstitutionSeries (A := R[X]) X
          (signedRunSeries weight) =
      (∏ letter : SignedLetter q p,
          signedLetterBaseSeries weight letter) *
        (1 - PowerSeries.C X +
          PowerSeries.C X *
            smirnovSubstitutionSeries (A := R[X]) X
              (signedRunSeries weight)) := by
  let left : PowerSeries R[X] :=
    ∏ letter : SignedLetter q p,
      (1 + PowerSeries.C X * signedRunSeries weight letter)
  let right : PowerSeries R[X] :=
    ∏ letter : SignedLetter q p,
      (1 + signedRunSeries weight letter)
  let base : PowerSeries R[X] :=
    ∏ letter : SignedLetter q p,
      signedLetterBaseSeries weight letter
  let series : PowerSeries R[X] :=
    smirnovSubstitutionSeries (A := R[X]) X (signedRunSeries weight)
  let tail : PowerSeries R[X] :=
    1 - PowerSeries.C X + PowerSeries.C X * series
  have hsmirnov : left * series = right * tail := by
    exact signedRunSeries_smirnov_product_identity weight
  have hcross : PowerSeries.rescale X base * right = base * left := by
    exact rescale_prod_signedLetterBaseSeries_mul_prod_one_add_run weight
  have hregular : IsRegular left :=
    isRegular_prod_one_add_C_mul_signedRunSeries weight
  apply hregular.left
  change left * (PowerSeries.rescale X base * series) =
    left * (base * tail)
  calc
    left * (PowerSeries.rescale X base * series) =
        PowerSeries.rescale X base * (left * series) := by ring
    _ = PowerSeries.rescale X base * (right * tail) := by rw [hsmirnov]
    _ = (PowerSeries.rescale X base * right) * tail := by ring
    _ = (base * left) * tail := by rw [hcross]
    _ = left * (base * tail) := by ring

/-- The finite signed-run Smirnov series is the Chow series of the finite
supersymmetric Toeplitz coefficients. -/
theorem finiteSignedRunSmirnovSeries_eq_toeplitzChowSeries
    (xs ys : List ℝ) :
    smirnovSubstitutionSeries (A := ℝ[X]) X
        (signedRunSeries (finiteSignedLetterWeight xs ys)) =
      toeplitzChowSeries (finiteSupersymmetricCoeff xs ys) := by
  apply eq_toeplitzChowSeries_of_rescale_mul
    (finiteSupersymmetricCoeff xs ys)
    (finiteSupersymmetricCoeff_zero xs ys)
  have h := signedRunSmirnovSeries_product_identity
    (finiteSignedLetterWeight xs ys)
  rw [prod_signedLetterBaseSeries_finiteSignedLetterWeight,
    finiteSupersymmetricPolynomialSeries_eq_toeplitzCoefficientSeries] at h
  exact h

/-- Finite Brändén--Vecchi Theorem 8.11: the actual supersymmetric Toeplitz
Chow polynomial equals the literal signed-word descent/collision enumerator. -/
theorem finiteSupersymmetricChow_eq_finiteSignedWordEnumerator
    (xs ys : List ℝ) (n : ℕ) :
    finiteSupersymmetricChow xs ys n =
      finiteSignedWordEnumerator xs ys n := by
  rw [finiteSignedWordEnumerator]
  rw [signedWordEnumerator_eq_signedSmirnovSubstitutionCoeff]
  rw [← coeff_smirnovSubstitutionSeries_signedRunSeries]
  rw [finiteSignedRunSmirnovSeries_eq_toeplitzChowSeries]
  simp [finiteSupersymmetricChow, finiteSupersymmetricToeplitz]

/-- The finite Chow identity remains valid after adjoining outer zero-weight
negative and positive letters to the literal signed alphabet. -/
theorem finiteSupersymmetricChow_eq_signedWordEnumerator_add_zero_letters
    (xs ys : List ℝ) (r s n : ℕ) :
    finiteSupersymmetricChow xs ys n =
      signedWordEnumerator
        (extendSignedLetterWeight
          (signedLetterExtend ys.length xs.length r s).toEmbedding
          (finiteSignedLetterWeight xs ys)) n := by
  rw [finiteSupersymmetricChow_eq_finiteSignedWordEnumerator,
    finiteSignedWordEnumerator]
  exact signedWordEnumerator_add_zero_letters
    (finiteSignedLetterWeight xs ys) r s n

/-- In list coordinates, adjoining zero-weight outer letters leaves the
literal finite signed-word enumerator unchanged. -/
theorem finiteSignedWordEnumerator_append_zeros
    (xs ys : List ℝ) (r s n : ℕ) :
    finiteSignedWordEnumerator (xs ++ List.replicate s 0)
        (ys ++ List.replicate r 0) n =
      finiteSignedWordEnumerator xs ys n := by
  rw [← finiteSupersymmetricChow_eq_finiteSignedWordEnumerator,
    finiteSupersymmetricChow_append_zeros,
    finiteSupersymmetricChow_eq_finiteSignedWordEnumerator]

/-- With nonnegative parameters, the literal finite signed-word enumerator
has nonnegative coefficients. -/
theorem finiteSignedWordEnumerator_nonnegCoeffs
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    HasNonnegCoeffs (finiteSignedWordEnumerator xs ys n) := by
  rw [← finiteSupersymmetricChow_eq_finiteSignedWordEnumerator]
  exact finiteSupersymmetricChow_nonnegCoeffs hxs hys n

/-- With nonnegative parameters, the literal finite signed-word enumerator is
zero or split over the reals. -/
theorem finiteSignedWordEnumerator_eq_zero_or_splits
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    finiteSignedWordEnumerator xs ys n = 0 ∨
      (finiteSignedWordEnumerator xs ys n).Splits := by
  rw [← finiteSupersymmetricChow_eq_finiteSignedWordEnumerator]
  exact finiteSupersymmetricChow_eq_zero_or_splits hxs hys n

/-- With nonnegative parameters, every literal finite signed-word enumerator
is a Pólya-frequency polynomial. -/
theorem finiteSignedWordEnumerator_isPFPolynomial
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    IsPFPolynomial (finiteSignedWordEnumerator xs ys n) := by
  exact IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (finiteSignedWordEnumerator_nonnegCoeffs hxs hys n)
    (finiteSignedWordEnumerator_eq_zero_or_splits hxs hys n)

/-- Consecutive literal finite signed-word enumerators are in zero-aware
proper position for nonnegative parameters. -/
theorem finiteSignedWordEnumerator_prec0_succ
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) (n : ℕ) :
    Prec0 (finiteSignedWordEnumerator xs ys n)
      (finiteSignedWordEnumerator xs ys (n + 1)) := by
  rw [← finiteSupersymmetricChow_eq_finiteSignedWordEnumerator,
    ← finiteSupersymmetricChow_eq_finiteSignedWordEnumerator]
  exact finiteSupersymmetricChow_prec0_succ hxs hys n

end

end RealRooted.BrandenVecchi
