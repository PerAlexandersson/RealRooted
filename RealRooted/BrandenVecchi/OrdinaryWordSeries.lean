import RealRooted.BrandenVecchi.SmirnovSubstitutionSeries

/-!
# Ordinary words from Smirnov skeletons

Every ordinary word compresses to a Smirnov skeleton together with a positive
length for each skeleton letter. A run with letter weight `a` is encoded by
the geometric series `a z + a^2 z^2 + ...`. This module records the algebraic
series and its finite-product symmetry before identifying its coefficients
with literal words.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The positive-length geometric series for one constant-letter run. -/
def ordinaryRunSeries {R : Type*} [CommSemiring R] (a : R) :
    PowerSeries R[X] :=
  PowerSeries.C (C a) * PowerSeries.X *
    PowerSeries.rescale (C a) (PowerSeries.mk 1)

@[simp]
theorem coeff_ordinaryRunSeries_zero {R : Type*} [CommSemiring R]
    (a : R) :
    PowerSeries.coeff 0 (ordinaryRunSeries a) = 0 := by
  simp [ordinaryRunSeries]

@[simp]
theorem coeff_ordinaryRunSeries_succ {R : Type*} [CommSemiring R]
    (a : R) (r : ℕ) :
    PowerSeries.coeff (r + 1) (ordinaryRunSeries a) = C (a ^ (r + 1)) := by
  rw [ordinaryRunSeries, mul_assoc, PowerSeries.coeff_C_mul]
  rw [show PowerSeries.coeff (r + 1)
      (PowerSeries.X * PowerSeries.rescale (C a) (PowerSeries.mk 1)) =
        PowerSeries.coeff r
          (PowerSeries.rescale (C a) (PowerSeries.mk 1)) by
    simp]
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
    Pi.one_apply, mul_one]
  simp [pow_succ']

/-- The geometric run series has denominator `1 - a z`. -/
theorem ordinaryRunSeries_mul_one_sub {R : Type*} [CommRing R] (a : R) :
    ordinaryRunSeries a *
        (1 - PowerSeries.C (C a) * PowerSeries.X) =
      PowerSeries.C (C a) * PowerSeries.X := by
  have h := congrArg (PowerSeries.rescale (C a))
    (PowerSeries.mk_one_mul_one_sub_eq_one R[X])
  rw [ordinaryRunSeries, mul_assoc, mul_assoc]
  rw [show PowerSeries.rescale (C a) (PowerSeries.mk 1) *
      (1 - PowerSeries.C (C a) * PowerSeries.X) = 1 by
    simpa [map_sub, PowerSeries.rescale_X] using h]
  simp

/-- Product of the letter weights along a finite word. -/
def wordWeight {R : Type*} [CommSemiring R] {m n : ℕ}
    (weight : Fin m → R) (word : Fin n → Fin m) : R :=
  ∏ i, weight (word i)

@[simp]
theorem wordWeight_zero {R : Type*} [CommSemiring R] {m : ℕ}
    (weight : Fin m → R) (word : Fin 0 → Fin m) :
    wordWeight weight word = 1 := by
  simp [wordWeight]

@[simp]
theorem wordWeight_snoc {R : Type*} [CommSemiring R] {m n : ℕ}
    (weight : Fin m → R) (word : Fin n → Fin m) (i : Fin m) :
    wordWeight weight (Fin.snoc word i) =
      wordWeight weight word * weight i := by
  unfold wordWeight
  simpa using
    (Fin.prod_univ_castSucc
      (fun j : Fin (n + 1) =>
        weight (@Fin.snoc n (fun _ => Fin m) word i j)))

/-- The literal weighted descent polynomial over all finite words. -/
def weightedWordPolynomial {R : Type*} [CommSemiring R] {m : ℕ}
    (weight : Fin m → R) (n : ℕ) : R[X] :=
  ∑ word : Fin n → Fin m,
    C (wordWeight weight word) *
      X ^ RealRooted.ParkingFunctions.wordDescentNumber word

@[simp]
theorem weightedWordPolynomial_zero {R : Type*} [CommSemiring R]
    {m : ℕ} (weight : Fin m → R) :
    weightedWordPolynomial weight 0 = 1 := by
  simp [weightedWordPolynomial]

/-- Contribution of a word obtained by appending one prescribed final
letter. -/
def weightedWordEndingSummand {R : Type*} [CommSemiring R] {m n : ℕ}
    (weight : Fin m → R) (word : Fin n → Fin m) (i : Fin m) : R[X] :=
  C (wordWeight weight (Fin.snoc word i)) *
    X ^ RealRooted.ParkingFunctions.wordDescentNumber (Fin.snoc word i)

/-- Weighted ordinary words with a prescribed final letter. The index counts
the letters preceding that final letter. -/
def weightedWordEnding {R : Type*} [CommSemiring R] {m : ℕ}
    (weight : Fin m → R) (n : ℕ) (i : Fin m) : R[X] :=
  ∑ word : Fin n → Fin m, weightedWordEndingSummand weight word i

@[simp]
theorem weightedWordEnding_zero {R : Type*} [CommSemiring R] {m : ℕ}
    (weight : Fin m → R) (i : Fin m) :
    weightedWordEnding weight 0 i = C (weight i) := by
  simp [weightedWordEnding, weightedWordEndingSummand]

/-- Appending a final letter gives the ordinary last-letter transition. -/
theorem weightedWordEndingSummand_snoc {R : Type*} [CommSemiring R]
    {m n : ℕ} (weight : Fin m → R) (word : Fin n → Fin m)
    (j i : Fin m) :
    weightedWordEndingSummand weight (Fin.snoc word j) i =
      C (weight i) * (if i < j then X else 1) *
        weightedWordEndingSummand weight word j := by
  classical
  unfold weightedWordEndingSummand
  rw [wordWeight_snoc,
    RealRooted.ParkingFunctions.wordDescentNumber_snoc]
  simp only [Fin.snoc_last]
  by_cases hij : i < j
  · rw [if_pos hij, if_pos hij, pow_succ]
    simp
    ring
  · rw [if_neg hij, if_neg hij]
    simp
    ring

/-- Last-letter recurrence for weighted ordinary words. -/
theorem weightedWordEnding_succ {R : Type*} [CommSemiring R] {m : ℕ}
    (weight : Fin m → R) (n : ℕ) (i : Fin m) :
    weightedWordEnding weight (n + 1) i =
      ∑ j : Fin m, C (weight i) * (if i < j then X else 1) *
        weightedWordEnding weight n j := by
  classical
  rw [weightedWordEnding]
  rw [show (∑ word : Fin (n + 1) → Fin m,
      weightedWordEndingSummand weight word i) =
      ∑ j : Fin m, ∑ word : Fin n → Fin m,
        weightedWordEndingSummand weight (Fin.snoc word j) i by
    symm
    simpa only [Fintype.sum_prod_type] using
      Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin m)
        (fun pair : Fin m × (Fin n → Fin m) =>
          weightedWordEndingSummand weight
            (Fin.snoc pair.2 pair.1) i)
        (fun word : Fin (n + 1) → Fin m =>
          weightedWordEndingSummand weight word i)
        (fun _ => rfl)]
  apply Fintype.sum_congr
  intro j
  simp_rw [weightedWordEndingSummand_snoc]
  rw [weightedWordEnding, ← Finset.mul_sum]

/-- Ordered last-letter recurrence, with the diagonal term retained. -/
theorem weightedWordEnding_succ_split {R : Type*} [CommSemiring R]
    {m : ℕ} (weight : Fin m → R) (n : ℕ) (i : Fin m) :
    weightedWordEnding weight (n + 1) i =
      C (weight i) *
        ((∑ j ∈ Finset.Iio i, weightedWordEnding weight n j) +
          weightedWordEnding weight n i +
          X * ∑ j ∈ Finset.Ioi i, weightedWordEnding weight n j) := by
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
  rw [weightedWordEnding_succ]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [hIio, hIoi]
  rw [show weightedWordEnding weight n i =
      ∑ j : Fin m, if j = i then weightedWordEnding weight n j else 0 by
    simp]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
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

/-- Every nonempty ordinary word belongs to exactly one final-letter
refinement. -/
theorem weightedWordPolynomial_succ {R : Type*} [CommSemiring R] {m : ℕ}
    (weight : Fin m → R) (n : ℕ) :
    weightedWordPolynomial weight (n + 1) =
      ∑ i : Fin m, weightedWordEnding weight n i := by
  classical
  unfold weightedWordPolynomial
  rw [show (∑ word : Fin (n + 1) → Fin m,
      C (wordWeight weight word) *
        X ^ RealRooted.ParkingFunctions.wordDescentNumber word) =
      ∑ i : Fin m, ∑ word : Fin n → Fin m,
        weightedWordEndingSummand weight word i by
    symm
    simpa only [Fintype.sum_prod_type,
      weightedWordEndingSummand] using
      Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin m)
        (fun pair : Fin m × (Fin n → Fin m) =>
          C (wordWeight weight (Fin.snoc pair.2 pair.1)) *
            X ^ RealRooted.ParkingFunctions.wordDescentNumber
              (Fin.snoc pair.2 pair.1))
        (fun word : Fin (n + 1) → Fin m =>
          C (wordWeight weight word) *
            X ^ RealRooted.ParkingFunctions.wordDescentNumber word)
        (fun _ => rfl)]
  apply Fintype.sum_congr
  intro i
  rw [weightedWordEnding]

/-- Formal length-generating series of the literal weighted ordinary-word
polynomials. -/
def weightedWordSeries {R : Type*} [CommRing R] {m : ℕ}
    (weight : Fin m → R) : PowerSeries R[X] :=
  PowerSeries.mk fun n => weightedWordPolynomial weight n

/-- Formal length-generating series for ordinary words ending in `i`. -/
def weightedWordEndingSeries {R : Type*} [CommRing R] {m : ℕ}
    (weight : Fin m → R) (i : Fin m) : PowerSeries R[X] :=
  PowerSeries.X * PowerSeries.mk fun n => weightedWordEnding weight n i

@[simp]
theorem coeff_weightedWordSeries {R : Type*} [CommRing R] {m : ℕ}
    (weight : Fin m → R) (n : ℕ) :
    PowerSeries.coeff n (weightedWordSeries weight) =
      weightedWordPolynomial weight n := by
  simp [weightedWordSeries]

@[simp]
theorem coeff_weightedWordEndingSeries_zero {R : Type*} [CommRing R]
    {m : ℕ} (weight : Fin m → R) (i : Fin m) :
    PowerSeries.coeff 0 (weightedWordEndingSeries weight i) = 0 := by
  simp [weightedWordEndingSeries]

@[simp]
theorem constantCoeff_weightedWordEndingSeries {R : Type*} [CommRing R]
    {m : ℕ} (weight : Fin m → R) (i : Fin m) :
    PowerSeries.constantCoeff (weightedWordEndingSeries weight i) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_weightedWordEndingSeries_zero weight i

@[simp]
theorem coeff_weightedWordEndingSeries_succ {R : Type*} [CommRing R]
    {m : ℕ} (weight : Fin m → R) (i : Fin m) (n : ℕ) :
    PowerSeries.coeff (n + 1) (weightedWordEndingSeries weight i) =
      weightedWordEnding weight n i := by
  simp [weightedWordEndingSeries]

/-- The total ordinary-word series is one plus its final-letter refinements. -/
theorem weightedWordSeries_eq_one_add_sum_ending
    {R : Type*} [CommRing R] {m : ℕ} (weight : Fin m → R) :
    weightedWordSeries weight =
      1 + ∑ i : Fin m, weightedWordEndingSeries weight i := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n => simp [weightedWordPolynomial_succ]

/-- Formal-series form of the ordinary last-letter recurrence. -/
theorem weightedWordEndingSeries_eq_append
    {R : Type*} [CommRing R] {m : ℕ}
    (weight : Fin m → R) (i : Fin m) :
    weightedWordEndingSeries weight i =
      PowerSeries.X *
        (PowerSeries.C (C (weight i)) *
          (1 +
            (∑ j ∈ Finset.Iio i,
              weightedWordEndingSeries weight j) +
            weightedWordEndingSeries weight i +
            PowerSeries.C X *
              ∑ j ∈ Finset.Ioi i,
                weightedWordEndingSeries weight j)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul]
      cases n with
      | zero => simp
      | succ n =>
          simp [weightedWordEnding_succ_split]

/-- After summing repeated equal final letters geometrically, the ordinary
last-letter recurrence has the Smirnov substitution shape. -/
theorem weightedWordEndingSeries_eq_geometric
    {R : Type*} [CommRing R] {m : ℕ}
    (weight : Fin m → R) (i : Fin m) :
    weightedWordEndingSeries weight i =
      ordinaryRunSeries (weight i) *
        (1 +
          (∑ j ∈ Finset.Iio i,
            weightedWordEndingSeries weight j) +
          PowerSeries.C X *
            ∑ j ∈ Finset.Ioi i,
              weightedWordEndingSeries weight j) := by
  let ending := weightedWordEndingSeries weight i
  let marked := PowerSeries.C (C (weight i)) * PowerSeries.X
  let body :=
    1 + (∑ j ∈ Finset.Iio i, weightedWordEndingSeries weight j) +
      PowerSeries.C X *
        ∑ j ∈ Finset.Ioi i, weightedWordEndingSeries weight j
  have happend : ending = marked * (body + ending) := by
    calc
      ending = PowerSeries.X *
          (PowerSeries.C (C (weight i)) *
            (1 +
              (∑ j ∈ Finset.Iio i,
                weightedWordEndingSeries weight j) +
              weightedWordEndingSeries weight i +
              PowerSeries.C X *
                ∑ j ∈ Finset.Ioi i,
                  weightedWordEndingSeries weight j)) :=
        weightedWordEndingSeries_eq_append weight i
      _ = marked * (body + ending) := by
        dsimp only [ending, marked, body]
        ring
  have hrun :
      ordinaryRunSeries (weight i) * (1 - marked) = marked := by
    dsimp only [marked]
    exact ordinaryRunSeries_mul_one_sub (weight i)
  have hregular : IsRegular (1 - marked) := by
    apply PowerSeries.isRegular_of_isRegular_constantCoeff
    simpa [marked] using (isRegular_one : IsRegular (1 : R[X]))
  apply hregular.left
  calc
    (1 - marked) * ending = marked * body := by
      linear_combination happend
    _ = (1 - marked) * (ordinaryRunSeries (weight i) * body) := by
      symm
      calc
        (1 - marked) * (ordinaryRunSeries (weight i) * body) =
            (ordinaryRunSeries (weight i) * (1 - marked)) * body := by
          ring
        _ = marked * body := by rw [hrun]

/-- The literal ordinary-word series satisfies the same finite-product
equation as geometric-run substitution into Smirnov words. -/
theorem weightedWordSeries_product_identity
    {R : Type*} [CommRing R] {m : ℕ} (weight : Fin m → R) :
    (∏ i : Fin m,
        (1 + PowerSeries.C X * ordinaryRunSeries (weight i))) *
        weightedWordSeries weight =
      (∏ i : Fin m, (1 + ordinaryRunSeries (weight i))) *
        (1 - PowerSeries.C X +
          PowerSeries.C X * weightedWordSeries weight) := by
  rw [weightedWordSeries_eq_one_add_sum_ending]
  exact smirnovAbstract_product_identity
    (PowerSeries.C X) (fun i => ordinaryRunSeries (weight i))
    (fun i => weightedWordEndingSeries weight i)
    (weightedWordEndingSeries_eq_geometric weight)

/-- Substitute positive geometric run series into the Smirnov series. -/
def ordinaryWordSeries {R : Type*} [CommRing R] {m : ℕ}
    (weight : Fin m → R) : PowerSeries R[X] :=
  smirnovSubstitutionSeries (A := R[X]) X
    (fun i => ordinaryRunSeries (weight i))

@[simp]
theorem coeff_ordinaryWordSeries_zero {R : Type*} [CommRing R]
    {m : ℕ} (weight : Fin m → R) :
    PowerSeries.coeff 0 (ordinaryWordSeries weight) = 1 := by
  rw [ordinaryWordSeries, coeff_smirnovSubstitutionSeries]
  simp [smirnovSubstitutionFixed_zero]

/-- The substituted series satisfies the generic finite-product identity. -/
theorem ordinaryWordSeries_product_identity {R : Type*} [CommRing R]
    {m : ℕ} (weight : Fin m → R) :
    (∏ i : Fin m,
        (1 + PowerSeries.C X * ordinaryRunSeries (weight i))) *
        ordinaryWordSeries weight =
      (∏ i : Fin m, (1 + ordinaryRunSeries (weight i))) *
        (1 - PowerSeries.C X +
          PowerSeries.C X * ordinaryWordSeries weight) := by
  apply smirnovSubstitutionSeries_product_identity
  intro i
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_ordinaryRunSeries_zero (weight i)

private theorem isRegular_one_sub_X {R : Type*} [CommRing R] :
    IsRegular (1 - X : R[X]) := by
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

/-- Literal ordinary words are exactly geometric-run substitution into
Smirnov skeletons. -/
theorem weightedWordSeries_eq_ordinaryWordSeries
    {R : Type*} [CommRing R] {m : ℕ} (weight : Fin m → R) :
    weightedWordSeries weight = ordinaryWordSeries weight := by
  have hzero : ∀ i,
      PowerSeries.constantCoeff (ordinaryRunSeries (weight i)) = 0 := by
    intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_ordinaryRunSeries_zero (weight i)
  apply eq_smirnovSubstitutionSeries_of_product_identity
    (A := R[X]) X (fun i => ordinaryRunSeries (weight i))
      hzero isRegular_one_sub_X
  exact weightedWordSeries_product_identity weight

/-- Coefficients of geometric-run substitution are literal weighted
ordinary-word descent polynomials. -/
theorem coeff_ordinaryWordSeries {R : Type*} [CommRing R] {m : ℕ}
    (weight : Fin m → R) (n : ℕ) :
    PowerSeries.coeff n (ordinaryWordSeries weight) =
      weightedWordPolynomial weight n := by
  rw [← weightedWordSeries_eq_ordinaryWordSeries,
    coeff_weightedWordSeries]

/-- Permuting the letter weights leaves the ordinary-word series unchanged. -/
theorem ordinaryWordSeries_comp_equiv {R : Type*} [CommRing R]
    {m : ℕ} (weight : Fin m → R) (e : Equiv.Perm (Fin m)) :
    ordinaryWordSeries (weight ∘ e) = ordinaryWordSeries weight := by
  have hzero : ∀ i,
      PowerSeries.constantCoeff (ordinaryRunSeries (weight i)) = 0 := by
    intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_ordinaryRunSeries_zero (weight i)
  simpa [ordinaryWordSeries, Function.comp_def] using
    (smirnovSubstitutionSeries_comp_equiv
      (A := R[X]) X (fun i => ordinaryRunSeries (weight i))
      hzero isRegular_one_sub_X e)

/-- The literal weighted ordinary-word polynomial is invariant under
permuting the alphabet weights. -/
theorem weightedWordPolynomial_comp_equiv
    {R : Type*} [CommRing R] {m : ℕ}
    (weight : Fin m → R) (e : Equiv.Perm (Fin m)) (n : ℕ) :
    weightedWordPolynomial (weight ∘ e) n =
      weightedWordPolynomial weight n := by
  calc
    weightedWordPolynomial (weight ∘ e) n =
        PowerSeries.coeff n (ordinaryWordSeries (weight ∘ e)) := by
      rw [coeff_ordinaryWordSeries]
    _ = PowerSeries.coeff n (ordinaryWordSeries weight) := by
      rw [ordinaryWordSeries_comp_equiv]
    _ = weightedWordPolynomial weight n := coeff_ordinaryWordSeries weight n

/-- Weighted ordinary-word polynomials commute with change of coefficient
ring. -/
theorem map_weightedWordPolynomial
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {m : ℕ} (weight : Fin m → R) (n : ℕ) :
    (weightedWordPolynomial weight n).map φ =
      weightedWordPolynomial (fun i => φ (weight i)) n := by
  classical
  unfold weightedWordPolynomial
  simp only [Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  apply Finset.sum_congr rfl
  intro word _
  congr 2
  exact map_prod φ (fun i => weight (word i)) Finset.univ

end

end RealRooted.BrandenVecchi
