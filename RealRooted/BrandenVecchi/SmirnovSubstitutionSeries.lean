import RealRooted.BrandenVecchi.SignedWordRuns.FiberSum
import RealRooted.BrandenVecchi.SmirnovChow
import RealRooted.Mathlib.RingTheory.PowerSeries.Regular
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Locally finite Smirnov substitution series

This module substitutes positive-order formal series for the letter weights
in the finite weighted Smirnov enumerator.  The total series is defined
coefficientwise: in degree `n`, only skeleton lengths at most `n` occur.
-/

open Polynomial BigOperators
open scoped PowerSeries.WithPiTopology

namespace RealRooted.BrandenVecchi

noncomputable section

variable {A : Type*} [CommRing A]

/-- The contribution of length-`k` Smirnov skeletons after substituting a
formal series for every letter weight and `t` for the descent variable. -/
def smirnovSubstitutionFixed {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (k : ℕ) : PowerSeries A :=
  ∑ word ∈ smirnovWords m k,
    PowerSeries.C (t ^ smirnovDescentNumber word) *
      ∏ i, weight (word i)

@[simp]
theorem smirnovSubstitutionFixed_zero {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) :
    smirnovSubstitutionFixed t weight 0 = 1 := by
  simp [smirnovSubstitutionFixed, smirnovWords, IsSmirnovWord]

/-- Evaluation form of a fixed-length contribution. -/
theorem smirnovSubstitutionFixed_eq_eval {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (k : ℕ) :
    smirnovSubstitutionFixed t weight k =
      Polynomial.eval (PowerSeries.C t)
        (weightedSmirnovPolynomial weight k) := by
  classical
  rw [smirnovSubstitutionFixed, weightedSmirnovPolynomial]
  change _ =
    (Polynomial.evalRingHom (PowerSeries.C t))
      (∑ word ∈ smirnovWords m k,
        C (smirnovWordWeight weight word) *
          X ^ smirnovDescentNumber word)
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro word _
  change PowerSeries.C (t ^ smirnovDescentNumber word) *
      (∏ i, weight (word i)) =
    Polynomial.eval (PowerSeries.C t)
      (C (smirnovWordWeight weight word) *
        X ^ smirnovDescentNumber word)
  rw [eval_C_mul, eval_X_pow, smirnovWordWeight]
  simp only [map_pow]
  ring

/-- The substituted contribution of nonempty skeletons with prescribed last
letter.  The index counts the letters preceding the last letter. -/
def smirnovSubstitutionEndingFixed {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (n : ℕ) (i : Fin m) :
    PowerSeries A :=
  Polynomial.eval (PowerSeries.C t) (weightedSmirnovEnding weight n i)

@[simp]
theorem smirnovSubstitutionEndingFixed_zero {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (i : Fin m) :
    smirnovSubstitutionEndingFixed t weight 0 i = weight i := by
  simp [smirnovSubstitutionEndingFixed]

/-- Ordered last-letter recurrence after formal-series substitution. -/
theorem smirnovSubstitutionEndingFixed_succ {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (n : ℕ) (i : Fin m) :
    smirnovSubstitutionEndingFixed t weight (n + 1) i =
      weight i *
        ((∑ j ∈ Finset.Iio i,
            smirnovSubstitutionEndingFixed t weight n j) +
          PowerSeries.C t * ∑ j ∈ Finset.Ioi i,
            smirnovSubstitutionEndingFixed t weight n j) := by
  rw [smirnovSubstitutionEndingFixed,
    weightedSmirnovEnding_succ_split]
  change (Polynomial.evalRingHom (PowerSeries.C t))
      (C (weight i) *
        ((∑ j ∈ Finset.Iio i, weightedSmirnovEnding weight n j) +
          X * ∑ j ∈ Finset.Ioi i,
            weightedSmirnovEnding weight n j)) = _
  simp only [map_mul, map_add, map_sum]
  simp [smirnovSubstitutionEndingFixed]

/-- Every nonempty fixed-length contribution is the sum of its final-letter
refinements. -/
theorem smirnovSubstitutionFixed_succ {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (n : ℕ) :
    smirnovSubstitutionFixed t weight (n + 1) =
      ∑ i : Fin m, smirnovSubstitutionEndingFixed t weight n i := by
  rw [smirnovSubstitutionFixed_eq_eval,
    weightedSmirnovPolynomial_succ]
  change (Polynomial.evalRingHom (PowerSeries.C t))
      (∑ i : Fin m, weightedSmirnovEnding weight n i) = _
  simp [smirnovSubstitutionEndingFixed]

/-- The coefficientwise locally finite total Smirnov substitution series. -/
def smirnovSubstitutionSeries {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n ↦
    ∑ k ∈ Finset.range (n + 1),
      PowerSeries.coeff n (smirnovSubstitutionFixed t weight k)

@[simp]
theorem coeff_smirnovSubstitutionSeries {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (smirnovSubstitutionSeries t weight) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff n (smirnovSubstitutionFixed t weight k) := by
  simp [smirnovSubstitutionSeries]

/-- A word of length `k` in positive-order series has no coefficient below
degree `k`. -/
theorem coeff_smirnovWordWeight_eq_zero_of_lt {m k : ℕ}
    (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0)
    (word : Fin k → Fin m) {n : ℕ} (hnk : n < k) :
    PowerSeries.coeff n (smirnovWordWeight weight word) = 0 := by
  rw [smirnovWordWeight]
  apply PowerSeries.coeff_of_lt_order
  have hprod : (k : ℕ∞) ≤ (∏ i, weight (word i)).order := by
    calc
      (k : ℕ∞) = ∑ i : Fin k, (1 : ℕ∞) := by simp
      _ ≤ ∑ i : Fin k, (weight (word i)).order := by
        apply Finset.sum_le_sum
        intro i _
        exact PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
          (hweight (word i))
      _ ≤ (∏ i, weight (word i)).order :=
        PowerSeries.le_order_prod _ _
  exact (by exact_mod_cast hnk : (n : ℕ∞) < (k : ℕ∞)).trans_le hprod

/-- A product of `k` positive-order letter series has no coefficient below
degree `k`; hence neither does the length-`k` Smirnov contribution. -/
theorem coeff_smirnovSubstitutionFixed_eq_zero_of_lt {m : ℕ}
    (t : A) (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0)
    {n k : ℕ} (hnk : n < k) :
    PowerSeries.coeff n (smirnovSubstitutionFixed t weight k) = 0 := by
  classical
  rw [smirnovSubstitutionFixed, map_sum]
  apply Finset.sum_eq_zero
  intro word hword
  rw [PowerSeries.coeff_C_mul]
  change _ * PowerSeries.coeff n
      (smirnovWordWeight weight word) = 0
  rw [coeff_smirnovWordWeight_eq_zero_of_lt weight hweight word hnk]
  simp

/-- A last-letter contribution indexed by `k` has word length `k+1`, so its
coefficients below that length vanish. -/
theorem coeff_smirnovSubstitutionEndingFixed_eq_zero_of_lt {m : ℕ}
    (t : A) (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0)
    (i : Fin m) {n k : ℕ} (hnk : n < k + 1) :
    PowerSeries.coeff n
        (smirnovSubstitutionEndingFixed t weight k i) = 0 := by
  classical
  rw [smirnovSubstitutionEndingFixed, weightedSmirnovEnding]
  change PowerSeries.coeff n
      ((Polynomial.evalRingHom (PowerSeries.C t))
        (∑ word : Fin k → Fin m,
          weightedSmirnovEndingSummand weight word i)) = 0
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro word _
  rw [weightedSmirnovEndingSummand]
  by_cases hword : IsSmirnovWord (k + 1) (Fin.snoc word i)
  · rw [if_pos hword]
    change PowerSeries.coeff n
      (Polynomial.eval (PowerSeries.C t)
        (C (smirnovWordWeight weight (Fin.snoc word i)) *
          X ^ smirnovDescentNumber (Fin.snoc word i))) = 0
    rw [eval_C_mul, eval_X_pow]
    rw [← map_pow, PowerSeries.coeff_mul_C]
    rw [coeff_smirnovWordWeight_eq_zero_of_lt weight hweight
      (Fin.snoc word i) hnk]
    simp
  · simp [hword]

/-- The coefficientwise locally finite series of nonempty skeletons ending in
the prescribed letter. -/
def smirnovSubstitutionEndingSeries {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (i : Fin m) : PowerSeries A :=
  PowerSeries.mk fun n ↦
    ∑ k ∈ Finset.range n,
      PowerSeries.coeff n
        (smirnovSubstitutionEndingFixed t weight k i)

@[simp]
theorem coeff_smirnovSubstitutionEndingSeries {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (i : Fin m) (n : ℕ) :
    PowerSeries.coeff n
        (smirnovSubstitutionEndingSeries t weight i) =
      ∑ k ∈ Finset.range n,
        PowerSeries.coeff n
          (smirnovSubstitutionEndingFixed t weight k i) := by
  simp [smirnovSubstitutionEndingSeries]

@[simp]
theorem coeff_smirnovSubstitutionEndingSeries_zero {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A) (i : Fin m) :
    PowerSeries.coeff 0
        (smirnovSubstitutionEndingSeries t weight i) = 0 := by
  simp

/-- The last-letter pieces sum to their coefficientwise locally finite
series. -/
theorem hasSum_smirnovSubstitutionEndingFixed [TopologicalSpace A]
    [DiscreteTopology A] {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0)
    (i : Fin m) :
    HasSum (fun k ↦ smirnovSubstitutionEndingFixed t weight k i)
      (smirnovSubstitutionEndingSeries t weight i) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro n
  simpa using
    (hasSum_sum_of_ne_finset_zero
      (s := Finset.range n)
      (fun k hk ↦
        coeff_smirnovSubstitutionEndingFixed_eq_zero_of_lt
          t weight hweight i
          (Nat.lt_succ_of_le (Nat.le_of_not_gt (by simpa using hk)))))

/-- Topological-sum presentation of a last-letter series in the discrete
coefficient topology. -/
theorem smirnovSubstitutionEndingSeries_eq_tsum [TopologicalSpace A]
    [DiscreteTopology A] {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0)
    (i : Fin m) :
    smirnovSubstitutionEndingSeries t weight i =
      ∑' k, smirnovSubstitutionEndingFixed t weight k i := by
  exact
    (hasSum_smirnovSubstitutionEndingFixed t weight hweight i).tsum_eq.symm

/-- The fixed-length contributions sum to the coefficientwise definition.
The topology used in this proof is discrete on coefficients; the resulting
formal-series equality is purely algebraic. -/
theorem hasSum_smirnovSubstitutionFixed [TopologicalSpace A]
    [DiscreteTopology A] {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0) :
    HasSum (smirnovSubstitutionFixed t weight)
      (smirnovSubstitutionSeries t weight) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro n
  simpa using
    (hasSum_sum_of_ne_finset_zero
      (s := Finset.range (n + 1))
      (fun k hk ↦
        coeff_smirnovSubstitutionFixed_eq_zero_of_lt t weight hweight
          (Nat.le_of_not_gt (by simpa using hk))))

/-- The coefficientwise total series agrees with the topological sum of its
fixed-length pieces in the discrete coefficient topology. -/
theorem smirnovSubstitutionSeries_eq_tsum [TopologicalSpace A]
    [DiscreteTopology A] {m : ℕ} (t : A)
    (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0) :
    smirnovSubstitutionSeries t weight =
      ∑' k, smirnovSubstitutionFixed t weight k := by
  exact (hasSum_smirnovSubstitutionFixed t weight hweight).tsum_eq.symm

/-- The total substituted series is the empty word plus the sum of its
last-letter refinements. -/
theorem smirnovSubstitutionSeries_eq_one_add_sum_ending {m : ℕ}
    (t : A) (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0) :
    smirnovSubstitutionSeries t weight =
      1 + ∑ i : Fin m,
        smirnovSubstitutionEndingSeries t weight i := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  rw [smirnovSubstitutionSeries_eq_tsum t weight hweight]
  have hfixed : Summable (smirnovSubstitutionFixed t weight) :=
    (hasSum_smirnovSubstitutionFixed t weight hweight).summable
  rw [hfixed.tsum_eq_zero_add, smirnovSubstitutionFixed_zero]
  congr 1
  calc
    (∑' n, smirnovSubstitutionFixed t weight (n + 1)) =
        ∑' n, ∑ i : Fin m,
          smirnovSubstitutionEndingFixed t weight n i := by
      apply tsum_congr
      exact smirnovSubstitutionFixed_succ t weight
    _ = ∑ i : Fin m,
          ∑' n, smirnovSubstitutionEndingFixed t weight n i := by
      apply Summable.tsum_finsetSum
      intro i hi
      exact
        (hasSum_smirnovSubstitutionEndingFixed
          t weight hweight i).summable
    _ = ∑ i : Fin m,
          smirnovSubstitutionEndingSeries t weight i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (smirnovSubstitutionEndingSeries_eq_tsum
        t weight hweight i).symm

/-- Formal-series last-letter equation for the locally finite substituted
refinements. -/
theorem smirnovSubstitutionEndingSeries_eq {m : ℕ}
    (t : A) (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0)
    (i : Fin m) :
    smirnovSubstitutionEndingSeries t weight i =
      weight i *
        (1 +
          (∑ j ∈ Finset.Iio i,
            smirnovSubstitutionEndingSeries t weight j) +
          PowerSeries.C t *
            ∑ j ∈ Finset.Ioi i,
              smirnovSubstitutionEndingSeries t weight j) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  have hend (j : Fin m) :
      Summable (fun n ↦
        smirnovSubstitutionEndingFixed t weight n j) :=
    (hasSum_smirnovSubstitutionEndingFixed
      t weight hweight j).summable
  have hsum (s : Finset (Fin m)) :
      Summable (fun n ↦
        ∑ j ∈ s, smirnovSubstitutionEndingFixed t weight n j) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        simpa [Finset.sum_insert hj] using (hend j).add ih
  have hlo := hsum (Finset.Iio i)
  have hhi := hsum (Finset.Ioi i)
  have hhiMul :
      Summable (fun n ↦ PowerSeries.C t *
        ∑ j ∈ Finset.Ioi i,
          smirnovSubstitutionEndingFixed t weight n j) :=
    hhi.mul_left (PowerSeries.C t)
  have hbody : Summable (fun n ↦
      (∑ j ∈ Finset.Iio i,
        smirnovSubstitutionEndingFixed t weight n j) +
      PowerSeries.C t *
        ∑ j ∈ Finset.Ioi i,
          smirnovSubstitutionEndingFixed t weight n j) :=
    hlo.add hhiMul
  rw [smirnovSubstitutionEndingSeries_eq_tsum t weight hweight i]
  rw [(hend i).tsum_eq_zero_add,
    smirnovSubstitutionEndingFixed_zero]
  simp_rw [smirnovSubstitutionEndingFixed_succ]
  rw [hbody.tsum_mul_left]
  rw [hlo.tsum_add hhiMul, hhi.tsum_mul_left]
  rw [Summable.tsum_finsetSum (fun j hj ↦ hend j)]
  rw [Summable.tsum_finsetSum (fun j hj ↦ hend j)]
  simp_rw [← smirnovSubstitutionEndingSeries_eq_tsum
    t weight hweight]
  ring

/-! ## An algebraic finite-alphabet telescope -/

variable {B : Type*} [CommRing B]

/-- The cut expression for an abstract family of last-letter contributions. -/
def smirnovAbstractCut {m : ℕ} (t : B) (ending : Fin m → B)
    (k : ℕ) : B :=
  1 + (∑ i, if i.val < k then ending i else 0) +
    t * ∑ i, if k ≤ i.val then ending i else 0

/-- Product of the rescaled factors below a cut. -/
def smirnovAbstractRescaledProduct {m : ℕ} (t : B)
    (weight : Fin m → B) (k : ℕ) : B :=
  ∏ i, if i.val < k then 1 + t * weight i else 1

/-- Product of the unscaled factors below a cut. -/
def smirnovAbstractProduct {m : ℕ} (weight : Fin m → B)
    (k : ℕ) : B :=
  ∏ i, if i.val < k then 1 + weight i else 1

/-- One abstract last-letter equation moves the cut past its letter. -/
theorem smirnovAbstractCut_factor_step {m k : ℕ}
    (t : B) (weight ending : Fin m → B) (hk : k < m)
    (hending : ∀ i,
      ending i = weight i *
        (1 + (∑ j ∈ Finset.Iio i, ending j) +
          t * ∑ j ∈ Finset.Ioi i, ending j)) :
    (1 + t * weight ⟨k, hk⟩) *
        smirnovAbstractCut t ending (k + 1) =
      (1 + weight ⟨k, hk⟩) *
        smirnovAbstractCut t ending k := by
  let kfin : Fin m := ⟨k, hk⟩
  have hIio :
      (∑ j ∈ Finset.Iio kfin, ending j) =
        ∑ j, if j.val < k then ending j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iio]
    rfl
  have hIoi :
      (∑ j ∈ Finset.Ioi kfin, ending j) =
        ∑ j, if k + 1 ≤ j.val then ending j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ioi]
    exact Nat.lt_iff_add_one_le
  rw [smirnovAbstractCut, smirnovAbstractCut,
    sum_fin_val_lt_succ hk, sum_fin_succ_le_val hk]
  rw [hending kfin, hIio, hIoi]
  ring

/-- The abstract factor identity accumulated up to an arbitrary cut. -/
theorem smirnovAbstract_telescope_aux {m : ℕ}
    (t : B) (weight ending : Fin m → B)
    (hending : ∀ i,
      ending i = weight i *
        (1 + (∑ j ∈ Finset.Iio i, ending j) +
          t * ∑ j ∈ Finset.Ioi i, ending j))
    (k : ℕ) (hk : k ≤ m) :
    smirnovAbstractRescaledProduct t weight k *
        smirnovAbstractCut t ending k =
      smirnovAbstractProduct weight k *
        smirnovAbstractCut t ending 0 := by
  induction k with
  | zero =>
      simp [smirnovAbstractRescaledProduct, smirnovAbstractProduct]
  | succ k ih =>
      have hklt : k < m := Nat.lt_of_succ_le hk
      rw [smirnovAbstractRescaledProduct,
        prod_fin_val_lt_succ hklt,
        smirnovAbstractProduct, prod_fin_val_lt_succ hklt]
      calc
        (smirnovAbstractRescaledProduct t weight k *
              (1 + t * weight ⟨k, hklt⟩)) *
            smirnovAbstractCut t ending (k + 1) =
          smirnovAbstractRescaledProduct t weight k *
            ((1 + t * weight ⟨k, hklt⟩) *
              smirnovAbstractCut t ending (k + 1)) := by ring
        _ = smirnovAbstractRescaledProduct t weight k *
            ((1 + weight ⟨k, hklt⟩) *
              smirnovAbstractCut t ending k) := by
          rw [smirnovAbstractCut_factor_step
            t weight ending hklt hending]
        _ = (1 + weight ⟨k, hklt⟩) *
            (smirnovAbstractRescaledProduct t weight k *
              smirnovAbstractCut t ending k) := by ring
        _ = (1 + weight ⟨k, hklt⟩) *
            (smirnovAbstractProduct weight k *
              smirnovAbstractCut t ending 0) := by
          rw [ih (Nat.le_of_succ_le hk)]
        _ = (smirnovAbstractProduct weight k *
              (1 + weight ⟨k, hklt⟩)) *
            smirnovAbstractCut t ending 0 := by ring

@[simp]
theorem smirnovAbstractCut_zero {m : ℕ} (t : B)
    (ending : Fin m → B) :
    smirnovAbstractCut t ending 0 =
      1 - t + t * (1 + ∑ i, ending i) := by
  simp [smirnovAbstractCut]
  ring

@[simp]
theorem smirnovAbstractCut_card {m : ℕ} (t : B)
    (ending : Fin m → B) :
    smirnovAbstractCut t ending m = 1 + ∑ i, ending i := by
  have hsuffix :
      (∑ i : Fin m, if m ≤ i.val then ending i else 0) = 0 := by
    apply Fintype.sum_eq_zero
    intro i
    simp [Nat.not_le_of_lt i.isLt]
  simp [smirnovAbstractCut, hsuffix]

/-- Finite-alphabet product identity from the abstract last-letter equations. -/
theorem smirnovAbstract_product_identity {m : ℕ}
    (t : B) (weight ending : Fin m → B)
    (hending : ∀ i,
      ending i = weight i *
        (1 + (∑ j ∈ Finset.Iio i, ending j) +
          t * ∑ j ∈ Finset.Ioi i, ending j)) :
    (∏ i : Fin m, (1 + t * weight i)) *
        (1 + ∑ i, ending i) =
      (∏ i : Fin m, (1 + weight i)) *
        (1 - t + t * (1 + ∑ i, ending i)) := by
  simpa [smirnovAbstractRescaledProduct, smirnovAbstractProduct,
    Fin.isLt] using
    smirnovAbstract_telescope_aux t weight ending hending m le_rfl

/-- Locally finite Smirnov substitution satisfies the finite-product
denominator identity. -/
theorem smirnovSubstitutionSeries_product_identity {m : ℕ}
    (t : A) (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0) :
    (∏ i : Fin m, (1 + PowerSeries.C t * weight i)) *
        smirnovSubstitutionSeries t weight =
      (∏ i : Fin m, (1 + weight i)) *
        (1 - PowerSeries.C t +
          PowerSeries.C t * smirnovSubstitutionSeries t weight) := by
  rw [smirnovSubstitutionSeries_eq_one_add_sum_ending
    t weight hweight]
  exact smirnovAbstract_product_identity
    (PowerSeries.C t) weight
    (smirnovSubstitutionEndingSeries t weight)
    (smirnovSubstitutionEndingSeries_eq t weight hweight)

/-- The finite-product equation uniquely determines the locally finite
Smirnov substitution series when its scalar denominator is regular. -/
theorem eq_smirnovSubstitutionSeries_of_product_identity {m : ℕ}
    (t : A) (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0)
    (ht : IsRegular (1 - t)) (series : PowerSeries A)
    (hseries :
      (∏ i : Fin m, (1 + PowerSeries.C t * weight i)) * series =
        (∏ i : Fin m, (1 + weight i)) *
          (1 - PowerSeries.C t + PowerSeries.C t * series)) :
    series = smirnovSubstitutionSeries t weight := by
  let rescaledProduct :=
    ∏ i : Fin m, (1 + PowerSeries.C t * weight i)
  let product := ∏ i : Fin m, (1 + weight i)
  let denominator := rescaledProduct - product * PowerSeries.C t
  have hseriesDenominator :
      denominator * series = product * (1 - PowerSeries.C t) := by
    dsimp only [denominator, rescaledProduct, product]
    linear_combination hseries
  have htarget :=
    smirnovSubstitutionSeries_product_identity t weight hweight
  have htargetDenominator :
      denominator * smirnovSubstitutionSeries t weight =
        product * (1 - PowerSeries.C t) := by
    dsimp only [denominator, rescaledProduct, product]
    linear_combination htarget
  have hconstant : PowerSeries.constantCoeff denominator = 1 - t := by
    simp [denominator, rescaledProduct, product, hweight]
  apply (PowerSeries.isRegular_of_isRegular_constantCoeff
    (hconstant ▸ ht)).left
  exact hseriesDenominator.trans htargetDenominator.symm

/-- Permuting the alphabet weights leaves the substituted Smirnov series
unchanged when the scalar denominator is regular. -/
theorem smirnovSubstitutionSeries_comp_equiv {m : ℕ}
    (t : A) (weight : Fin m → PowerSeries A)
    (hweight : ∀ i, PowerSeries.constantCoeff (weight i) = 0)
    (ht : IsRegular (1 - t)) (e : Equiv.Perm (Fin m)) :
    smirnovSubstitutionSeries t (weight ∘ e) =
      smirnovSubstitutionSeries t weight := by
  let rescaledProduct :=
    ∏ i : Fin m, (1 + PowerSeries.C t * weight i)
  let product := ∏ i : Fin m, (1 + weight i)
  let denominator := rescaledProduct - product * PowerSeries.C t
  have hrescaled :
      (∏ i : Fin m,
          (1 + PowerSeries.C t * (weight ∘ e) i)) =
        rescaledProduct := by
    exact Fintype.prod_equiv e
      (fun i => 1 + PowerSeries.C t * (weight ∘ e) i)
      (fun i => 1 + PowerSeries.C t * weight i) (fun _ => rfl)
  have hproduct :
      (∏ i : Fin m, (1 + (weight ∘ e) i)) = product := by
    exact Fintype.prod_equiv e
      (fun i => 1 + (weight ∘ e) i)
      (fun i => 1 + weight i) (fun _ => rfl)
  have hpermuted := smirnovSubstitutionSeries_product_identity
    t (weight ∘ e) (fun i => hweight (e i))
  rw [hrescaled, hproduct] at hpermuted
  have horiginal :=
    smirnovSubstitutionSeries_product_identity t weight hweight
  have hpermutedDenominator :
      denominator * smirnovSubstitutionSeries t (weight ∘ e) =
        product * (1 - PowerSeries.C t) := by
    dsimp only [denominator]
    linear_combination hpermuted
  have horiginalDenominator :
      denominator * smirnovSubstitutionSeries t weight =
        product * (1 - PowerSeries.C t) := by
    dsimp only [denominator]
    linear_combination horiginal
  have hconstant : PowerSeries.constantCoeff denominator = 1 - t := by
    simp [denominator, rescaledProduct, product, hweight]
  apply (PowerSeries.isRegular_of_isRegular_constantCoeff
    (hconstant ▸ ht)).left
  exact hpermutedDenominator.trans horiginalDenominator.symm

/-! ## Signed-run specialization -/

/-- The finite-function Smirnov condition is the list-chain condition used by
the signed-run decomposition. -/
theorem isSmirnovWord_iff_listIsChain {m k : ℕ}
    (word : Fin k → Fin m) :
    IsSmirnovWord k word ↔
      (List.ofFn word).IsChain (· ≠ ·) := by
  cases k with
  | zero => simp [IsSmirnovWord]
  | succ k =>
      rw [List.isChain_ofFn]
      constructor
      · intro h n hn
        let i : Fin k := ⟨n, Nat.lt_of_succ_lt_succ hn⟩
        simpa [i] using h i
      · intro h i
        have hi := h i.val (Nat.succ_lt_succ i.isLt)
        convert hi using 1
        · exact congrArg word (Fin.ext rfl)
        · exact congrArg word (Fin.ext rfl)

/-- The two literal finite sets of Smirnov skeletons agree. -/
theorem smirnovWords_eq_signedSmirnovWords (q p k : ℕ) :
    smirnovWords (q + p) k = signedSmirnovWords q p k := by
  ext word
  simp [isSmirnovWord_iff_listIsChain]

/-- The tuple and list descent statistics agree on a Smirnov skeleton. -/
theorem smirnovDescentNumber_eq_listDescentNumber {q p k : ℕ}
    (word : Fin k → SignedLetter q p) :
    smirnovDescentNumber word =
      listDescentNumber (List.ofFn word) := by
  cases k with
  | zero => simp [listDescentNumber]
  | succ k =>
      change RealRooted.ParkingFunctions.descentNumber word = _
      simpa [signedDescentNumber] using
        (listDescentNumber_ofFn word).symm

/-- One fixed skeleton length specializes exactly to the signed-run summand. -/
theorem coeff_smirnovSubstitutionFixed_signedRunSeries
    {R : Type*} [CommRing R] {q p : ℕ}
    (weight : SignedLetter q p → R) (n k : ℕ) :
    PowerSeries.coeff n
        (smirnovSubstitutionFixed (A := R[X]) X
          (signedRunSeries weight) k) =
      ∑ skeleton ∈ signedSmirnovWords q p k,
        X ^ listDescentNumber (List.ofFn skeleton) *
          PowerSeries.coeff n
            (signedTupleSkeletonRunSeries weight skeleton) := by
  classical
  rw [smirnovSubstitutionFixed, map_sum,
    smirnovWords_eq_signedSmirnovWords]
  apply Finset.sum_congr rfl
  intro skeleton hskeleton
  rw [PowerSeries.coeff_C_mul]
  simp [smirnovDescentNumber_eq_listDescentNumber,
    signedTupleSkeletonRunSeries]

/-- The locally finite substitution coefficient is exactly the coefficient
defined by the signed-word run decomposition. -/
theorem coeff_smirnovSubstitutionSeries_signedRunSeries
    {R : Type*} [CommRing R] {q p : ℕ}
    (weight : SignedLetter q p → R) (n : ℕ) :
    PowerSeries.coeff n
        (smirnovSubstitutionSeries (A := R[X]) X
          (signedRunSeries weight)) =
      signedSmirnovSubstitutionCoeff weight n := by
  rw [coeff_smirnovSubstitutionSeries,
    signedSmirnovSubstitutionCoeff]
  apply Finset.sum_congr rfl
  intro k hk
  exact coeff_smirnovSubstitutionFixed_signedRunSeries weight n k

/-- Product identity after substituting the signed positive/negative run
factors. -/
theorem signedRunSeries_smirnov_product_identity
    {R : Type*} [CommRing R] {q p : ℕ}
    (weight : SignedLetter q p → R) :
    (∏ i : SignedLetter q p,
        (1 + PowerSeries.C X * signedRunSeries weight i)) *
        smirnovSubstitutionSeries (A := R[X]) X
          (signedRunSeries weight) =
      (∏ i : SignedLetter q p,
        (1 + signedRunSeries weight i)) *
        (1 - PowerSeries.C X +
          PowerSeries.C X *
            smirnovSubstitutionSeries (A := R[X]) X
              (signedRunSeries weight)) := by
  apply smirnovSubstitutionSeries_product_identity
  intro i
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_signedRunSeries_zero weight i

/-! ## Degenerate alphabets and weights -/

@[simp]
theorem smirnovSubstitutionFixed_empty_succ (t : A) (n : ℕ) :
    smirnovSubstitutionFixed t (fun i : Fin 0 => Fin.elim0 i)
      (n + 1) = 0 := by
  rw [smirnovSubstitutionFixed_eq_eval,
    weightedSmirnovPolynomial_empty_succ]
  simp

@[simp]
theorem smirnovSubstitutionSeries_empty (t : A) :
    smirnovSubstitutionSeries t
      (fun i : Fin 0 => Fin.elim0 i) = 1 := by
  rw [smirnovSubstitutionSeries_eq_one_add_sum_ending]
  · simp
  · exact fun i ↦ Fin.elim0 i

@[simp]
theorem smirnovSubstitutionFixed_zeroWeights {m : ℕ}
    (t : A) (n : ℕ) :
    smirnovSubstitutionFixed t
      (fun _ : Fin m => (0 : PowerSeries A)) (n + 1) = 0 := by
  rw [smirnovSubstitutionFixed_eq_eval,
    weightedSmirnovPolynomial_zeroWeights]
  simp

@[simp]
theorem smirnovSubstitutionSeries_zeroWeights {m : ℕ} (t : A) :
    smirnovSubstitutionSeries t
      (fun _ : Fin m => (0 : PowerSeries A)) = 1 := by
  have hweight : ∀ i : Fin m,
      PowerSeries.constantCoeff (0 : PowerSeries A) = 0 := by simp
  rw [smirnovSubstitutionSeries_eq_one_add_sum_ending
    t (fun _ : Fin m => (0 : PowerSeries A)) hweight]
  have hending : ∀ i : Fin m,
      smirnovSubstitutionEndingSeries t
          (fun _ : Fin m => (0 : PowerSeries A)) i = 0 := by
    intro i
    rw [smirnovSubstitutionEndingSeries_eq t _ hweight i]
    simp
  simp [hending]

end

end RealRooted.BrandenVecchi
