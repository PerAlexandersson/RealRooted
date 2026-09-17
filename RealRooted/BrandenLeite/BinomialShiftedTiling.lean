import RealRooted.BrandenLeite.ShiftedTiling

/-!
# Binomial shifted tiling rows

This file specializes the shifted two-seed recurrence to
`A(z) = (1 + z)^(m - 2)`, `B(z) = (1 + z)^m`, and
`γ = Nat.choose m 2`.
-/

open Polynomial

namespace RealRooted.BrandenLeite

noncomputable section

/-- A repeated unit optional-rise product is the corresponding binomial
polynomial. -/
theorem optionalRisePolynomial_replicate_one (m : ℕ) :
    optionalRisePolynomial 1 (List.replicate m 1) = (1 + X) ^ m := by
  simp [optionalRisePolynomial]

@[simp]
theorem coeff_optionalRisePolynomial_replicate_one (m j : ℕ) :
    (optionalRisePolynomial 1 (List.replicate m 1)).coeff j =
      (Nat.choose m j : ℝ) := by
  rw [optionalRisePolynomial_replicate_one,
    Polynomial.coeff_one_add_X_pow]

/-- A repeated unit rational background is a power of the geometric series. -/
theorem rationalBackgroundSeries_replicate_one (m : ℕ) :
    rationalBackgroundSeries (List.replicate m 1) =
      (PowerSeries.mk 1 : PowerSeries ℝ) ^ m := by
  simp [rationalBackgroundSeries,
    BrandenVecchi.finiteSupersymmetricSeries,
    BrandenVecchi.supersymmetricDenominatorFactor]

@[simp]
theorem coeff_rationalBackgroundSeries_replicate_one_succ (m n : ℕ) :
    PowerSeries.coeff n
        (rationalBackgroundSeries (List.replicate (m + 1) 1)) =
      (Nat.choose (m + n) m : ℝ) := by
  rw [rationalBackgroundSeries_replicate_one,
    PowerSeries.mk_one_pow_eq_mk_choose_add]
  simp

/-- The binomial incidence identity underlying the shifted constant term. -/
theorem choose_two_mul_choose_sub_two {m j : ℕ} (hj : 2 ≤ j) :
    Nat.choose m 2 * Nat.choose (m - 2) (j - 2) =
      Nat.choose j 2 * Nat.choose m j := by
  simpa [Nat.mul_comm] using
    (Nat.choose_mul (n := m) (k := j) (s := 2) hj).symm

/-- The lag-`j` coefficient in the binomial shifted recurrence. -/
def binomialShiftedRecurrenceCoefficient (m j : ℕ) : ℝ[X] :=
  twoSeedRecurrenceCoefficient
    (if 2 ≤ j then (Nat.choose (m - 2) (j - 2) : ℝ) else 0)
    (Nat.choose m j : ℝ) (Nat.choose m 2 : ℝ) j

/-- For lag at least two, the shifted coefficient has the displayed binomial
form from the two-seed construction. -/
theorem binomialShiftedRecurrenceCoefficient_eq
    {m j : ℕ} (hj : 2 ≤ j) :
    binomialShiftedRecurrenceCoefficient m j =
      C (Nat.choose (m - 2) (j - 2) : ℝ) * X +
        C (((Nat.choose j 2 : ℝ) - (-1 : ℝ) ^ j) *
          (Nat.choose m j : ℝ)) := by
  rw [binomialShiftedRecurrenceCoefficient,
    twoSeedRecurrenceCoefficient_eq, if_pos hj]
  have hchoose :
      (Nat.choose m 2 : ℝ) * (Nat.choose (m - 2) (j - 2) : ℝ) =
        (Nat.choose j 2 : ℝ) * (Nat.choose m j : ℝ) := by
    exact_mod_cast choose_two_mul_choose_sub_two hj
  rw [hchoose]
  ring

/-- The first lag is the constant coefficient `Nat.choose m 1`. -/
@[simp]
theorem binomialShiftedRecurrenceCoefficient_one (m : ℕ) :
    binomialShiftedRecurrenceCoefficient m 1 = C (Nat.choose m 1 : ℝ) := by
  simp [binomialShiftedRecurrenceCoefficient,
    twoSeedRecurrenceCoefficient]

/-- Every positive-lag binomial recurrence coefficient is coefficientwise
nonnegative. -/
theorem binomialShiftedRecurrenceCoefficient_hasNonnegCoeffs
    (m : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    HasNonnegCoeffs (binomialShiftedRecurrenceCoefficient m j) := by
  by_cases hj2 : 2 ≤ j
  · rw [binomialShiftedRecurrenceCoefficient_eq hj2]
    apply hasNonnegCoeffs_affine_linear (by positivity)
    rcases Nat.even_or_odd j with heven | hodd
    · rw [heven.neg_one_pow]
      have hchoose : 1 ≤ Nat.choose j 2 :=
        Nat.one_le_iff_ne_zero.mpr
          (Nat.choose_ne_zero_iff.mpr (by exact hj2))
      apply mul_nonneg
      · have hchooseR : (1 : ℝ) ≤ Nat.choose j 2 := by
          exact_mod_cast hchoose
        linarith
      · positivity
    · rw [hodd.neg_one_pow]
      apply mul_nonneg
      · have hchooseR : 0 ≤ (Nat.choose j 2 : ℝ) := by positivity
        linarith
      · positivity
  · have hj1 : j = 1 := by lia
    subst j
    rw [binomialShiftedRecurrenceCoefficient_one]
    exact hasNonnegCoeffs_C (by positivity)

/-- The binomial two-seed row after translation by `Nat.choose m 2`. -/
def binomialShiftedRodRow (m n : ℕ) : ℝ[X] :=
  shiftedRationalRodRow (List.replicate m 1) 1 2
    (List.replicate (m - 2) 1) (Nat.choose m 2 : ℝ) n

/-- Binomial shifted rows are PF and consecutive rows are in zero-aware
proper position. -/
theorem binomialShiftedRodRows_pf_and_prec0 (m : ℕ) :
    (∀ n, IsPFPolynomial (binomialShiftedRodRow m n)) ∧
      ∀ n, Interl (binomialShiftedRodRow m n)
        (binomialShiftedRodRow m (n + 1)) := by
  simpa [binomialShiftedRodRow] using
    (shiftedRationalRodRows_pf_and_prec0
      (ys := List.replicate m 1) (xs := List.replicate (m - 2) 1)
      (by simp) (by norm_num) (by norm_num) (by simp)
      (show 0 ≤ (Nat.choose m 2 : ℝ) by positivity))

/-- Exact guarded finite-sum recurrence for every binomial shifted row. -/
theorem binomialShiftedRodRow_recurrence (m n : ℕ) :
    binomialShiftedRodRow m n =
      C (if n = 0 then 1 else 0) +
        ∑ j ∈ Finset.range n,
          binomialShiftedRecurrenceCoefficient m (j + 1) *
            binomialShiftedRodRow m (n - (j + 1)) := by
  simpa [binomialShiftedRodRow,
    binomialShiftedRecurrenceCoefficient] using
    shiftedRationalRodRow_two_seed_recurrence
      (List.replicate m 1) 1 (List.replicate (m - 2) 1)
        (Nat.choose m 2 : ℝ) n

/-- Every root of a binomial shifted row lies strictly below the translation
threshold. -/
theorem binomialShiftedRodRow_roots_lt_neg
    {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    ∀ x ∈ (binomialShiftedRodRow m n).roots,
      x < -(Nat.choose m 2 : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  apply shiftedRationalRodRow_roots_lt_neg
      (ys := List.replicate (2 + d) 1)
      (xs := List.replicate (2 + d - 2) 1)
      (by simp) (by norm_num) (by norm_num) (by simp)
  rw [show 2 + d = (d + 1) + 1 by lia,
    coeff_rationalBackgroundSeries_replicate_one_succ]
  exact_mod_cast (Nat.choose_pos (by lia : d + 1 ≤ d + 1 + n)).ne'

/-- Explicit positive-lag inventory for the cubic binomial client. -/
theorem binomialShiftedRecurrenceCoefficient_three
    {j : ℕ} (hjpos : 1 ≤ j) :
    binomialShiftedRecurrenceCoefficient 3 j =
      if j = 1 then C 3 else if j = 2 then X else
        if j = 3 then X + C 4 else 0 := by
  by_cases hj : j ≤ 3
  · interval_cases j <;>
      norm_num [binomialShiftedRecurrenceCoefficient,
        twoSeedRecurrenceCoefficient, Nat.choose,
        Polynomial.C_ofNat] <;> ring
  · have hj4 : 4 ≤ j := by lia
    have hB : Nat.choose 3 j = 0 := Nat.choose_eq_zero_of_lt (by lia)
    have hA : Nat.choose (3 - 2) (j - 2) = 0 :=
      Nat.choose_eq_zero_of_lt (by norm_num; lia)
    simp [binomialShiftedRecurrenceCoefficient,
      twoSeedRecurrenceCoefficient, hB, hA, (show 2 ≤ j by lia),
      (show j ≠ 3 by lia), (show j ≠ 2 by lia),
      (show j ≠ 1 by lia)]

/-- Explicit positive-lag inventory for the quartic binomial client. -/
theorem binomialShiftedRecurrenceCoefficient_four
    {j : ℕ} (hjpos : 1 ≤ j) :
    binomialShiftedRecurrenceCoefficient 4 j =
      if j = 1 then C 4 else if j = 2 then X else
        if j = 3 then C 2 * X + C 16 else
          if j = 4 then X + C 5 else 0 := by
  by_cases hj : j ≤ 4
  · interval_cases j <;>
      norm_num [binomialShiftedRecurrenceCoefficient,
        twoSeedRecurrenceCoefficient, Nat.choose,
        Polynomial.C_ofNat] <;> ring
  · have hj5 : 5 ≤ j := by lia
    have hB : Nat.choose 4 j = 0 := Nat.choose_eq_zero_of_lt (by lia)
    have hA : Nat.choose (4 - 2) (j - 2) = 0 :=
      Nat.choose_eq_zero_of_lt (by norm_num; lia)
    simp [binomialShiftedRecurrenceCoefficient,
      twoSeedRecurrenceCoefficient, hB, hA, (show 2 ≤ j by lia),
      (show j ≠ 4 by lia), (show j ≠ 3 by lia),
      (show j ≠ 2 by lia), (show j ≠ 1 by lia)]

/-- The displayed cubic recurrence from the binomial two-seed construction. -/
theorem binomialShiftedRodRow_three_add_three (n : ℕ) :
    binomialShiftedRodRow 3 (n + 3) =
      C 3 * binomialShiftedRodRow 3 (n + 2) +
        X * binomialShiftedRodRow 3 (n + 1) +
          (X + C 4) * binomialShiftedRodRow 3 n := by
  have h := binomialShiftedRodRow_recurrence 3 (n + 3)
  have hcoeff (j : ℕ) :
      binomialShiftedRecurrenceCoefficient 3 (j + 1) =
        if j = 0 then C 3 else if j = 1 then X else
          if j = 2 then X + C 4 else 0 := by
    simpa using
      (binomialShiftedRecurrenceCoefficient_three
        (j := j + 1) (by lia))
  simp_rw [hcoeff] at h
  have hsum :
      ∑ j ∈ Finset.range (n + 3),
          (if j = 0 then C 3 else if j = 1 then X else
            if j = 2 then X + C 4 else 0) *
            binomialShiftedRodRow 3 (n + 3 - (j + 1)) =
        C 3 * binomialShiftedRodRow 3 (n + 2) +
          X * binomialShiftedRodRow 3 (n + 1) +
            (X + C 4) * binomialShiftedRodRow 3 n := by
    have hsplit (j : ℕ) :
        (if j = 0 then C 3 else if j = 1 then X else
          if j = 2 then X + C 4 else 0) *
            binomialShiftedRodRow 3 (n + 3 - (j + 1)) =
          (if j = 0 then
            C 3 * binomialShiftedRodRow 3 (n + 3 - (j + 1)) else 0) +
          (if j = 1 then
            X * binomialShiftedRodRow 3 (n + 3 - (j + 1)) else 0) +
          (if j = 2 then
            (X + C 4) * binomialShiftedRodRow 3
              (n + 3 - (j + 1)) else 0) := by
      by_cases h0 : j = 0
      · simp [h0]
      · by_cases h1 : j = 1
        · simp [h0, h1]
        · by_cases h2 : j = 2 <;> simp [h0, h1, h2]
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp [show 0 < n + 3 by lia, show 1 < n + 3 by lia,
      show 2 < n + 3 by lia]
  rw [hsum] at h
  simpa [show n + 3 ≠ 0 by lia] using h

/-- The displayed quartic recurrence from the binomial two-seed
construction. -/
theorem binomialShiftedRodRow_four_add_four (n : ℕ) :
    binomialShiftedRodRow 4 (n + 4) =
      C 4 * binomialShiftedRodRow 4 (n + 3) +
        X * binomialShiftedRodRow 4 (n + 2) +
          (C 2 * X + C 16) * binomialShiftedRodRow 4 (n + 1) +
            (X + C 5) * binomialShiftedRodRow 4 n := by
  have h := binomialShiftedRodRow_recurrence 4 (n + 4)
  have hcoeff (j : ℕ) :
      binomialShiftedRecurrenceCoefficient 4 (j + 1) =
        if j = 0 then C 4 else if j = 1 then X else
          if j = 2 then C 2 * X + C 16 else
            if j = 3 then X + C 5 else 0 := by
    simpa using
      (binomialShiftedRecurrenceCoefficient_four
        (j := j + 1) (by lia))
  simp_rw [hcoeff] at h
  have hsum :
      ∑ j ∈ Finset.range (n + 4),
          (if j = 0 then C 4 else if j = 1 then X else
            if j = 2 then C 2 * X + C 16 else
              if j = 3 then X + C 5 else 0) *
            binomialShiftedRodRow 4 (n + 4 - (j + 1)) =
        C 4 * binomialShiftedRodRow 4 (n + 3) +
          X * binomialShiftedRodRow 4 (n + 2) +
            (C 2 * X + C 16) * binomialShiftedRodRow 4 (n + 1) +
              (X + C 5) * binomialShiftedRodRow 4 n := by
    have hsplit (j : ℕ) :
        (if j = 0 then C 4 else if j = 1 then X else
          if j = 2 then C 2 * X + C 16 else
            if j = 3 then X + C 5 else 0) *
            binomialShiftedRodRow 4 (n + 4 - (j + 1)) =
          (if j = 0 then
            C 4 * binomialShiftedRodRow 4 (n + 4 - (j + 1)) else 0) +
          (if j = 1 then
            X * binomialShiftedRodRow 4 (n + 4 - (j + 1)) else 0) +
          (if j = 2 then
            (C 2 * X + C 16) * binomialShiftedRodRow 4
              (n + 4 - (j + 1)) else 0) +
          (if j = 3 then
            (X + C 5) * binomialShiftedRodRow 4
              (n + 4 - (j + 1)) else 0) := by
      by_cases h0 : j = 0
      · simp [h0]
      · by_cases h1 : j = 1
        · simp [h1]
        · by_cases h2 : j = 2
          · simp [h0, h1, h2]
          · by_cases h3 : j = 3 <;> simp [h0, h1, h2, h3]
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq',
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp [show 0 < n + 4 by lia, show 1 < n + 4 by lia,
      show 2 < n + 4 by lia, show 3 < n + 4 by lia]
  rw [hsum] at h
  simpa [show n + 4 ≠ 0 by lia] using h

end

end RealRooted.BrandenLeite
