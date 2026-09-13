import RealRooted.BrandenLeite.StationaryTiling
import RealRooted.InterlacingSequence.NonnegativeShift

/-!
# Positive translations of stationary tiling rows

This file transports the stationary rational rod rows through the common
substitution `X ↦ X + γ`.  It keeps the affine root and proper-position layer
separate from the later coefficient-sign arithmetic for two seed polynomials.
-/

open Polynomial

namespace RealRooted.BrandenLeite

noncomputable section

/-- A stationary rational rod row after the translation `X ↦ X + γ`. -/
def shiftedRationalRodRow (ys : List ℝ) (c : ℝ) (r : ℕ)
    (xs : List ℝ) (γ : ℝ) (n : ℕ) : ℝ[X] :=
  (rationalRodRow ys c r xs n).comp (X + C γ)

/-- The signed rational denominator is the positive seed polynomial evaluated
at `-X`, viewed as a formal power series. -/
theorem rationalBackgroundDenominator_eq_comp_neg_X (ys : List ℝ) :
    rationalBackgroundDenominator ys =
      (((optionalRisePolynomial 1 ys).comp (-X) : ℝ[X]) : PowerSeries ℝ) := by
  induction ys with
  | nil => simp [rationalBackgroundDenominator, optionalRisePolynomial]
  | cons y ys ih =>
      have hopt : optionalRisePolynomial 1 (y :: ys) =
          (1 + C y * X) * optionalRisePolynomial 1 ys := by
        simp [optionalRisePolynomial]
      rw [show rationalBackgroundDenominator (y :: ys) =
          (1 - PowerSeries.C y * PowerSeries.X) *
            rationalBackgroundDenominator ys by
          simp [rationalBackgroundDenominator]]
      rw [hopt, mul_comp, ih]
      rw [Polynomial.coe_mul]
      congr 1
      simp
      ring

/-- Denominator coefficients are the alternating coefficients of the positive
seed polynomial. -/
theorem coeff_rationalBackgroundDenominator (ys : List ℝ) (n : ℕ) :
    PowerSeries.coeff n (rationalBackgroundDenominator ys) =
      (-1 : ℝ) ^ n * (optionalRisePolynomial 1 ys).coeff n := by
  rw [rationalBackgroundDenominator_eq_comp_neg_X, Polynomial.coeff_coe]
  have h := Polynomial.comp_C_mul_X_coeff
    (p := optionalRisePolynomial 1 ys) (r := (-1 : ℝ)) (n := n)
  have hneg : (C (-1 : ℝ) * X : ℝ[X]) = -X := by
    rw [show C (-1 : ℝ) = (-1 : ℝ[X]) by norm_num, neg_one_mul]
  simpa [hneg, mul_comm] using h

/-- The affine coefficient contributed at lag `j` by positive seed
coefficients `a,b` after translation by `γ`. -/
def twoSeedRecurrenceCoefficient (a b γ : ℝ) (j : ℕ) : ℝ[X] :=
  C a * (X + C γ) - C ((-1 : ℝ) ^ j * b)

theorem twoSeedRecurrenceCoefficient_eq (a b γ : ℝ) (j : ℕ) :
    twoSeedRecurrenceCoefficient a b γ j =
      C a * X + C (γ * a - (-1 : ℝ) ^ j * b) := by
  simp [twoSeedRecurrenceCoefficient]
  ring

/-- The even-lag lower bound is exactly what makes every affine recurrence
coefficient nonnegative; odd lags are automatically nonnegative. -/
theorem twoSeedRecurrenceCoefficient_hasNonnegCoeffs
    {a b γ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ) (j : ℕ)
    (heven : Even j → b ≤ γ * a) :
    HasNonnegCoeffs (twoSeedRecurrenceCoefficient a b γ j) := by
  rw [twoSeedRecurrenceCoefficient_eq]
  apply hasNonnegCoeffs_affine_linear ha
  rcases Nat.even_or_odd j with hj | hj
  · rw [hj.neg_one_pow]
    linarith [heven hj]
  · rw [hj.neg_one_pow]
    nlinarith [mul_nonneg hγ ha]

/-- Nonnegative translation preserves PF rows and consecutive zero-aware
proper position. -/
theorem shiftedRationalRodRows_pf_and_prec0
    {ys xs : List ℝ} (hys : ∀ y ∈ ys, 0 ≤ y)
    {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : r ≠ 0)
    (hxs : ∀ x ∈ xs, 0 ≤ x) {γ : ℝ} (hγ : 0 ≤ γ) :
    (∀ n, IsPFPolynomial (shiftedRationalRodRow ys c r xs γ n)) ∧
      ∀ n, Prec0 (shiftedRationalRodRow ys c r xs γ n)
        (shiftedRationalRodRow ys c r xs γ (n + 1)) := by
  obtain ⟨hpf, hprec⟩ := rationalRodRows_pf_and_prec0 hys hc hr hxs
  constructor
  · intro n
    simpa [shiftedRationalRodRow] using
      (hpf n).comp_C_mul_X_add_C (a := 1) (d := γ) zero_lt_one hγ
  · intro n
    exact (prec0_comp_X_add_C_iff γ).2 (hprec n)

/-- The translated one-monomer specialization. -/
def shiftedMonomerRodRow (b c : ℝ) (r : ℕ) (xs : List ℝ)
    (γ : ℝ) (n : ℕ) : ℝ[X] :=
  (monomerRodRow b c r xs n).comp (X + C γ)

/-- Positive monomer weight moves every root strictly to the left of `-γ`. -/
theorem shiftedMonomerRodRow_roots_lt_neg
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) {r : ℕ} (hr : r ≠ 0)
    {xs : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x) (γ : ℝ) (n : ℕ) :
    ∀ x ∈ (shiftedMonomerRodRow b c r xs γ n).roots, x < -γ := by
  intro x hx
  rw [shiftedMonomerRodRow, roots_comp_X_add_C] at hx
  rcases Multiset.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hyneg := monomerRodRow_roots_neg hb hc hr hxs n y hy
  linarith

/-- A nonzero background coefficient gives the strict translated root bound
for an arbitrary finite rational background. -/
theorem shiftedRationalRodRow_roots_lt_neg
    {ys xs : List ℝ} (hys : ∀ y ∈ ys, 0 ≤ y)
    {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : r ≠ 0)
    (hxs : ∀ x ∈ xs, 0 ≤ x) (γ : ℝ) (n : ℕ)
    (hbackground : PowerSeries.coeff n (rationalBackgroundSeries ys) ≠ 0) :
    ∀ x ∈ (shiftedRationalRodRow ys c r xs γ n).roots, x < -γ := by
  intro x hx
  rw [shiftedRationalRodRow, roots_comp_X_add_C] at hx
  rcases Multiset.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hpf := (rationalRodRows_pf_and_prec0 hys hc hr hxs).1 n
  have hcoeff : (rationalRodRow ys c r xs n).coeff 0 ≠ 0 := by
    rw [coeff_zero_rationalRodRow ys c hr xs n]
    exact hbackground
  have hyneg := hpf.roots_neg_of_coeff_zero_ne hcoeff y hy
  linarith

/-- Translation of the exact causal rational-denominator recurrence. -/
theorem shiftedRationalRodRow_eq_sub_sum
    (ys : List ℝ) (c : ℝ) {r : ℕ} (hr : r ≠ 0)
    (xs : List ℝ) (γ : ℝ) (n : ℕ) :
    shiftedRationalRodRow ys c r xs γ n =
      C (if n = 0 then 1 else 0) -
        ∑ j ∈ Finset.range n,
          (C (PowerSeries.coeff (j + 1)
                (rationalBackgroundDenominator ys)) -
              C (PowerSeries.coeff (j + 1)
                (markedFactorSeries c r xs)) * (X + C γ)) *
            shiftedRationalRodRow ys c r xs γ (n - (j + 1)) := by
  have h := congrArg (fun p : ℝ[X] => p.comp (X + C γ))
    (rationalRodRow_eq_sub_sum ys c hr xs n)
  by_cases hn : n = 0
  · simpa [hn, shiftedRationalRodRow, rationalRodDenominatorSeries,
      coeff_polynomialLift, PowerSeries.coeff_C_mul] using h
  · simpa [hn, shiftedRationalRodRow, rationalRodDenominatorSeries,
      coeff_polynomialLift, PowerSeries.coeff_C_mul] using h

/-- The exact two-seed recurrence before reversing the outer subtraction. -/
theorem shiftedRationalRodRow_two_seed_eq_sub_sum
    (ys : List ℝ) (c : ℝ) (xs : List ℝ) (γ : ℝ) (n : ℕ) :
    shiftedRationalRodRow ys c 2 xs γ n =
      C (if n = 0 then 1 else 0) -
        ∑ j ∈ Finset.range n,
          (C ((-1 : ℝ) ^ (j + 1) *
                (optionalRisePolynomial 1 ys).coeff (j + 1)) -
              C (if 2 ≤ j + 1 then
                  (optionalRisePolynomial c xs).coeff (j + 1 - 2)
                else 0) * (X + C γ)) *
            shiftedRationalRodRow ys c 2 xs γ (n - (j + 1)) := by
  simpa only [coeff_rationalBackgroundDenominator,
    coeff_markedFactorSeries] using
    shiftedRationalRodRow_eq_sub_sum ys c (by norm_num) xs γ n

/-- Canonical guarded two-seed recurrence, with the lag-`j+1` coefficient
packaged as `twoSeedRecurrenceCoefficient`. -/
theorem shiftedRationalRodRow_two_seed_recurrence
    (ys : List ℝ) (c : ℝ) (xs : List ℝ) (γ : ℝ) (n : ℕ) :
    shiftedRationalRodRow ys c 2 xs γ n =
      C (if n = 0 then 1 else 0) +
        ∑ j ∈ Finset.range n,
          twoSeedRecurrenceCoefficient
              (if 2 ≤ j + 1 then
                (optionalRisePolynomial c xs).coeff (j + 1 - 2)
              else 0)
              ((optionalRisePolynomial 1 ys).coeff (j + 1)) γ (j + 1) *
            shiftedRationalRodRow ys c 2 xs γ (n - (j + 1)) := by
  rw [shiftedRationalRodRow_two_seed_eq_sub_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [twoSeedRecurrenceCoefficient]
  ring

end

end RealRooted.BrandenLeite
