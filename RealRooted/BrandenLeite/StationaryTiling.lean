import RealRooted.BrandenLeite.TilingFactors
import RealRooted.BrandenLeite.TwoKernel
import RealRooted.FiniteFreeRootCount

/-!
# Stationary rational rod-tiling rows

This file specializes the literal two-kernel theorem to finite products of
geometric background factors and optional-rise marked factors.  It records the
exact formal denominator identity and its finite coefficient recurrence before
specializing to a single monomer background.
-/

open Polynomial

namespace RealRooted.BrandenLeite

noncomputable section

/-- The finite scalar denominator `∏ y ∈ ys, (1 - y * X)`. -/
def rationalBackgroundDenominator (ys : List ℝ) : PowerSeries ℝ :=
  (ys.map fun y => 1 - PowerSeries.C y * PowerSeries.X).prod

/-- The coefficient rows of
`1 / (Q(z) - X * z^r * A(z))`, represented through the two-kernel theorem. -/
def rationalRodRow (ys : List ℝ) (c : ℝ) (r : ℕ)
    (xs : List ℝ) (n : ℕ) : ℝ[X] :=
  twoKernelRow (rationalBackgroundSeries ys)
    (markedFactorSeries c r xs) n

/-- The formal series whose coefficients are the rational rod rows. -/
def rationalRodGeneratingSeries (ys : List ℝ) (c : ℝ) (r : ℕ)
    (xs : List ℝ) : PowerSeries ℝ[X] :=
  twoKernelGeneratingSeries (rationalBackgroundSeries ys)
    (markedFactorSeries c r xs)

/-- The polynomial-valued denominator `Q(z) - X * z^r * A(z)`. -/
def rationalRodDenominatorSeries (ys : List ℝ) (c : ℝ) (r : ℕ)
    (xs : List ℝ) : PowerSeries ℝ[X] :=
  polynomialLift (rationalBackgroundDenominator ys) -
    PowerSeries.C X * polynomialLift (markedFactorSeries c r xs)

@[simp]
theorem coeff_rationalRodGeneratingSeries
    (ys : List ℝ) (c : ℝ) (r : ℕ) (xs : List ℝ) (n : ℕ) :
    PowerSeries.coeff n (rationalRodGeneratingSeries ys c r xs) =
      rationalRodRow ys c r xs n := by
  simp [rationalRodGeneratingSeries, rationalRodRow]

@[simp]
theorem constantCoeff_rationalBackgroundDenominator (ys : List ℝ) :
    PowerSeries.constantCoeff (rationalBackgroundDenominator ys) = 1 := by
  induction ys with
  | nil => simp [rationalBackgroundDenominator]
  | cons y ys ih =>
      change PowerSeries.constantCoeff
        ((1 - PowerSeries.C y * PowerSeries.X) *
          rationalBackgroundDenominator ys) = 1
      rw [map_mul, ih]
      simp

/-- The scalar denominator and background product are exact formal inverses. -/
theorem rationalBackgroundDenominator_mul_series (ys : List ℝ) :
    rationalBackgroundDenominator ys * rationalBackgroundSeries ys = 1 := by
  simpa [rationalBackgroundDenominator, mul_comm] using
    rationalBackgroundSeries_mul_denominators ys

/-- All stationary rational rod rows are PF and consecutive rows are in
zero-aware proper position. -/
theorem rationalRodRows_pf_and_prec0
    {ys xs : List ℝ} (hys : ∀ y ∈ ys, 0 ≤ y)
    {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : r ≠ 0)
    (hxs : ∀ x ∈ xs, 0 ≤ x) :
    (∀ n, IsPFPolynomial (rationalRodRow ys c r xs n)) ∧
      ∀ n, Interl (rationalRodRow ys c r xs n)
        (rationalRodRow ys c r xs (n + 1)) := by
  have hg := rationalBackgroundSeries_coeff_isPolyaFreqSeq hys
  have hh := markedFactorSeries_coeff_isPolyaFreqSeq hc r hxs
  have hg0 : 0 < PowerSeries.coeff 0 (rationalBackgroundSeries ys) := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    simp
  have hh0 : PowerSeries.coeff 0 (markedFactorSeries c r xs) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantCoeff_markedFactorSeries c hr xs
  simpa [rationalRodRow] using
    (twoKernelRows_pf_and_prec0 hg hh hg0 hh0)

/-- Multiplication by the literal rational denominator recovers one. -/
theorem rationalRodDenominator_mul_generatingSeries
    (ys : List ℝ) (c : ℝ) {r : ℕ} (hr : r ≠ 0) (xs : List ℝ) :
    rationalRodDenominatorSeries ys c r xs *
        rationalRodGeneratingSeries ys c r xs = 1 := by
  let Q := rationalBackgroundDenominator ys
  let g := rationalBackgroundSeries ys
  let h := markedFactorSeries c r xs
  let F := twoKernelGeneratingSeries g h
  have hzero : PowerSeries.constantCoeff h = 0 := by
    exact constantCoeff_markedFactorSeries c hr xs
  have hQg : Q * g = 1 := rationalBackgroundDenominator_mul_series ys
  have hbase :
      (1 - PowerSeries.C X * polynomialLift (g * h)) * F =
        polynomialLift g :=
    one_sub_mul_twoKernelGeneratingSeries hzero
  have hfactor :
      rationalRodDenominatorSeries ys c r xs =
        polynomialLift Q *
          (1 - PowerSeries.C X * polynomialLift (g * h)) := by
    change polynomialLift Q - PowerSeries.C X * polynomialLift h = _
    calc
      polynomialLift Q - PowerSeries.C X * polynomialLift h =
          polynomialLift Q - PowerSeries.C X *
            (polynomialLift Q * polynomialLift (g * h)) := by
              rw [← polynomialLift_mul, ← mul_assoc, hQg, one_mul]
      _ = polynomialLift Q *
          (1 - PowerSeries.C X * polynomialLift (g * h)) := by ring
  change rationalRodDenominatorSeries ys c r xs * F = 1
  rw [hfactor, mul_assoc, hbase, ← polynomialLift_mul, hQg,
    polynomialLift_one]

/-- Exact finite coefficient identity for the rational denominator. -/
theorem rationalRodRow_finite_denominator
    (ys : List ℝ) (c : ℝ) {r : ℕ} (hr : r ≠ 0)
    (xs : List ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff j (rationalRodDenominatorSeries ys c r xs) *
          rationalRodRow ys c r xs (n - j) =
      if n = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff n)
    (rationalRodDenominator_mul_generatingSeries ys c hr xs)
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa [coeff_rationalRodGeneratingSeries] using h

/-- The exact inhomogeneous causal recurrence, including its low-index
numerator term. -/
theorem rationalRodRow_eq_sub_sum
    (ys : List ℝ) (c : ℝ) {r : ℕ} (hr : r ≠ 0)
    (xs : List ℝ) (n : ℕ) :
    rationalRodRow ys c r xs n =
      (if n = 0 then 1 else 0) -
        ∑ j ∈ Finset.range n,
          PowerSeries.coeff (j + 1)
              (rationalRodDenominatorSeries ys c r xs) *
            rationalRodRow ys c r xs (n - (j + 1)) := by
  apply eq_sub_sum_of_finite_denominator_numerator
    (D := fun j =>
      PowerSeries.coeff j (rationalRodDenominatorSeries ys c r xs))
    (E := fun j => if j = 0 then 1 else 0)
  · rw [rationalRodDenominatorSeries, map_sub,
      coeff_polynomialLift, PowerSeries.coeff_C_mul,
      coeff_polynomialLift, PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_rationalBackgroundDenominator,
      constantCoeff_markedFactorSeries c hr xs]
    simp
  · exact rationalRodRow_finite_denominator ys c hr xs

@[simp]
theorem rationalRodRow_zero
    (ys : List ℝ) (c : ℝ) (r : ℕ) (xs : List ℝ) :
    rationalRodRow ys c r xs 0 = 1 := by
  simp [rationalRodRow, twoKernelRow]

/-- The unmarked coefficient of a rational rod row is the corresponding
background-series coefficient. -/
theorem coeff_zero_rationalRodRow
    (ys : List ℝ) (c : ℝ) {r : ℕ} (hr : r ≠ 0)
    (xs : List ℝ) (n : ℕ) :
    (rationalRodRow ys c r xs n).coeff 0 =
      PowerSeries.coeff n (rationalBackgroundSeries ys) := by
  have hzero : PowerSeries.constantCoeff (markedFactorSeries c r xs) = 0 :=
    constantCoeff_markedFactorSeries c hr xs
  rw [rationalRodRow, coeff_twoKernelRow hzero]
  simp

/-- Stationary rod rows with a single monomer background of weight `b`. -/
def monomerRodRow (b c : ℝ) (r : ℕ) (xs : List ℝ) (n : ℕ) : ℝ[X] :=
  rationalRodRow [b] c r xs n

/-- Monomer rod rows inherit PF and consecutive zero-aware proper position. -/
theorem monomerRodRows_pf_and_prec0
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) {r : ℕ} (hr : r ≠ 0)
    {xs : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x) :
    (∀ n, IsPFPolynomial (monomerRodRow b c r xs n)) ∧
      ∀ n, Interl (monomerRodRow b c r xs n)
        (monomerRodRow b c r xs (n + 1)) := by
  simpa [monomerRodRow] using
    (rationalRodRows_pf_and_prec0 (ys := [b]) (by simpa) hc hr hxs)

/-- Positive-degree coefficients of the one-background denominator. -/
theorem coeff_rationalRodDenominatorSeries_singleton_succ
    (b c : ℝ) (r : ℕ) (xs : List ℝ) (j : ℕ) :
    PowerSeries.coeff (j + 1)
        (rationalRodDenominatorSeries [b] c r xs) =
      (if j = 0 then C (-b) else 0) -
        X * C (PowerSeries.coeff (j + 1)
          (markedFactorSeries c r xs)) := by
  simp [rationalRodDenominatorSeries, rationalBackgroundDenominator,
    coeff_polynomialLift, PowerSeries.coeff_C_mul]
  by_cases hj : j = 0
  · subst j
    simp
  · rw [PowerSeries.coeff_C, ite_eq_right hj, ite_eq_right hj]
    simp

/-- The constant coefficient counts the all-monomer configuration. -/
@[simp]
theorem coeff_zero_monomerRodRow
    (b c : ℝ) {r : ℕ} (hr : r ≠ 0) (xs : List ℝ) (n : ℕ) :
    (monomerRodRow b c r xs n).coeff 0 = b ^ n := by
  simpa [monomerRodRow] using coeff_zero_rationalRodRow [b] c hr xs n

/-- The exact guarded stationary rod recurrence with one monomer species. -/
theorem monomerRodRow_succ
    (b c : ℝ) {r : ℕ} (hr : r ≠ 0) (xs : List ℝ) (n : ℕ) :
    monomerRodRow b c r xs (n + 1) =
      C b * monomerRodRow b c r xs n +
        X * ∑ j ∈ Finset.range (n + 1),
          C (PowerSeries.coeff (j + 1) (markedFactorSeries c r xs)) *
            monomerRodRow b c r xs (n - j) := by
  rw [monomerRodRow, rationalRodRow_eq_sub_sum [b] c hr xs (n + 1)]
  simp_rw [coeff_rationalRodDenominatorSeries_singleton_succ,
    Nat.succ_sub_succ_eq_sub]
  simp [monomerRodRow]
  have hbackground :
      ∑ j ∈ Finset.range (n + 1),
          (if j = 0 then -C b else 0) *
            rationalRodRow [b] c r xs (n - j) =
        -C b * rationalRodRow [b] c r xs n := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      simp [hj0]
    · simp
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, hbackground]
  ring_nf
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The same recurrence with the marked coefficients exposed as the guarded
optional-rise inventory. -/
theorem monomerRodRow_succ_factor_coeff
    (b c : ℝ) {r : ℕ} (hr : r ≠ 0) (xs : List ℝ) (n : ℕ) :
    monomerRodRow b c r xs (n + 1) =
      C b * monomerRodRow b c r xs n +
        X * ∑ j ∈ Finset.range (n + 1),
          C (if r ≤ j + 1 then
              (optionalRisePolynomial c xs).coeff (j + 1 - r)
            else 0) * monomerRodRow b c r xs (n - j) := by
  simpa only [coeff_markedFactorSeries] using
    monomerRodRow_succ b c hr xs n

/-- The optional-rise inventory `(1 + z)^2`, shifted by two length units,
has marked coefficients `1, 2, 1`. -/
theorem coeff_quadraticMarkedFactorSeries (j : ℕ) :
    PowerSeries.coeff (j + 1) (markedFactorSeries 1 2 [1, 1]) =
      if j = 1 then 1 else if j = 2 then 2 else if j = 3 then 1 else 0 := by
  have hpoly : optionalRisePolynomial 1 [1, 1] =
      1 + C 2 * X + X ^ 2 := by
    norm_num [optionalRisePolynomial]
    rw [show C 2 = (2 : ℝ[X]) by rfl]
    ring
  rw [coeff_markedFactorSeries, hpoly]
  by_cases hj : j ≤ 3
  · interval_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_one,
        Polynomial.coeff_C_mul, Polynomial.coeff_X,
        Polynomial.coeff_X_pow]
  · have hj4 : 4 ≤ j := by lia
    rw [ite_eq_left (by lia)]
    have hs0 : j - 1 ≠ 0 := by lia
    have hs1 : j - 1 ≠ 1 := by lia
    have hs1' : 1 ≠ j - 1 := Ne.symm hs1
    have hj1 : j ≠ 1 := by lia
    have hj2 : j ≠ 2 := by lia
    have hj3 : j ≠ 3 := by lia
    simp [Polynomial.coeff_add, Polynomial.coeff_one,
      Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_X_pow, hs0, hs1', hj1, hj2, hj3]

/-- The stationary rod model with marked inventory `(1 + z)^2` and lag two. -/
def quadraticRodRow (n : ℕ) : ℝ[X] :=
  monomerRodRow 1 1 2 [1, 1] n

/-- The four-lag recurrence
`P_(n+4) = P_(n+3) + X*P_(n+2) + 2*X*P_(n+1) + X*P_n`. -/
theorem quadraticRodRow_add_four (n : ℕ) :
    quadraticRodRow (n + 4) =
      quadraticRodRow (n + 3) + X * quadraticRodRow (n + 2) +
        C 2 * X * quadraticRodRow (n + 1) + X * quadraticRodRow n := by
  have h := monomerRodRow_succ 1 1 (r := 2) (by norm_num) [1, 1] (n + 3)
  simp_rw [coeff_quadraticMarkedFactorSeries] at h
  have hC (j : ℕ) :
      Polynomial.C (if j = 1 then (1 : ℝ) else if j = 2 then 2 else
        if j = 3 then 1 else 0) =
        if j = 1 then 1 else if j = 2 then C 2 else
          if j = 3 then 1 else 0 := by
    by_cases h1 : j = 1
    · simp [h1]
    · by_cases h2 : j = 2
      · simp [h2]
      · by_cases h3 : j = 3 <;> simp [h1, h2, h3]
  simp_rw [hC] at h
  have hsum :
      ∑ j ∈ Finset.range (n + 4),
          (if j = 1 then 1 else if j = 2 then C 2 else
            if j = 3 then 1 else 0) *
            monomerRodRow 1 1 2 [1, 1] (n + 3 - j) =
        monomerRodRow 1 1 2 [1, 1] (n + 2) +
          C 2 * monomerRodRow 1 1 2 [1, 1] (n + 1) +
            monomerRodRow 1 1 2 [1, 1] n := by
    have hsplit (j : ℕ) :
        (if j = 1 then 1 else if j = 2 then C 2 else
          if j = 3 then 1 else 0) *
            monomerRodRow 1 1 2 [1, 1] (n + 3 - j) =
          (if j = 1 then monomerRodRow 1 1 2 [1, 1] (n + 3 - j) else 0) +
          (if j = 2 then C 2 * monomerRodRow 1 1 2 [1, 1] (n + 3 - j) else 0) +
          (if j = 3 then monomerRodRow 1 1 2 [1, 1] (n + 3 - j) else 0) := by
      by_cases h1 : j = 1
      · simp [h1]
      · by_cases h2 : j = 2
        · simp [h2]
        · by_cases h3 : j = 3 <;> simp [h1, h2, h3]
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp [show 1 < n + 4 by lia, show 2 < n + 4 by lia,
      show 3 < n + 4 by lia]
  rw [show n + 3 + 1 = n + 4 by lia, hsum] at h
  simp [quadraticRodRow] at h ⊢
  ring_nf at h ⊢
  exact h

/-- Positive monomer weight excludes zero from every root multiset. -/
theorem monomerRodRow_roots_neg
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) {r : ℕ} (hr : r ≠ 0)
    {xs : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x) (n : ℕ) :
    ∀ x ∈ (monomerRodRow b c r xs n).roots, x < 0 := by
  have hpf := (monomerRodRows_pf_and_prec0 hb.le hc hr hxs).1 n
  apply hpf.roots_neg_of_coeff_zero_ne
  simp [hr, pow_ne_zero _ hb.ne']

end

end RealRooted.BrandenLeite
