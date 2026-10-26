module

public import RealRooted.CombinatorialExamples.PathPowerClique
public import RealRooted.WagnerX.NonnegativeRoots

/-!
# Weighted renewal polynomials

We formalize the weighted-renewal family from
[RealRooted issue #2037](https://github.com/PerAlexandersson/RealRooted/issues/2037).
For positive `a : Fin d → ℝ`, put `R(z) = ∏ r, (1 + a r * z)`.  The
coefficient polynomial `P n` extracted from

`1 / (1 - x * R(t * x ^ ℓ))`

is identified with row `d * (n - ℓ)` of a periodic weighted gap recurrence
with fixed delay `d * ℓ + 1`.  The fixed-delay window then proves
`StrictInterl (P n) (P (n + s))` whenever `d * s ≤ d * ℓ + 1`.

For the rigid specialization, coefficient extraction from

`1 / (1 - x * (1 + t * x ^ ℓ) ^ d)`

gives the polynomial

`P n = ∑ j, choose (d * (n - ℓ * j)) j * t ^ j`.

We retain its identification with a sampled path-power polynomial and its
existing public theorem statements.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RealRooted

/-- The periodic extension of a finite sequence of weights, indexed from zero. -/
def periodicRenewalWeight {d : ℕ} [NeZero d] (a : Fin d → ℝ) (n : ℕ) : ℝ :=
  a ⟨n % d, Nat.mod_lt n (Nat.pos_of_neZero d)⟩

/-- The product of the first `N` linear factors from a periodic weight sequence. -/
def periodicRenewalProduct {d : ℕ} [NeZero d] (a : Fin d → ℝ) (N : ℕ) : ℝ[X] :=
  ∏ i ∈ range N, (1 + C (periodicRenewalWeight a i) * X)

/-- The product `∏ r, (1 + a r X)` that drives a weighted renewal family. -/
def renewalFactorPolynomial {d : ℕ} (a : Fin d → ℝ) : ℝ[X] :=
  ∏ r, (1 + C (a r) * X)

/-- The weighted gap-subset polynomials, specified by their fixed-delay recurrence.

At row `N + 1`, the new endpoint has periodic weight `a (N % d)`, and its
predecessor row is `N + 1 - (d * ℓ + 1)`. -/
def weightedGapPolynomial {d : ℕ} [NeZero d] (a : Fin d → ℝ) (ℓ : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | N + 1 =>
      weightedGapPolynomial a ℓ N +
        C (periodicRenewalWeight a N) * X *
          weightedGapPolynomial a ℓ (N + 1 - (d * ℓ + 1))
termination_by N => N
decreasing_by
  · exact Nat.lt_succ_self _
  · apply Nat.sub_lt
    · positivity
    · positivity

private theorem periodicRenewalProduct_succ {d : ℕ} [NeZero d] (a : Fin d → ℝ) (N : ℕ) :
    periodicRenewalProduct a (N + 1) =
      periodicRenewalProduct a N *
        (1 + C (periodicRenewalWeight a N) * X) := by
  simp [periodicRenewalProduct, Finset.prod_range_succ]

private theorem coeff_periodicRenewalProduct_succ {d : ℕ} [NeZero d]
    (a : Fin d → ℝ) (N j : ℕ) :
    (periodicRenewalProduct a (N + 1)).coeff (j + 1) =
      (periodicRenewalProduct a N).coeff (j + 1) +
        periodicRenewalWeight a N * (periodicRenewalProduct a N).coeff j := by
  rw [periodicRenewalProduct_succ]
  ring_nf
  simp only [add_comm 1 j]
  rw [coeff_add, coeff_mul_X, coeff_mul_C]
  ring

private theorem coeff_zero_periodicRenewalProduct {d : ℕ} [NeZero d]
    (a : Fin d → ℝ) (N : ℕ) :
    (periodicRenewalProduct a N).coeff 0 = 1 := by
  induction N with
  | zero => simp [periodicRenewalProduct]
  | succ N ih =>
      rw [periodicRenewalProduct_succ, mul_coeff_zero, ih]
      simp

private theorem periodicRenewalWeight_sub_mul {d : ℕ} [NeZero d]
    (a : Fin d → ℝ) (N q : ℕ) (hq : d * q ≤ N) :
    periodicRenewalWeight a (N - d * q) = periodicRenewalWeight a N := by
  unfold periodicRenewalWeight
  apply congrArg a
  apply Fin.ext
  dsimp
  conv_rhs => rw [show N = N - d * q + d * q by lia]
  simp [Nat.add_mod]

private theorem coeff_zero_weightedGapPolynomial {d : ℕ} [NeZero d]
    (a : Fin d → ℝ) (ℓ N : ℕ) :
    (weightedGapPolynomial a ℓ N).coeff 0 = 1 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      rcases N with _ | N
      · simp [weightedGapPolynomial]
      · rw [weightedGapPolynomial, coeff_add]
        simp [ih N (Nat.lt_succ_self N)]

private theorem coeff_weightedGapPolynomial_succ {d : ℕ} [NeZero d]
    (a : Fin d → ℝ) (ℓ N j : ℕ) :
    (weightedGapPolynomial a ℓ N).coeff (j + 1) =
      (periodicRenewalProduct a (N - d * ℓ * j)).coeff (j + 1) := by
  revert j
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro j
      rcases N with _ | N
      · simp [weightedGapPolynomial, periodicRenewalProduct]
      · rw [weightedGapPolynomial, coeff_add]
        rw [mul_assoc, coeff_C_mul, coeff_X_mul]
        rcases j with _ | j
        · rw [ih N (Nat.lt_succ_self N) 0, coeff_zero_weightedGapPolynomial]
          simpa [coeff_zero_periodicRenewalProduct] using
            (coeff_periodicRenewalProduct_succ a N 0).symm
        · rw [ih N (Nat.lt_succ_self N) (j + 1)]
          have hlag : N + 1 - (d * ℓ + 1) < N + 1 := by
            exact Nat.sub_lt (Nat.succ_pos N) (by positivity)
          rw [ih (N + 1 - (d * ℓ + 1)) hlag j]
          have hindex :
              N + 1 - (d * ℓ + 1) - d * ℓ * j = N - d * ℓ * (j + 1) := by
            ring_nf
            lia
          rw [hindex]
          by_cases hbound : d * ℓ * (j + 1) ≤ N
          · have hsucc : N + 1 - d * ℓ * (j + 1) =
                (N - d * ℓ * (j + 1)) + 1 := by
              lia
            rw [hsucc, coeff_periodicRenewalProduct_succ]
            have hweight := periodicRenewalWeight_sub_mul a N (ℓ * (j + 1))
              (by simpa [mul_assoc] using hbound)
            rw [show d * (ℓ * (j + 1)) = d * ℓ * (j + 1) by ring] at hweight
            rw [hweight]
          · have hzero : N + 1 ≤ d * ℓ * (j + 1) := by lia
            have hzero' : N ≤ d * ℓ * (j + 1) := by lia
            rw [Nat.sub_eq_zero_of_le hzero, Nat.sub_eq_zero_of_le hzero']
            simp only [periodicRenewalProduct, range_zero, prod_empty, coeff_one,
              Nat.succ_ne_zero, ite_false, mul_zero, add_zero]

private theorem periodicRenewalProduct_block {d : ℕ} [NeZero d]
    (a : Fin d → ℝ) (k : ℕ) :
    ∏ i ∈ range d,
        (1 + C (periodicRenewalWeight a (d * k + i)) * X) =
      renewalFactorPolynomial a := by
  rw [renewalFactorPolynomial, Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [mem_range.mp hi, dite_true]
  simp only [periodicRenewalWeight]
  congr 4
  simp [Nat.add_mod, Nat.mod_eq_of_lt (mem_range.mp hi)]

private theorem periodicRenewalProduct_mul {d : ℕ} [NeZero d]
    (a : Fin d → ℝ) (k : ℕ) :
    periodicRenewalProduct a (d * k) = renewalFactorPolynomial a ^ k := by
  induction k with
  | zero => simp [periodicRenewalProduct]
  | succ k ih =>
      rw [Nat.mul_succ, periodicRenewalProduct, Finset.prod_range_add]
      change periodicRenewalProduct a (d * k) * _ = _
      rw [ih, periodicRenewalProduct_block, pow_succ]

/-- The constant coefficient of a renewal factor polynomial is one. -/
theorem coeff_zero_renewalFactorPolynomial {d : ℕ} (a : Fin d → ℝ) :
    (renewalFactorPolynomial a).coeff 0 = 1 := by
  classical
  rw [renewalFactorPolynomial, coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  simp

private theorem coeff_zero_renewalFactorPolynomial_pow {d : ℕ}
    (a : Fin d → ℝ) (n : ℕ) :
    (renewalFactorPolynomial a ^ n).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero,
    coeff_zero_renewalFactorPolynomial, one_pow]

/-- The coefficient polynomial extracted from `1 / (1 - x * R (t * x ^ ℓ))`.

The coefficient of `X ^ j` is `[z ^ j] R(z) ^ (n - ℓ * j)`.  The theorem
`weightedRenewalPolynomial_eq_weightedGapPolynomial` below proves that this
explicit formula is exactly the sampled periodic fixed-delay recurrence. -/
def renewalPolynomial (R : ℝ[X]) (ℓ n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n + 1),
    C ((R ^ (n - ℓ * j)).coeff j) * X ^ j

/-- The renewal polynomial driven by `∏ r, (1 + a r X)`. -/
def weightedRenewalPolynomial {d : ℕ} (a : Fin d → ℝ) (ℓ n : ℕ) : ℝ[X] :=
  renewalPolynomial (renewalFactorPolynomial a) ℓ n

/-- Expanding the definition of a weighted renewal polynomial exposes its driver. -/
theorem weightedRenewalPolynomial_eq_renewalPolynomial {d : ℕ}
    (a : Fin d → ℝ) (ℓ n : ℕ) :
    weightedRenewalPolynomial a ℓ n =
      renewalPolynomial (renewalFactorPolynomial a) ℓ n := rfl

/-- Coefficients of a renewal polynomial. Terms whose apparent factor exponent
would be negative vanish after truncated subtraction. -/
theorem coeff_renewalPolynomial (R : ℝ[X]) (ℓ n j : ℕ) (hℓ : ℓ ≠ 0) :
    (renewalPolynomial R ℓ n).coeff j = (R ^ (n - ℓ * j)).coeff j := by
  simp only [renewalPolynomial, finsetSum_coeff, coeff_C_mul_X_pow,
    Finset.sum_ite_eq, mem_range]
  split_ifs with hj
  · rfl
  · have hnj : n < j := by lia
    have hjℓ : j ≤ ℓ * j := by
      simpa [one_mul] using Nat.mul_le_mul_right j (Nat.one_le_iff_ne_zero.mpr hℓ)
    have hsub : n - ℓ * j = 0 := Nat.sub_eq_zero_of_le (by lia)
    rw [hsub, pow_zero, coeff_one]
    have hj0 : j ≠ 0 := by lia
    simp only [hj0, ite_false]

/-- Coefficients of the weighted renewal polynomial.  Terms whose apparent
factor exponent would be negative vanish after truncated subtraction. -/
theorem coeff_weightedRenewalPolynomial {d : ℕ} (a : Fin d → ℝ)
    (ℓ n j : ℕ) (hℓ : ℓ ≠ 0) :
    (weightedRenewalPolynomial a ℓ n).coeff j =
      (renewalFactorPolynomial a ^ (n - ℓ * j)).coeff j := by
  exact coeff_renewalPolynomial (renewalFactorPolynomial a) ℓ n j hℓ

private theorem weightedRenewalPolynomial_eq_one_of_lt {d : ℕ}
    (a : Fin d → ℝ) {ℓ n : ℕ} (hℓ : ℓ ≠ 0) (hn : n < ℓ) :
    weightedRenewalPolynomial a ℓ n = 1 := by
  ext j
  rw [coeff_weightedRenewalPolynomial a ℓ n j hℓ]
  rcases j with _ | j
  · simpa using coeff_zero_renewalFactorPolynomial_pow a n
  · have hsub : n - ℓ * (j + 1) = 0 := by
      apply Nat.sub_eq_zero_of_le
      have hmul : ℓ ≤ ℓ * (j + 1) := by
        exact Nat.le_mul_of_pos_right ℓ (Nat.succ_pos j)
      lia
    rw [hsub, pow_zero, coeff_one]

/-- The explicit renewal coefficient formula is the periodic weighted gap
recurrence sampled at row `d * (n - ℓ)`.  This is the compression identity
from RealRooted issue #2037. -/
theorem weightedRenewalPolynomial_eq_weightedGapPolynomial {d : ℕ} [NeZero d]
    (a : Fin d → ℝ) (ℓ n : ℕ) (hℓ : ℓ ≠ 0) :
    weightedRenewalPolynomial a ℓ n =
      weightedGapPolynomial a ℓ (d * (n - ℓ)) := by
  by_cases hn : n < ℓ
  · rw [weightedRenewalPolynomial_eq_one_of_lt a hℓ hn]
    have hsub : n - ℓ = 0 := Nat.sub_eq_zero_of_le hn.le
    simp [hsub, weightedGapPolynomial]
  · have hℓn : ℓ ≤ n := by lia
    ext j
    rw [coeff_weightedRenewalPolynomial a ℓ n j hℓ]
    rcases j with _ | j
    · rw [coeff_zero_weightedGapPolynomial]
      simpa using coeff_zero_renewalFactorPolynomial_pow a n
    · rw [coeff_weightedGapPolynomial_succ]
      have hindex : d * (n - ℓ) - d * ℓ * j = d * (n - ℓ * (j + 1)) := by
        rw [show d * ℓ * j = d * (ℓ * j) by ring, ← Nat.mul_sub_left_distrib]
        congr 1
        ring_nf
        lia
      rw [hindex, periodicRenewalProduct_mul]

/-- **General weighted renewal interlacing window.**  Suppose every factor
weight is positive.  If `d, ℓ ≥ 1` and `d * s ≤ d * ℓ + 1`, then the
coefficient polynomial of `x ^ n` in
`1 / (1 - x * R (t * x ^ ℓ))` interlaces the row at `x ^ (n + s)`, where
`R = ∏ r, (1 + a r X)`. -/
theorem strictInterl_weightedRenewalPolynomial_add {d : ℕ} [NeZero d]
    (a : Fin d → ℝ) (ℓ n s : ℕ) (hℓ : ℓ ≠ 0)
    (ha : ∀ r, 0 < a r) (hs : d * s ≤ d * ℓ + 1) :
    StrictInterl (weightedRenewalPolynomial a ℓ n)
      (weightedRenewalPolynomial a ℓ (n + s)) := by
  let Q := weightedGapPolynomial a ℓ
  let w : ℕ → ℝ := fun m ↦ periodicRenewalWeight a (m - 1)
  have hw : ∀ m, 0 ≤ w m := by
    intro m
    exact (ha _).le
  have hQ0 : Q 0 = 1 := by
    simp [Q, weightedGapPolynomial]
  have hrec : ∀ N,
      Q (N + 1) = Q N + C (w (N + 1)) * X * Q (N + 1 - (d * ℓ + 1)) := by
    intro N
    simp [Q, w, weightedGapPolynomial]
  have hAB : d * (n - ℓ) ≤ d * (n + s - ℓ) := by
    exact Nat.mul_le_mul_left d (Nat.sub_le_sub_right (Nat.le_add_right n s) ℓ)
  have hgap : d * (n + s - ℓ) ≤ d * (n - ℓ) + (d * ℓ + 1) := by
    calc
      d * (n + s - ℓ) ≤ d * ((n - ℓ) + s) :=
        Nat.mul_le_mul_left d (by lia)
      _ = d * (n - ℓ) + d * s := by ring
      _ ≤ d * (n - ℓ) + (d * ℓ + 1) := Nat.add_le_add_left hs _
  rw [weightedRenewalPolynomial_eq_weightedGapPolynomial a ℓ n hℓ,
    weightedRenewalPolynomial_eq_weightedGapPolynomial a ℓ (n + s) hℓ]
  exact strictInterl_of_fixedDelay_recurrence Q w (d * ℓ + 1) (by lia)
    hw hQ0 hrec hAB hgap

/-- The renewal polynomial driven by the constant polynomial one is constant. -/
@[simp]
theorem renewalPolynomial_one (ℓ n : ℕ) : renewalPolynomial 1 ℓ n = 1 := by
  ext j
  rcases j with _ | j <;> simp [renewalPolynomial, coeff_one]

/-- **Renewal interlacing window** (RealRooted issue #2037).  Let `R` have nonnegative
coefficients, constant coefficient one, and only real roots, and let `d = R.natDegree`.  If
`ℓ ≠ 0` and `d * s ≤ d * ℓ + 1`, then the coefficient of `x ^ n` in
`1 / (1 - x * R (t * x ^ ℓ))` interlaces the coefficient of `x ^ (n + s)`.  For `d = 0` the
rows are constant. -/
theorem strictInterl_renewalPolynomial_add (R : ℝ[X]) (ℓ n s : ℕ)
    (hRnn : HasNonnegCoeffs R) (hR0 : R.coeff 0 = 1) (hRsplits : R.Splits) (hℓ : ℓ ≠ 0)
    (hs : R.natDegree * s ≤ R.natDegree * ℓ + 1) :
    StrictInterl (renewalPolynomial R ℓ n) (renewalPolynomial R ℓ (n + s)) := by
  by_cases hd : R.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hd, hR0, map_one, renewalPolynomial_one,
      renewalPolynomial_one]
    exact StrictInterl.refl one_ne_zero Polynomial.Splits.one
  have : NeZero R.natDegree := ⟨hd⟩
  obtain ⟨a, ha, hR⟩ := exists_eq_prod_one_add_C_mul_X_of_splits hRnn hR0 hRsplits
  have hR' : R = renewalFactorPolynomial a := hR
  rw [hR']
  exact strictInterl_weightedRenewalPolynomial_add a ℓ n s hℓ ha hs

/-- The coefficient polynomial extracted from
`1 / (1 - x * (1 + t * x ^ ℓ) ^ d)`.

The truncated subtraction is harmless for `ℓ ≥ 1`: the coefficient theorem below
proves explicitly that every summand outside the nonnegative-index range vanishes. -/
def rigidRenewalPolynomial (d ℓ n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n + 1), C (((d * (n - ℓ * j)).choose j : ℕ) : ℝ) * X ^ j

/-- Coefficients of the rigid renewal polynomial.  In the out-of-range case
`n < ℓ * j`, the proof reduces the upper binomial index to zero before using
that `j > 0`; thus no negative index is represented by truncated subtraction. -/
@[simp]
theorem coeff_rigidRenewalPolynomial (d ℓ n j : ℕ) (hℓ : 1 ≤ ℓ) :
    (rigidRenewalPolynomial d ℓ n).coeff j =
      ((d * (n - ℓ * j)).choose j : ℕ) := by
  simp only [rigidRenewalPolynomial, finsetSum_coeff, coeff_C_mul_X_pow,
    Finset.sum_ite_eq, mem_range]
  split_ifs with hj
  · norm_cast
  · have hnj : n < j := by lia
    have hjℓ : j ≤ ℓ * j := by
      simpa [one_mul] using Nat.mul_le_mul_right j hℓ
    have hsub : n - ℓ * j = 0 := Nat.sub_eq_zero_of_le (by lia)
    rw [hsub, mul_zero, Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero]

/-- The rigid renewal polynomial is a sampled path-power polynomial.  This is
the compression identity used in
[RealRooted issue #2037](https://github.com/PerAlexandersson/RealRooted/issues/2037). -/
theorem rigidRenewalPolynomial_eq_pathPowerCliquePolynomial
    (d ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    rigidRenewalPolynomial d ℓ n =
      pathPowerCliquePolynomial (d * ℓ + 1) (d * n) := by
  ext j
  rw [coeff_rigidRenewalPolynomial d ℓ n j hℓ,
    coeff_pathPowerCliquePolynomial]
  norm_cast
  simp only [Nat.add_sub_cancel]
  rw [mul_assoc, ← Nat.mul_sub_left_distrib]

/-- A rigid renewal polynomial is nonzero. -/
theorem rigidRenewalPolynomial_ne_zero (d ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    rigidRenewalPolynomial d ℓ n ≠ 0 := by
  rw [rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ n hℓ]
  exact pathPowerCliquePolynomial_ne_zero (d * ℓ + 1) (d * n)

/-- Every rigid renewal polynomial splits over the reals. -/
theorem splits_rigidRenewalPolynomial (d ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    (rigidRenewalPolynomial d ℓ n).Splits := by
  rw [rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ n hℓ]
  exact splits_pathPowerCliquePolynomial (d * ℓ + 1) (d * n)

/-- **Rigid renewal interlacing window.**  If `d, ℓ ≥ 1` and
`d * s ≤ d * ℓ + 1`, then the coefficient polynomial of `x ^ n` in
`1 / (1 - x * (1 + t * x ^ ℓ) ^ d)` interlaces the coefficient polynomial
of `x ^ (n + s)`.

This is the rigid case of
[RealRooted issue #2037](https://github.com/PerAlexandersson/RealRooted/issues/2037).
Its fixed-delay input is the weighted form of Fisk, Example 16.10. -/
theorem strictInterl_rigidRenewalPolynomial_add
    (d ℓ n s : ℕ) (hd : 1 ≤ d) (hℓ : 1 ≤ ℓ)
    (hs : d * s ≤ d * ℓ + 1) :
    StrictInterl (rigidRenewalPolynomial d ℓ n)
      (rigidRenewalPolynomial d ℓ (n + s)) := by
  by_cases hs0 : s = 0
  · subst s
    simpa using StrictInterl.refl (rigidRenewalPolynomial_ne_zero d ℓ n hℓ)
      (splits_rigidRenewalPolynomial d ℓ n hℓ)
  · rw [rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ n hℓ,
      rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ (n + s) hℓ,
      Nat.mul_add]
    apply strictInterl_pathPowerCliquePolynomial_add
    · have hdℓ : 0 < d * ℓ := Nat.mul_pos hd hℓ
      lia
    · exact Nat.mul_pos hd (Nat.pos_of_ne_zero hs0)
    · exact hs

/-- Consecutive rigid renewal polynomials interlace.  This is the rigid-tiling
consequence requested in RealRooted issue #2037. -/
theorem strictInterl_rigidRenewalPolynomial_succ
    (d ℓ n : ℕ) (hd : 1 ≤ d) (hℓ : 1 ≤ ℓ) :
    StrictInterl (rigidRenewalPolynomial d ℓ n)
      (rigidRenewalPolynomial d ℓ (n + 1)) := by
  apply strictInterl_rigidRenewalPolynomial_add d ℓ n 1 hd hℓ
  have hdℓ : d ≤ d * ℓ := by
    simpa using Nat.mul_le_mul_left d hℓ
  simpa using le_trans hdℓ (Nat.le_add_right (d * ℓ) 1)

end RealRooted
