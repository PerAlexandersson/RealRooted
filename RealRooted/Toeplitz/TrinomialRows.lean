module

public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Coefficients of reciprocal trinomials

We define the numerator-one rows of `1 / (1 + b t^ℓ + a t^k)` over a commutative ring.
The coefficient recurrence is the generating-function bridge used in
Bøgvad--Ndikubwayo--Shapiro, *Generalizing Tran's Conjecture*, arXiv:2001.09248v2,
Lemma 2.1 and Theorem 1.2. The real-curve theorem itself is not assumed here.
-/

@[expose] public section

noncomputable section

namespace RealRooted.Trinomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The trinomial denominator, as a formal power series. -/
def denominator (ℓ k : ℕ) (a b : R) : PowerSeries R :=
  1 + PowerSeries.C b * PowerSeries.X ^ ℓ + PowerSeries.C a * PowerSeries.X ^ k

/-- The formal reciprocal with constant coefficient one. Positive lags make this an inverse. -/
def rowSeries (ℓ k : ℕ) (a b : R) : PowerSeries R :=
  PowerSeries.invOfUnit (denominator ℓ k a b) 1

/-- The numerator-one coefficient row of a reciprocal trinomial. -/
def row (ℓ k : ℕ) (a b : R) (n : ℕ) : R :=
  PowerSeries.coeff n (rowSeries ℓ k a b)

/-- Positive lags give constant coefficient one in the denominator. -/
theorem constantCoeff_denominator {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0) (a b : R) :
    PowerSeries.constantCoeff (denominator ℓ k a b) = 1 := by
  simp [denominator, hℓ, hk]

/-- The defining generating-function identity for the numerator-one rows. -/
theorem denominator_mul_rowSeries {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0) (a b : R) :
    denominator ℓ k a b * rowSeries ℓ k a b = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simpa using constantCoeff_denominator hℓ hk a b)

/-- The initial row is one. -/
@[simp] theorem row_zero (ℓ k : ℕ) (a b : R) : row ℓ k a b 0 = 1 := by
  simp [row, rowSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The coefficient recurrence, with zero rows at negative indices encoded by conditionals. -/
theorem row_succ {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0) (a b : R) (n : ℕ) :
    row ℓ k a b (n + 1) =
      -(b * if ℓ ≤ n + 1 then row ℓ k a b (n + 1 - ℓ) else 0) -
        a * if k ≤ n + 1 then row ℓ k a b (n + 1 - k) else 0 := by
  have h := congrArg (PowerSeries.coeff (n + 1)) (denominator_mul_rowSeries hℓ hk a b)
  simp only [denominator, add_mul, one_mul, map_add, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul'] at h
  simp only [PowerSeries.coeff_one, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ite_false] at h
  simp only [row]
  linear_combination h

/-- Ring homomorphisms commute with the numerator-one rows. -/
theorem map_row (f : R →+* S) {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0)
    (a b : R) (n : ℕ) :
    f (row ℓ k a b n) = row ℓ k (f a) (f b) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [row_succ hℓ hk, row_succ hℓ hk]
      simp only [map_sub, map_neg, map_mul]
      congr 1
      · split_ifs with h
        · rw [ih _ (by lia)]
        · simp
      · split_ifs with h
        · rw [ih _ (by lia)]
        · simp

/-- A numerator-one series is determined by its denominator identity. -/
theorem rowSeries_eq_of_mul_eq_one {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0)
    (a b : R) {s : PowerSeries R} (hs : denominator ℓ k a b * s = 1) :
    s = rowSeries ℓ k a b := by
  have hleft : rowSeries ℓ k a b * denominator ℓ k a b = 1 := by
    rw [mul_comm, denominator_mul_rowSeries hℓ hk]
  calc
    s = (rowSeries ℓ k a b * denominator ℓ k a b) * s := by rw [hleft, one_mul]
    _ = rowSeries ℓ k a b * (denominator ℓ k a b * s) := by rw [mul_assoc]
    _ = rowSeries ℓ k a b := by rw [hs, mul_one]

/-- Scaling the series variable multiplies row `n` by the `n`th power of the scale. -/
theorem row_rescale {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0) (a b c : R) (n : ℕ) :
    row ℓ k (a * c ^ k) (b * c ^ ℓ) n = c ^ n * row ℓ k a b n := by
  have hC (v : R) : PowerSeries.rescale c (PowerSeries.C v) = PowerSeries.C v := by
    ext m
    simp [PowerSeries.coeff_C]
    split_ifs with hm <;> simp [hm]
  have hD : PowerSeries.rescale c (denominator ℓ k a b) =
      denominator ℓ k (a * c ^ k) (b * c ^ ℓ) := by
    simp only [denominator, map_add, map_one, map_mul, hC, map_pow,
      PowerSeries.rescale_X, mul_pow]
    simp only [← map_pow, ← mul_assoc, ← map_mul]
  have h := congrArg (PowerSeries.rescale c) (denominator_mul_rowSeries hℓ hk a b)
  rw [map_mul, map_one, hD] at h
  have hs := rowSeries_eq_of_mul_eq_one hℓ hk _ _ h
  have hc := congrArg (PowerSeries.coeff n) hs
  simpa [row] using hc.symm

/-- With vanishing high-lag coefficient, the lag-one rows are powers of `-b`. -/
@[simp] theorem row_oneLag_zero_left {k : ℕ} (hk : k ≠ 0) (b : R) (n : ℕ) :
    row 1 k 0 b n = (-b) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [row_succ (by decide : 1 ≠ 0) hk]
    simp only [show 1 ≤ n + 1 by lia, ite_true, Nat.add_sub_cancel, zero_mul, sub_zero, ih]
    ring

/-- At a lag-one row zero where the high-lag coefficient vanishes,
the linear coefficient vanishes too. -/
theorem eq_zero_of_row_oneLag_zero_left {K : Type*} [Field K] {k : ℕ} (hk : k ≠ 0)
    {b : K} {n : ℕ} (hrow : row 1 k 0 b n = 0) : b = 0 := by
  rw [row_oneLag_zero_left hk] at hrow
  by_contra hb
  exact pow_ne_zero n (neg_ne_zero.mpr hb) hrow

/-- A nonzero numerator-one row has a nonnegative decomposition of its index into the lags. -/
theorem exists_decomposition_of_row_ne_zero {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0)
    (a b : R) {n : ℕ} (hne : row ℓ k a b n ≠ 0) :
    ∃ i j : ℕ, n = ℓ * i + k * j := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨0, 0, by simp⟩
    | succ n =>
      by_cases hs : ℓ ≤ n + 1 ∧ row ℓ k a b (n + 1 - ℓ) ≠ 0
      · obtain ⟨i, j, hij⟩ := ih (n + 1 - ℓ) (by lia) hs.2
        refine ⟨i + 1, j, ?_⟩
        have h := Nat.sub_add_cancel hs.1
        nlinarith
      · have hshort : (if ℓ ≤ n + 1 then row ℓ k a b (n + 1 - ℓ) else 0) = 0 := by
          split_ifs with h
          · by_contra hne
            exact hs ⟨h, hne⟩
          · rfl
        have hl : k ≤ n + 1 ∧ row ℓ k a b (n + 1 - k) ≠ 0 := by
          rw [row_succ hℓ hk, hshort, mul_zero, neg_zero, zero_sub] at hne
          by_cases hkn : k ≤ n + 1
          · refine ⟨hkn, ?_⟩
            intro hz
            simp [hkn, hz] at hne
          · simp [hkn] at hne
        obtain ⟨i, j, hij⟩ := ih (n + 1 - k) (by lia) hl.2
        refine ⟨i, j + 1, ?_⟩
        have h := Nat.sub_add_cancel hl.1
        nlinarith

end RealRooted.Trinomial
