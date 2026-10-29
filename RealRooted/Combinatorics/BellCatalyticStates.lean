module

import RealRooted.OperatorMatrix.Directed
public import RealRooted.PFPolynomial

import Mathlib.Tactic
import RealRooted.AffineProperPosition
import RealRooted.Mathlib.Data.Nat.Choose.Sum

/-!
# Catalytic states for threshold-Bell polynomials

This file introduces the canonical distinguished-block recurrence from
[RealRooted issue #1990](https://github.com/PerAlexandersson/RealRooted/issues/1990), together
with its active, remainder, and Pascal states.  It establishes the elementary Pascal algebra
and records small concrete rows.  The adjacency hypothesis in the issue remains the intended
open boundary for the later interlacing theorem.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RealRooted

/-- The threshold-Bell polynomial in which a block contributes `X` exactly when its size is at
least `j`; this is the canonical distinguished-block recurrence of issue #1990. -/
def thresholdBell (j : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => ∑ a ∈ range (n + 1),
      C ((n.choose a : ℕ) : ℝ) * X ^ (if j ≤ a + 1 then 1 else 0) * thresholdBell j (n - a)

/-- The active catalytic state: the derivative plus the first newly marked block size. -/
def bellActive (j k : ℕ) : ℝ[X] :=
  (thresholdBell j k).derivative +
    C ((k.choose (j - 1) : ℕ) : ℝ) * thresholdBell j (k - j + 1)

/-- The remainder catalytic state, collecting distinguished blocks of size below `j`. -/
def bellRemainder (j k : ℕ) : ℝ[X] :=
  ∑ r ∈ range (min k (j - 2) + 1),
    C ((k.choose r : ℕ) : ℝ) * thresholdBell j (k - r)

/-- The `i`th Pascal state based at rank `k`; its intended range is `i ≤ k`. -/
def bellPascalState (j k i : ℕ) : ℝ[X] :=
  ∑ r ∈ range (i + 1), C ((i.choose r : ℕ) : ℝ) * thresholdBell j (k - r)

/-- The defining distinguished-block recurrence for threshold-Bell polynomials. -/
theorem thresholdBell_succ (j n : ℕ) :
    thresholdBell j (n + 1) = ∑ a ∈ range (n + 1),
      C ((n.choose a : ℕ) : ℝ) * X ^ (if j ≤ a + 1 then 1 else 0) *
        thresholdBell j (n - a) := by
  rw [thresholdBell]

/-- The rank-zero threshold-Bell polynomial is one. -/
@[simp]
theorem thresholdBell_zero (j : ℕ) : thresholdBell j 0 = 1 := by
  rw [thresholdBell]

/-- Every threshold-Bell polynomial has nonnegative coefficients. -/
theorem thresholdBell_hasNonnegCoeffs (j n : ℕ) :
    HasNonnegCoeffs (thresholdBell j n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simpa [thresholdBell] using hasNonnegCoeffs_one
      | succ n =>
          rw [thresholdBell]
          apply hasNonnegCoeffs_finsetSum
          intro a ha
          have ha_le : a ≤ n := by simpa using ha
          have hrec : HasNonnegCoeffs (thresholdBell j (n - a)) :=
            ih (n - a) (by lia)
          exact ((hasNonnegCoeffs_C (a := ((n.choose a : ℕ) : ℝ)) (by positivity)).mul
            (hasNonnegCoeffs_X.pow _)).mul hrec

/-- Every active catalytic state has nonnegative coefficients. -/
theorem bellActive_hasNonnegCoeffs (j k : ℕ) :
    HasNonnegCoeffs (bellActive j k) := by
  apply (thresholdBell_hasNonnegCoeffs j k).derivative.add
  exact hasNonnegCoeffs_C_mul (by positivity)
    (thresholdBell_hasNonnegCoeffs j (k - j + 1))

/-- Every remainder catalytic state has nonnegative coefficients. -/
theorem bellRemainder_hasNonnegCoeffs (j k : ℕ) :
    HasNonnegCoeffs (bellRemainder j k) := by
  rw [bellRemainder]
  apply hasNonnegCoeffs_finsetSum
  intro r _
  exact hasNonnegCoeffs_C_mul (by positivity)
    (thresholdBell_hasNonnegCoeffs j (k - r))

/-- Every Pascal state has nonnegative coefficients. -/
theorem bellPascalState_hasNonnegCoeffs (j k i : ℕ) :
    HasNonnegCoeffs (bellPascalState j k i) := by
  rw [bellPascalState]
  apply hasNonnegCoeffs_finsetSum
  intro r _
  exact hasNonnegCoeffs_C_mul (by positivity)
    (thresholdBell_hasNonnegCoeffs j (k - r))

/-- Below the threshold window, the remainder is the terminal Pascal state. -/
theorem bellRemainder_eq_pascalState_of_le {j k : ℕ} (hk : k ≤ j - 2) :
    bellRemainder j k = bellPascalState j k k := by
  rw [bellRemainder, bellPascalState, min_eq_left hk]

/-- The shifted Vandermonde convolution needed to collect coefficients in the derivative
identity of issue #1990.  This is a direct specialization of Mathlib's upper-index
Vandermonde convolution. -/
theorem sum_choose_mul_choose_sub (k r j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (∑ i ∈ range k, i.choose r * (k - i - 1).choose (j - 1)) = k.choose (j + r) := by
  have hk : 1 ≤ k := hj.trans hjk
  rw [show j + r = 1 + (r + (j - 1)) by lia]
  simpa only [Nat.sub_add_cancel hk, Nat.sub_sub, Nat.add_comm, Nat.add_sub_cancel] using
    (Nat.sum_range_succ_choose_mul_choose (k - 1) r (j - 1))

/-- The zeroth Pascal state is the underlying threshold-Bell row. -/
@[simp]
theorem bellPascalState_zero (j k : ℕ) :
    bellPascalState j k 0 = thresholdBell j k := by
  simp [bellPascalState]

/-- Pascal states satisfy the two-dimensional Pascal recurrence, with negative indices
interpreted by truncated natural-number subtraction. -/
theorem bellPascalState_succ (j k i : ℕ) :
    bellPascalState j k (i + 1) =
      bellPascalState j k i + bellPascalState j (k - 1) i := by
  rw [bellPascalState, bellPascalState, bellPascalState]
  simp only [map_natCast]
  rw [sum_choose_succ_mul (R := ℝ[X])
    (fun r _ => thresholdBell j (k - r)) i]
  congr 1
  apply sum_congr rfl
  intro r _
  congr 2
  simp only [Nat.sub_sub]
  rw [Nat.add_comm]

/-- The forward half of the dense Ferrers endpoint criterion from issue #1990: an ordered PF
pair remains ordered after replacing it by its row sum and its `X`-weighted row sum. -/
theorem interl_add_X_mul_add_of_interl {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q) :
    Interl (p + q) (X * p + q) := by
  have hpXp : Interl p (X * p) :=
    (interl_iff_interl_X_mul hp hp).mp hp.interl_self
  have hqXp : Interl q (X * p) :=
    (interl_iff_interl_X_mul hp hq).mp hpq
  have hpout : Interl p (X * p + q) :=
    interl_add_right_of_common_left_of_nonneg hpXp hpq
      hp.X_mul.hasNonnegCoeffs hq.hasNonnegCoeffs
  have hqout : Interl q (X * p + q) :=
    interl_add_right_of_common_left_of_nonneg hqXp hq.interl_self
      hp.X_mul.hasNonnegCoeffs hq.hasNonnegCoeffs
  exact interl_add_left_of_common_right_of_nonneg hpout hqout
    hp.hasNonnegCoeffs hq.hasNonnegCoeffs

/-- Active/remainder interlacing implies the associated catalytic endpoint comparison. -/
theorem bellCatalyticEndpoints_interl_of_active_remainder
    (j k : ℕ) (hA : IsPFPolynomial (bellActive j k))
    (hR : IsPFPolynomial (bellRemainder j k))
    (hAR : Interl (bellActive j k) (bellRemainder j k)) :
    Interl (bellActive j k + bellRemainder j k)
      (X * bellActive j k + bellRemainder j k) :=
  interl_add_X_mul_add_of_interl hA hR hAR

/-- For threshold three, the first row is the constant polynomial one. -/
example : thresholdBell 3 1 = 1 := by
  norm_num [thresholdBell, Finset.sum_range_succ]

/-- For threshold three, the second row counts the two partitions with no large block. -/
example : thresholdBell 3 2 = 2 := by
  norm_num [thresholdBell, Finset.sum_range_succ]

/-- For threshold three, the third row is `4 + X`. -/
example : thresholdBell 3 3 = 4 + X := by
  norm_num [thresholdBell, Finset.sum_range_succ]

/-- For threshold three, the fourth row is `10 + 5 X`. -/
example : thresholdBell 3 4 = 10 + 5 * X := by
  norm_num [thresholdBell, Finset.sum_range_succ]
  ring

/-- At threshold three and rank three, the active state is the constant four. -/
theorem bellActive_three_three : bellActive 3 3 = 4 := by
  norm_num [bellActive, thresholdBell, Finset.sum_range_succ]
  norm_num [Polynomial.C_ofNat]

/-- At threshold three and rank three, the remainder state is `10 + X`. -/
theorem bellRemainder_three_three : bellRemainder 3 3 = 10 + X := by
  norm_num [bellRemainder, thresholdBell, Finset.sum_range_succ]
  ring

/-- The first nonconstant threshold-three active/remainder packet is ordered. -/
theorem bellActive_interl_bellRemainder_three_three :
    Interl (bellActive 3 3) (bellRemainder 3 3) := by
  rw [bellActive_three_three, bellRemainder_three_three]
  simpa [Polynomial.C_ofNat, Polynomial.C_1, add_comm] using
    (interl_C_affine_linear (c := 4) (u := 1) (v := 10) (by norm_num))

/-- At threshold three and rank three, the distinguished-block endpoint splits as `X A + R`. -/
theorem thresholdBell_four_eq_active_remainder :
    thresholdBell 3 4 = X * bellActive 3 3 + bellRemainder 3 3 := by
  rw [bellActive_three_three, bellRemainder_three_three]
  norm_num [thresholdBell, Finset.sum_range_succ]
  ring

end RealRooted
