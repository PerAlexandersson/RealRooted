import RealRooted.Basic.Coefficients
import RealRooted.DerivativeRecurrence.QuadraticDegree
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# A144696 row polynomials and Bernstein images

This file defines the A144696 differential-recurrence polynomials and the
linear basis transform that sends `X ^ n` to the `n`th row polynomial. Its
images of `X ^ k * (1 + X) ^ (d - k)` are the Bernstein-image rows used in
the interval-root preservation argument.

Only finite polynomial algebra is developed here. The strict interlacing and
residue estimates belong to later modules.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted

private theorem coeff_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ[X]) (j : ℕ) :
    (∑ i ∈ s, f i).coeff j = ∑ i ∈ s, (f i).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, coeff_add]

/-- The degree-`n` row polynomial of OEIS A144696. -/
def a144696Polynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (1 + C ((n + 2 : ℕ) : ℝ) * X) * a144696Polynomial n +
        X * (1 - X) * (a144696Polynomial n).derivative

@[simp] theorem a144696Polynomial_zero :
    a144696Polynomial 0 = 1 :=
  rfl

/-- The defining differential recurrence for the A144696 rows. -/
theorem a144696Polynomial_succ (n : ℕ) :
    a144696Polynomial (n + 1) =
      (1 + C ((n + 2 : ℕ) : ℝ) * X) * a144696Polynomial n +
        X * (1 - X) * (a144696Polynomial n).derivative := by
  rfl

/-- The defining recurrence with its index term separated. -/
theorem a144696Polynomial_succ_index (n : ℕ) :
    a144696Polynomial (n + 1) =
      (1 + C 2 * X) * a144696Polynomial n +
        X * (C (n : ℝ) * a144696Polynomial n) +
        (X * (1 - X)) * (a144696Polynomial n).derivative := by
  rw [a144696Polynomial_succ]
  push_cast
  simp only [map_add]
  norm_num
  ring

private theorem a144696Polynomial_succ_scaled_shift (n : ℕ) :
    a144696Polynomial (n + 1) =
      (C 1 * X + C (-1) * X ^ 2) * (a144696Polynomial n).derivative +
        (C 1 + C (2 + (n : ℝ)) * X) * a144696Polynomial n := by
  rw [a144696Polynomial_succ]
  push_cast
  simp only [map_add]
  norm_num
  ring

/-- The `n`th A144696 row polynomial has degree exactly `n`. -/
theorem natDegree_a144696Polynomial (n : ℕ) :
    (a144696Polynomial n).natDegree = n := by
  exact natDegree_of_quadratic_derivative_shift
    a144696Polynomial 2 a144696Polynomial_zero
      a144696Polynomial_succ_scaled_shift (by norm_num) n

/-- The leading coefficient of the `n`th A144696 row is `2 ^ n`. -/
theorem leadingCoeff_a144696Polynomial (n : ℕ) :
    (a144696Polynomial n).leadingCoeff = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [leadingCoeff, natDegree_a144696Polynomial,
        quadratic_derivative_shift_coeff_succ
          a144696Polynomial 2 a144696Polynomial_succ_scaled_shift]
      have habove : (a144696Polynomial n).coeff (n + 1) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_a144696Polynomial]
        lia
      have ihcoeff : (a144696Polynomial n).coeff n = 2 ^ n := by
        calc
          (a144696Polynomial n).coeff n =
              (a144696Polynomial n).coeff (a144696Polynomial n).natDegree := by
                rw [natDegree_a144696Polynomial]
          _ = (a144696Polynomial n).leadingCoeff := coeff_natDegree
          _ = 2 ^ n := ih
      rw [habove, ihcoeff]
      ring

/-- Every A144696 row has constant coefficient one. -/
@[simp] theorem coeff_zero_a144696Polynomial (n : ℕ) :
    (a144696Polynomial n).coeff 0 = 1 := by
  induction n with
  | zero => simp [a144696Polynomial]
  | succ n ih => simp [a144696Polynomial_succ, ih]

/-- Coefficient recurrence for the A144696 rows. -/
theorem coeff_succ_a144696Polynomial (n k : ℕ) :
    (a144696Polynomial (n + 1)).coeff (k + 1) =
      ((k : ℝ) + 2) * (a144696Polynomial n).coeff (k + 1) +
        (2 + (n : ℝ) - (k : ℝ)) * (a144696Polynomial n).coeff k := by
  exact quadratic_derivative_shift_coeff_succ
    a144696Polynomial 2 a144696Polynomial_succ_scaled_shift n k

/-- Every coefficient of an A144696 row is nonnegative. -/
theorem hasNonnegCoeffs_a144696Polynomial (n : ℕ) :
    HasNonnegCoeffs (a144696Polynomial n) := by
  induction n with
  | zero => simpa [a144696Polynomial] using hasNonnegCoeffs_one
  | succ n ih =>
      intro j
      cases j with
      | zero => simp
      | succ k =>
          rw [coeff_succ_a144696Polynomial]
          by_cases hk : k ≤ n
          · have hkR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
            have hfactor : 0 ≤ 2 + (n : ℝ) - (k : ℝ) := by linarith
            exact add_nonneg
              (mul_nonneg (by positivity) (ih (k + 1)))
              (mul_nonneg hfactor (ih k))
          · have hkdeg : (a144696Polynomial n).coeff k = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              rw [natDegree_a144696Polynomial]
              lia
            have hksuccdeg : (a144696Polynomial n).coeff (k + 1) = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              rw [natDegree_a144696Polynomial]
              lia
            rw [hkdeg, hksuccdeg]
            simp

/-- Coefficients through the degree of an A144696 row are strictly positive. -/
theorem coeff_pos_a144696Polynomial {n k : ℕ} (hk : k ≤ n) :
    0 < (a144696Polynomial n).coeff k := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by lia
      subst k
      simp [a144696Polynomial]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [coeff_succ_a144696Polynomial]
          have hkn : k ≤ n := by lia
          have hkR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
          have hfactor : 0 < 2 + (n : ℝ) - (k : ℝ) := by linarith
          exact add_pos_of_nonneg_of_pos
            (mul_nonneg (by positivity)
              (hasNonnegCoeffs_a144696Polynomial n (k + 1)))
            (mul_pos hfactor (ih hkn))

/-- Evaluation of the `n`th A144696 row at one. -/
theorem eval_one_a144696Polynomial (n : ℕ) :
    (a144696Polynomial n).eval 1 = (Nat.factorial (n + 2) : ℝ) / 2 := by
  induction n with
  | zero => norm_num [a144696Polynomial]
  | succ n ih =>
      rw [a144696Polynomial_succ]
      simp [ih, Nat.factorial_succ]
      ring

/-- The linear coefficient-basis transform sending `X ^ n` to the `n`th
A144696 row polynomial. -/
def a144696Transform (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform a144696Polynomial p

@[simp] theorem a144696Transform_X_pow (n : ℕ) :
    a144696Transform (X ^ n) = a144696Polynomial n := by
  exact Polynomial.basisTransform_X_pow a144696Polynomial n

theorem a144696Transform_add (p q : ℝ[X]) :
    a144696Transform (p + q) = a144696Transform p + a144696Transform q := by
  exact Polynomial.basisTransform_add a144696Polynomial p q

theorem a144696Transform_C_mul (a : ℝ) (p : ℝ[X]) :
    a144696Transform (C a * p) = C a * a144696Transform p := by
  rw [show C a * p = a • p by rw [Polynomial.smul_eq_C_mul],
    a144696Transform, Polynomial.basisTransform_smul]
  rfl

/-- Multiplication by `X` under the A144696 basis transform. -/
theorem a144696Transform_X_mul (p : ℝ[X]) :
    a144696Transform (X * p) =
      (1 + C 2 * X) * a144696Transform p +
        X * a144696Transform (X * p.derivative) +
        X * (1 - X) * (a144696Transform p).derivative := by
  exact Polynomial.basisTransform_X_mul_of_succ_index_derivative
    a144696Polynomial (1 + C 2 * X) X (X * (1 - X))
      a144696Polynomial_succ_index p

/-- The image of the degree-`d` Bernstein basis element indexed by `k`. -/
def a144696BernsteinImage (d k : ℕ) : ℝ[X] :=
  a144696Transform (X ^ k * (1 + X) ^ (d - k))

/-- Explicit binomial sum for an A144696 Bernstein image. -/
theorem a144696BernsteinImage_eq_sum (d k : ℕ) :
    a144696BernsteinImage d k =
      ∑ i ∈ Finset.range (d - k + 1),
        C (Nat.choose (d - k) i : ℝ) * a144696Polynomial (k + i) := by
  have hpow :
      ((1 + X : ℝ[X]) ^ (d - k)) =
        ∑ i ∈ Finset.range (d - k + 1),
          C (Nat.choose (d - k) i : ℝ) * X ^ i := by
    rw [show (1 + X : ℝ[X]) = X + 1 by ring, add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    simp
    ring
  rw [a144696BernsteinImage, hpow, Finset.mul_sum,
    a144696Transform, Polynomial.basisTransform_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show X ^ k * (C (Nat.choose (d - k) i : ℝ) * X ^ i) =
      C (Nat.choose (d - k) i : ℝ) * X ^ (k + i) by
        rw [pow_add]
        ring]
  exact Polynomial.basisTransform_C_mul_X_pow
    a144696Polynomial (Nat.choose (d - k) i : ℝ) (k + i)

/-- Every Bernstein image has nonnegative coefficients. -/
theorem hasNonnegCoeffs_a144696BernsteinImage (d k : ℕ) :
    HasNonnegCoeffs (a144696BernsteinImage d k) := by
  intro j
  rw [a144696BernsteinImage_eq_sum, coeff_finset_sum]
  simp only [coeff_C_mul]
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (by positivity) (hasNonnegCoeffs_a144696Polynomial (k + i) j)

/-- Every coefficient through degree `d` of an in-range Bernstein image is
strictly positive. -/
theorem coeff_pos_a144696BernsteinImage
    {d k j : ℕ} (hk : k ≤ d) (hj : j ≤ d) :
    0 < (a144696BernsteinImage d k).coeff j := by
  rw [a144696BernsteinImage_eq_sum, coeff_finset_sum]
  simp only [coeff_C_mul]
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (by positivity)
      (hasNonnegCoeffs_a144696Polynomial (k + i) j)
  · refine ⟨d - k, Finset.mem_range.mpr (by lia), ?_⟩
    rw [Nat.choose_self, Nat.cast_one, one_mul, Nat.add_sub_of_le hk]
    exact coeff_pos_a144696Polynomial hj

/-- Every in-range Bernstein image has degree exactly `d`. -/
theorem natDegree_a144696BernsteinImage
    {d k : ℕ} (hk : k ≤ d) :
    (a144696BernsteinImage d k).natDegree = d := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [a144696BernsteinImage_eq_sum]
    refine natDegree_sum_le_of_forall_le (Finset.range (d - k + 1))
      (fun i => C (Nat.choose (d - k) i : ℝ) *
        a144696Polynomial (k + i)) ?_
    intro i hi
    calc
      (C (Nat.choose (d - k) i : ℝ) *
          a144696Polynomial (k + i)).natDegree ≤
          (a144696Polynomial (k + i)).natDegree := natDegree_C_mul_le _ _
      _ = k + i := natDegree_a144696Polynomial (k + i)
      _ ≤ d := by
        have hirange : i < d - k + 1 := Finset.mem_range.mp hi
        have hi' : i ≤ d - k := by lia
        lia
  · exact (coeff_pos_a144696BernsteinImage hk le_rfl).ne'

/-- Every in-range Bernstein image has leading coefficient `2 ^ d`. -/
theorem leadingCoeff_a144696BernsteinImage
    {d k : ℕ} (hk : k ≤ d) :
    (a144696BernsteinImage d k).leadingCoeff = 2 ^ d := by
  rw [leadingCoeff, natDegree_a144696BernsteinImage hk,
    a144696BernsteinImage_eq_sum, coeff_finset_sum]
  rw [Finset.sum_eq_single (d - k)]
  · rw [coeff_C_mul, Nat.choose_self, Nat.cast_one, one_mul,
      Nat.add_sub_of_le hk]
    calc
      (a144696Polynomial d).coeff d =
          (a144696Polynomial d).coeff (a144696Polynomial d).natDegree := by
            rw [natDegree_a144696Polynomial]
      _ = (a144696Polynomial d).leadingCoeff := coeff_natDegree
      _ = 2 ^ d := leadingCoeff_a144696Polynomial d
  · intro i hi hne
    rw [coeff_C_mul]
    have hi' : i < d - k := by
      have hirange : i < d - k + 1 := Finset.mem_range.mp hi
      have hile : i ≤ d - k := by lia
      exact lt_of_le_of_ne hile hne
    have hcoeff : (a144696Polynomial (k + i)).coeff d = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_a144696Polynomial]
      lia
    rw [hcoeff, mul_zero]
  · simp

/-- The diagonal Bernstein image is the original row polynomial. -/
@[simp] theorem a144696BernsteinImage_diagonal (d : ℕ) :
    a144696BernsteinImage d d = a144696Polynomial d := by
  simp [a144696BernsteinImage]

private theorem bernsteinBasis_pascal {d k : ℕ} (hk : k < d) :
    (X ^ k * (1 + X) ^ (d - k) : ℝ[X]) =
      X ^ k * (1 + X) ^ (d - 1 - k) +
        X ^ (k + 1) * (1 + X) ^ (d - (k + 1)) := by
  have hsub : d - k = (d - 1 - k) + 1 := by lia
  have hsub' : d - (k + 1) = d - 1 - k := by lia
  rw [hsub, hsub', pow_succ]
  ring

/-- Pascal relation between adjacent Bernstein images. -/
theorem a144696BernsteinImage_pascal {d k : ℕ} (hk : k < d) :
    a144696BernsteinImage d k =
      a144696BernsteinImage (d - 1) k +
        a144696BernsteinImage d (k + 1) := by
  rw [a144696BernsteinImage, bernsteinBasis_pascal hk,
    a144696Transform, Polynomial.basisTransform_add]
  rfl

private theorem X_mul_derivative_bernsteinBasis
    {d k : ℕ} (hk : k ≤ d) :
    X * (X ^ k * (1 + X) ^ (d - k) : ℝ[X]).derivative =
      C (k : ℝ) * (X ^ k * (1 + X) ^ (d - k)) +
        C ((d - k : ℕ) : ℝ) *
          (X ^ (k + 1) * (1 + X) ^ (d - (k + 1))) := by
  by_cases hk0 : k = 0
  · subst k
    simp only [pow_zero, one_mul, zero_add, Nat.sub_zero]
    rw [derivative_pow, derivative_add, derivative_one, derivative_X]
    simp
    ring
  rw [derivative_mul, derivative_pow, derivative_pow, derivative_X,
    derivative_add, derivative_one, derivative_X]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hsub : d - (k + 1) = d - k - 1 := by lia
  have hx : (X : ℝ[X]) * X ^ (k - 1) = X ^ k := by
    rw [← pow_succ']
    congr 1
    lia
  rw [hsub]
  simp only [mul_one, zero_add]
  rw [pow_succ]
  calc
    X * (C (k : ℝ) * X ^ (k - 1) * (1 + X) ^ (d - k) +
        X ^ k * (C ((d - k : ℕ) : ℝ) * (1 + X) ^ (d - k - 1))) =
      C (k : ℝ) * (X * X ^ (k - 1)) * (1 + X) ^ (d - k) +
        C ((d - k : ℕ) : ℝ) *
          (X ^ k * X * (1 + X) ^ (d - k - 1)) := by ring
    _ = _ := by
      rw [hx]
      ring

/-- Differential recurrence for adjacent Bernstein images. -/
theorem a144696BernsteinImage_succ
    {d k : ℕ} (hk : k ≤ d) :
    a144696BernsteinImage (d + 1) (k + 1) =
      (1 + C ((k + 2 : ℕ) : ℝ) * X) * a144696BernsteinImage d k +
        C ((d - k : ℕ) : ℝ) * X * a144696BernsteinImage d (k + 1) +
        X * (1 - X) * (a144696BernsteinImage d k).derivative := by
  have hsub : d + 1 - (k + 1) = d - k := by lia
  rw [a144696BernsteinImage, hsub, pow_succ]
  rw [show X ^ k * X * (1 + X) ^ (d - k) =
      (X : ℝ[X]) * (X ^ k * (1 + X) ^ (d - k)) by ring]
  rw [a144696Transform_X_mul, X_mul_derivative_bernsteinBasis hk,
    a144696Transform_add, a144696Transform_C_mul,
    a144696Transform_C_mul]
  change
    (1 + C 2 * X) * a144696BernsteinImage d k +
          X * (C (k : ℝ) * a144696BernsteinImage d k +
            C ((d - k : ℕ) : ℝ) * a144696BernsteinImage d (k + 1)) +
        X * (1 - X) * (a144696BernsteinImage d k).derivative = _
  push_cast
  simp only [map_add]
  ring

/-- The auxiliary degree-dropping polynomial in the A144696 residue step. -/
def a144696Auxiliary (d k : ℕ) : ℝ[X] :=
  (1 - X) * (a144696BernsteinImage d k).derivative +
    C ((d - k : ℕ) : ℝ) * a144696BernsteinImage d (k + 1) +
    C (k : ℝ) * a144696BernsteinImage d k

/-- The successor Bernstein image as an affine combination of its predecessor
and the auxiliary polynomial. -/
theorem a144696BernsteinImage_succ_eq_auxiliary
    {d k : ℕ} (hk : k ≤ d) :
    a144696BernsteinImage (d + 1) (k + 1) =
      (1 + C 2 * X) * a144696BernsteinImage d k +
        X * a144696Auxiliary d k := by
  rw [a144696BernsteinImage_succ hk, a144696Auxiliary]
  push_cast
  simp only [map_add]
  ring

end RealRooted
