module

public import RealRooted.MultiplierSequence.TwoSidedJensen
public import RealRooted.MultiplierSequence.InvPochhammer
public import RealRooted.NarayanaTransformation.Interlacing
public import RealRooted.ReciprocalShift.ProperPosition
public import RealRooted.WagnerX.NonnegativeRoots

/-!
# Strict interlacing for hypergeometric Jensen models

This module records two reusable models used by several OEIS rows. The first
is the two-sided Jensen weight `4^k / (2k)!`. The second is the composition of
two order-zero Narayana transforms. It also supplies the degree-changing
reciprocal-shift transport needed when a row is written in reverse order.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The product of the reciprocal rising-factorial weights at `1 / 2` and `1`. -/
def evenFactorialJensenWeight (k : ℕ) : ℝ :=
  ((ascPochhammer ℝ k).eval (1 / 2))⁻¹ * ((k.factorial : ℝ))⁻¹

/-- The even-factorial Jensen weight is strictly positive. -/
theorem evenFactorialJensenWeight_pos (k : ℕ) :
    0 < evenFactorialJensenWeight k := by
  rw [evenFactorialJensenWeight]
  exact mul_pos
    (inv_pos.mpr (ascPochhammer_pos k (1 / 2) (by norm_num)))
    (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos k))

/-- The even-factorial Jensen weight is a multiplier sequence. -/
theorem evenFactorialJensenWeight_isMultiplierSequence :
    IsMultiplierSequence evenFactorialJensenWeight := by
  have hpf :=
    (isPFMultiplierSequence_inv_ascPochhammer (by norm_num : (0 : ℝ) < 1 / 2)).mul
      isPFMultiplierSequence_inv_factorial
  exact (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hpf).1

private theorem ascPochhammer_eval_one_half_mul_factorial_mul_four_pow (k : ℕ) :
    (ascPochhammer ℝ k).eval (1 / 2) * (k.factorial : ℝ) * 4 ^ k =
      ((2 * k).factorial : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [ascPochhammer_succ_eval, Nat.factorial_succ k,
        show 2 * (k + 1) = 2 * k + 2 by lia,
        Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k), pow_succ]
      push_cast
      ring_nf at ih ⊢
      linear_combination (4 * (k : ℝ) ^ 2 + 6 * (k : ℝ) + 2) * ih

/-- Factorial form of the even-factorial Jensen weight. -/
theorem evenFactorialJensenWeight_eq (k : ℕ) :
    evenFactorialJensenWeight k =
      (4 : ℝ) ^ k / (Nat.factorial (2 * k) : ℝ) := by
  rw [evenFactorialJensenWeight]
  have hfactor := ascPochhammer_eval_one_half_mul_factorial_mul_four_pow k
  have hpoch : (ascPochhammer ℝ k).eval (1 / 2) ≠ 0 :=
    (ascPochhammer_pos k (1 / 2) (by norm_num)).ne'
  have hfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have heven : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The double Narayana transform used by A318397. -/
def doubleNarayanaPolynomial (n : ℕ) : ℝ[X] :=
  narayanaTransform 0 (narayanaPolynomial 0 n)

private theorem choose_square_convolution (n j : ℕ) (hj : j ≤ n) :
    ∑ i ∈ Finset.range (n - j + 1),
        (n.choose (n - i)) ^ 2 * ((n - i).choose j) ^ 2 =
      (n.choose j) ^ 2 * (2 * (n - j)).choose (n - j) := by
  calc
    ∑ i ∈ Finset.range (n - j + 1),
        (n.choose (n - i)) ^ 2 * ((n - i).choose j) ^ 2 =
        ∑ i ∈ Finset.range (n - j + 1),
          (n.choose j) ^ 2 * ((n - j).choose i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            have hi' : i ≤ n - j := Finset.mem_range_succ_iff.mp hi
            have hji : j ≤ n - i := by lia
            have hmul := Nat.choose_mul (n := n) (k := n - i) (s := j) hji
            have hidx : n - i - j = n - j - i := by lia
            rw [hidx] at hmul
            have hsym := Nat.choose_symm hi'
            grind
    _ = (n.choose j) ^ 2 *
          ∑ i ∈ Finset.range (n - j + 1), ((n - j).choose i) ^ 2 := by
            rw [Finset.mul_sum]
    _ = (n.choose j) ^ 2 * (2 * (n - j)).choose (n - j) := by
            rw [Nat.sum_range_choose_sq]

/-- Coefficients of the double order-zero Narayana transform. -/
theorem coeff_doubleNarayanaPolynomial (n j : ℕ) :
    (doubleNarayanaPolynomial n).coeff j =
      (((n.choose j) ^ 2 * (2 * (n - j)).choose (n - j) : ℕ) : ℝ) := by
  by_cases hj : j ≤ n
  · rw [doubleNarayanaPolynomial, coeff_narayanaTransform,
      narayanaTransform_coeff_sum_reflect 0 n j (narayanaPolynomial 0 n)
        (natDegree_narayanaPolynomial_le 0 n) hj]
    calc
      ∑ i ∈ Finset.range (n - j + 1),
          (narayanaPolynomial 0 n).coeff (n - i) *
            narayanaTransformCoeff 0 (n - i) j =
          ∑ i ∈ Finset.range (n - j + 1),
            (((n.choose (n - i)) ^ 2 * ((n - i).choose j) ^ 2 : ℕ) : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hi' : i ≤ n - j := Finset.mem_range_succ_iff.mp hi
              have hni : n - i ≤ n := Nat.sub_le n i
              have hjni : j ≤ n - i := by lia
              rw [coeff_narayanaPolynomial_of_le hni]
              simp only [narayanaTransformCoeff]
              rw [show Nat.choose (0 + (n - i)) (n - i) = 1 by simp,
                show Nat.choose (0 + j) j = 1 by simp]
              grind
      _ = ((∑ i ∈ Finset.range (n - j + 1),
            (n.choose (n - i)) ^ 2 * ((n - i).choose j) ^ 2 : ℕ) : ℝ) := by
              simp
      _ = (((n.choose j) ^ 2 * (2 * (n - j)).choose (n - j) : ℕ) : ℝ) := by
              rw [choose_square_convolution n j hj]
  · have hnj : n < j := Nat.lt_of_not_ge hj
    rw [doubleNarayanaPolynomial, coeff_narayanaTransform]
    have hz : (narayanaPolynomial 0 n).sum
        (fun k a => a * (narayanaPolynomial 0 k).coeff j) = 0 := by
      rw [Polynomial.sum_def]
      apply Finset.sum_eq_zero
      intro k hk
      have hkn : k ≤ n := Polynomial.le_natDegree_of_mem_supp k hk |>.trans
        (natDegree_narayanaPolynomial_le 0 n)
      rw [coeff_narayanaPolynomial_of_lt (lt_of_le_of_lt hkn hnj), mul_zero]
    rw [hz, Nat.choose_eq_zero_of_lt hnj]
    simp

/-- Double Narayana rows have nonnegative coefficients. -/
theorem doubleNarayanaPolynomial_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (doubleNarayanaPolynomial n) := by
  exact (hasNonnegCoeffs_narayanaPolynomial 0 n).narayanaTransform

/-- Double Narayana rows are PF polynomials. -/
theorem doubleNarayanaPolynomial_isPF (n : ℕ) :
    IsPFPolynomial (doubleNarayanaPolynomial n) := by
  exact narayanaTransformPreservesPF 0 (narayanaPolynomialRootLocation 0 n)

/-- A double Narayana row has degree at most its row index. -/
theorem natDegree_doubleNarayanaPolynomial_le (n : ℕ) :
    (doubleNarayanaPolynomial n).natDegree ≤ n := by
  exact (natDegree_narayanaTransform_le 0 _).trans
    (natDegree_narayanaPolynomial_le 0 n)

/-- Consecutive double Narayana rows are in directed proper position. -/
theorem strictInterl_doubleNarayanaPolynomial_succ (n : ℕ) :
    StrictInterl (doubleNarayanaPolynomial n)
      (doubleNarayanaPolynomial (n + 1)) := by
  simpa only [doubleNarayanaPolynomial, narayanaTransform_X_pow] using
    strictInterl_narayanaTransform_narayanaTransform
      (strictInterl_X_pow_succ n)
      (hasNonnegCoeffs_X.pow n)
      (hasNonnegCoeffs_X.pow (n + 1)) 0 0

/-- Increasing the padding of a reciprocal shift inserts one factor of `X`. -/
theorem reciprocalShift_succ_eq_X_mul {D : ℕ} {p : ℝ[X]}
    (hdegree : p.natDegree ≤ D) :
    reciprocalShift (D + 1) p = X * reciprocalShift D p := by
  ext i
  cases i with
  | zero =>
      rw [reciprocalShift, Polynomial.coeff_reflect, Polynomial.revAt_zero,
        coeff_X_mul_zero]
      exact coeff_eq_zero_of_natDegree_lt (by lia)
  | succ i =>
      rw [reciprocalShift, Polynomial.coeff_reflect, coeff_X_mul,
        reciprocalShift, Polynomial.coeff_reflect]
      by_cases hi : i ≤ D
      · rw [Polynomial.revAt_le hi, Polynomial.revAt_le (by lia)]
        congr 1
        lia
      · rw [Polynomial.revAt_eq_self_of_lt (by lia),
          Polynomial.revAt_eq_self_of_lt (by lia)]
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree (by lia)),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree (by lia))]

/-- Reciprocal shifts at consecutive exact degree bounds preserve the
forward orientation of a PF interlacing pair. -/
theorem strictInterl_reciprocalShift_succ
    {n : ℕ} {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpd : p.natDegree ≤ n) (hqd : q.natDegree ≤ n + 1)
    (hpq : StrictInterl p q) :
    StrictInterl (reciprocalShift n p) (reciprocalShift (n + 1) q) := by
  have hreverse :
      StrictInterl (reciprocalShift (n + 1) q)
        (reciprocalShift (n + 1) p) :=
    reciprocalShift_reverses_strictInterl hp hq (hpd.trans (by lia)) hqd hpq
  rw [reciprocalShift_succ_eq_X_mul hpd] at hreverse
  exact strictInterl_of_strictInterl_X_mul_of_nonneg hreverse
    hp.hasNonnegCoeffs.reciprocalShift hq.hasNonnegCoeffs.reciprocalShift

/-- Consecutive degree-padded reciprocal double Narayana rows interlace. -/
theorem strictInterl_reciprocalShift_doubleNarayanaPolynomial_succ (n : ℕ) :
    StrictInterl
      (reciprocalShift n (doubleNarayanaPolynomial n))
      (reciprocalShift (n + 1) (doubleNarayanaPolynomial (n + 1))) := by
  exact strictInterl_reciprocalShift_succ
    (doubleNarayanaPolynomial_isPF n)
    (doubleNarayanaPolynomial_isPF (n + 1))
    (natDegree_doubleNarayanaPolynomial_le n)
    (natDegree_doubleNarayanaPolynomial_le (n + 1))
    (strictInterl_doubleNarayanaPolynomial_succ n)

end RealRooted
