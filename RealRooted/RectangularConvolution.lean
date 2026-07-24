import Mathlib.Tactic

/-!
# Rectangular additive convolution

This file defines the rectangular additive convolution of Gribinski--Marcus
and records its basic coefficient and degree formulas.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

/-- Gribinski--Marcus rectangular additive convolution coefficient. -/
def rectangularConvolutionGamma (m n i j : ℕ) : ℝ :=
  ((Nat.factorial (n - i) : ℝ) * (Nat.factorial (n - j) : ℝ) /
      ((Nat.factorial n : ℝ) * (Nat.factorial (n - i - j) : ℝ))) *
    ((Nat.factorial (n + m - i) : ℝ) * (Nat.factorial (n + m - j) : ℝ) /
      ((Nat.factorial (n + m) : ℝ) * (Nat.factorial (n + m - i - j) : ℝ)))

/-- The rectangular convolution coefficient is symmetric in its two indices. -/
theorem rectangularConvolutionGamma_symm (m n i j : ℕ) :
    rectangularConvolutionGamma m n i j = rectangularConvolutionGamma m n j i := by
  unfold rectangularConvolutionGamma
  rw [Nat.sub_right_comm n i j, Nat.sub_right_comm (n + m) i j]
  ring

/-- The coefficient used in the rectangular additive convolution. -/
def rectangularConvolutionCoeff (m n : ℕ) (f g : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    rectangularConvolutionGamma m n i (k - i) *
      f.coeff (n - i) * g.coeff (n - (k - i))

/-- Rectangular additive convolution in the coefficient convention of
Mao--Wang, Eq. (2.3). -/
def rectangularAdditiveConvolution (m n : ℕ) (f g : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (rectangularConvolutionCoeff m n f g k) * X ^ (n - k)

/-- Coefficient extraction for the rectangular additive convolution. -/
theorem coeff_rectangularAdditiveConvolution_of_le (m n : ℕ) (f g : ℝ[X])
    {j : ℕ} (hj : j ≤ n) :
    (rectangularAdditiveConvolution m n f g).coeff j =
      rectangularConvolutionCoeff m n f g (n - j) := by
  unfold rectangularAdditiveConvolution
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem (n - j)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le n j)))]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Nat.sub_sub_self hj,
      if_pos rfl, mul_one]
  · intro k hk hkne
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun hjk => hkne (by lia)), mul_zero]

/-- The rectangular additive convolution has no coefficients above degree `n`. -/
theorem coeff_rectangularAdditiveConvolution_of_gt (m n : ℕ) (f g : ℝ[X])
    {j : ℕ} (hj : n < j) :
    (rectangularAdditiveConvolution m n f g).coeff j = 0 := by
  unfold rectangularAdditiveConvolution
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun hjk => by lia),
    mul_zero]

/-- The rectangular additive convolution has degree at most `n`. -/
theorem natDegree_rectangularAdditiveConvolution_le (m n : ℕ) (f g : ℝ[X]) :
    (rectangularAdditiveConvolution m n f g).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_rectangularAdditiveConvolution_of_gt m n f g hk

end

end RealRooted
