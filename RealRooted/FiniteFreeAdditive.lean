import Mathlib.Tactic

/-!
# Finite-free additive convolution

This file fixes the degree-boxed coefficient normalization for the symmetric
finite-free additive convolution of Marcus--Spielman--Srivastava.  The raw
descending coefficients already absorb the conventional `(-1)^k` sign.  As
with the existing finite-free multiplicative operation, inputs are truncated
to the ambient degree box.  This file contains only algebraic identities;
real-rootedness preservation and the half-integer rectangular descent belong
to later layers.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

/-- The factorial weight in the degree-`d` symmetric finite-free additive
convolution. -/
def finiteFreeAdditiveConvolutionGamma (d i j : ℕ) : ℝ :=
  (Nat.factorial (d - i) : ℝ) * Nat.factorial (d - j) /
    ((Nat.factorial d : ℝ) * Nat.factorial (d - i - j))

/-- The finite-free additive-convolution weight is symmetric in its two
indices. -/
theorem finiteFreeAdditiveConvolutionGamma_symm (d i j : ℕ) :
    finiteFreeAdditiveConvolutionGamma d i j =
      finiteFreeAdditiveConvolutionGamma d j i := by
  unfold finiteFreeAdditiveConvolutionGamma
  rw [Nat.sub_right_comm d i j]
  ring

/-- The coefficient in degree-boxed finite-free additive convolution. -/
def finiteFreeAdditiveConvolutionCoeff (d : ℕ) (p q : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    finiteFreeAdditiveConvolutionGamma d i (k - i) *
      p.coeff (d - i) * q.coeff (d - (k - i))

/-- Degree-`d` symmetric finite-free additive convolution in the raw
descending-coefficient convention of Marcus--Spielman--Srivastava.  Terms
outside the degree-`d` input box do not contribute. -/
def finiteFreeAdditiveConvolution (d : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (finiteFreeAdditiveConvolutionCoeff d p q k) * X ^ (d - k)

/-- Coefficient extraction inside the ambient degree box. -/
theorem coeff_finiteFreeAdditiveConvolution_of_le (d : ℕ) (p q : ℝ[X])
    {j : ℕ} (hj : j ≤ d) :
    (finiteFreeAdditiveConvolution d p q).coeff j =
      finiteFreeAdditiveConvolutionCoeff d p q (d - j) := by
  unfold finiteFreeAdditiveConvolution
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem (d - j)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le d j)))]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Nat.sub_sub_self hj, if_pos rfl, mul_one]
  · intro k hk hkne
    have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hkne (by lia)), mul_zero]

/-- Coefficients outside the degree box vanish. -/
theorem coeff_finiteFreeAdditiveConvolution_of_gt (d : ℕ) (p q : ℝ[X])
    {j : ℕ} (hj : d < j) :
    (finiteFreeAdditiveConvolution d p q).coeff j = 0 := by
  unfold finiteFreeAdditiveConvolution
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    if_neg (fun h => by lia), mul_zero]

/-- Coefficients of finite-free additive convolution, with the ambient-degree
box made explicit. -/
theorem coeff_finiteFreeAdditiveConvolution (d j : ℕ) (p q : ℝ[X]) :
    (finiteFreeAdditiveConvolution d p q).coeff j =
      if j ≤ d then finiteFreeAdditiveConvolutionCoeff d p q (d - j) else 0 := by
  by_cases hj : j ≤ d
  · simp [hj, coeff_finiteFreeAdditiveConvolution_of_le d p q hj]
  · simp [hj, coeff_finiteFreeAdditiveConvolution_of_gt d p q (Nat.lt_of_not_ge hj)]

/-- Finite-free additive convolution stays in its ambient degree box. -/
theorem natDegree_finiteFreeAdditiveConvolution_le (d : ℕ) (p q : ℝ[X]) :
    (finiteFreeAdditiveConvolution d p q).natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  exact coeff_finiteFreeAdditiveConvolution_of_gt d p q hj

/-- The coefficient kernel of finite-free additive convolution is
commutative. -/
theorem finiteFreeAdditiveConvolutionCoeff_comm (d k : ℕ) (p q : ℝ[X]) :
    finiteFreeAdditiveConvolutionCoeff d p q k =
      finiteFreeAdditiveConvolutionCoeff d q p k := by
  unfold finiteFreeAdditiveConvolutionCoeff
  rw [← Finset.sum_range_reflect
    (fun i => finiteFreeAdditiveConvolutionGamma d i (k - i) *
      q.coeff (d - i) * p.coeff (d - (k - i))) (k + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [Nat.add_sub_cancel]
  rw [Nat.sub_sub_self hik,
    finiteFreeAdditiveConvolutionGamma_symm]
  ring

/-- Finite-free additive convolution is commutative. -/
theorem finiteFreeAdditiveConvolution_comm (d : ℕ) (p q : ℝ[X]) :
    finiteFreeAdditiveConvolution d p q = finiteFreeAdditiveConvolution d q p := by
  ext j
  by_cases hj : j ≤ d
  · rw [coeff_finiteFreeAdditiveConvolution_of_le d p q hj,
      coeff_finiteFreeAdditiveConvolution_of_le d q p hj,
      finiteFreeAdditiveConvolutionCoeff_comm]
  · have hj' : d < j := Nat.lt_of_not_ge hj
    rw [coeff_finiteFreeAdditiveConvolution_of_gt d p q hj',
      coeff_finiteFreeAdditiveConvolution_of_gt d q p hj']

/-- The even lift used by the finite-free additive-convolution parity
reduction. -/
def finiteFreeAdditiveEvenLift (p : ℝ[X]) : ℝ[X] :=
  Polynomial.expand ℝ 2 p

/-- The odd lift used by the finite-free additive-convolution parity
reduction. -/
def finiteFreeAdditiveOddLift (p : ℝ[X]) : ℝ[X] :=
  X * finiteFreeAdditiveEvenLift p

/-- The even lift preserves coefficients in even degree. -/
theorem coeff_finiteFreeAdditiveEvenLift_two_mul (p : ℝ[X]) (n : ℕ) :
    (finiteFreeAdditiveEvenLift p).coeff (2 * n) = p.coeff n := by
  simp [finiteFreeAdditiveEvenLift]

/-- The even lift has no coefficients in odd degree. -/
theorem coeff_finiteFreeAdditiveEvenLift_two_mul_add_one (p : ℝ[X]) (n : ℕ) :
    (finiteFreeAdditiveEvenLift p).coeff (2 * n + 1) = 0 := by
  rw [finiteFreeAdditiveEvenLift, Polynomial.coeff_expand (by norm_num)]
  simp

/-- The odd lift has zero constant coefficient. -/
theorem coeff_finiteFreeAdditiveOddLift_zero (p : ℝ[X]) :
    (finiteFreeAdditiveOddLift p).coeff 0 = 0 := by
  simp [finiteFreeAdditiveOddLift]

/-- The odd lift has no coefficients in positive even degree. -/
theorem coeff_finiteFreeAdditiveOddLift_two_mul_add_two (p : ℝ[X]) (n : ℕ) :
    (finiteFreeAdditiveOddLift p).coeff (2 * n + 2) = 0 := by
  rw [finiteFreeAdditiveOddLift]
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by lia,
    Polynomial.coeff_X_mul]
  exact coeff_finiteFreeAdditiveEvenLift_two_mul_add_one p n

/-- The odd lift preserves coefficients in odd degree. -/
theorem coeff_finiteFreeAdditiveOddLift_two_mul_add_one (p : ℝ[X]) (n : ℕ) :
    (finiteFreeAdditiveOddLift p).coeff (2 * n + 1) = p.coeff n := by
  rw [finiteFreeAdditiveOddLift]
  rw [show 2 * n + 1 = 2 * n + 1 by rfl, Polynomial.coeff_X_mul]
  exact coeff_finiteFreeAdditiveEvenLift_two_mul p n

end

end RealRooted
