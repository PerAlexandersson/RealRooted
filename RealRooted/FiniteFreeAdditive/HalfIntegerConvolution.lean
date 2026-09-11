import RealRooted.FiniteFreeAdditive.HalfInteger
import RealRooted.Mathlib.Algebra.Polynomial.Coeff
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Generalized half-integer additive convolution

This file defines the degree-boxed polynomial convolution associated with the
generalized rectangular Pochhammer kernel.  It proves its algebraic agreement
with the existing rectangular additive convolution at natural parameters.  It
does not assert a root-preservation result.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

private theorem sum_range_two_mul_add_one_eq_sum_range_two_mul {R : Type*}
    [AddCommMonoid R] (F : ℕ → R) (k : ℕ)
    (hodd : ∀ i, i ≤ 2 * k → Odd i → F i = 0) :
    (∑ i ∈ Finset.range (2 * k + 1), F i) =
      ∑ i ∈ Finset.range (k + 1), F (2 * i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hodd' : ∀ i, i ≤ 2 * k → Odd i → F i = 0 := by
        intro i hi
        exact hodd i (by lia)
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih hodd']
      rw [hodd (2 * k + 1) (by lia) (odd_two_mul_add_one k)]
      calc
        (∑ i ∈ Finset.range (k + 1), F (2 * i)) + 0 + F (2 * k + 2) =
            (∑ i ∈ Finset.range (k + 1), F (2 * i)) + F (2 * (k + 1)) := by
          rw [show 2 * k + 2 = 2 * (k + 1) by ring]
          simp
        _ = ∑ i ∈ Finset.range (k + 1 + 1), F (2 * i) :=
          (Finset.sum_range_succ _ _).symm

/-- The coefficient of generalized rectangular additive convolution in its
ambient degree box. -/
def generalizedRectangularConvolutionCoeff (α : ℝ) (n : ℕ) (p q : ℝ[X])
    (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    generalizedRectangularConvolutionGamma α n i (k - i) *
      p.coeff (n - i) * q.coeff (n - (k - i))

private theorem finiteFreeAdditiveConvolutionCoeff_evenLift_eq_generalized
    (n k : ℕ) (p q : ℝ[X]) (hk : k ≤ n) :
    finiteFreeAdditiveConvolutionCoeff (2 * n)
      (finiteFreeAdditiveEvenLift p) (finiteFreeAdditiveEvenLift q) (2 * k) =
      generalizedRectangularConvolutionCoeff (-(1 / 2 : ℝ)) n p q k := by
  unfold finiteFreeAdditiveConvolutionCoeff generalizedRectangularConvolutionCoeff
  rw [sum_range_two_mul_add_one_eq_sum_range_two_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hin : i ≤ n := hi'.trans hk
    have hkin : i + (k - i) ≤ n := by
      rw [Nat.add_sub_of_le hi']
      exact hk
    rw [show 2 * k - 2 * i = 2 * (k - i) by lia]
    rw [finiteFreeAdditiveConvolutionGamma_even_eq_generalized n i (k - i) hkin]
    rw [show 2 * n - 2 * i = 2 * (n - i) by lia]
    rw [show 2 * n - 2 * (k - i) = 2 * (n - (k - i)) by lia]
    rw [coeff_finiteFreeAdditiveEvenLift_two_mul,
      coeff_finiteFreeAdditiveEvenLift_two_mul]
  · intro i hi hodd
    have hi' : i ≤ 2 * k := hi.trans (by lia)
    have hin : i ≤ 2 * n := hi'.trans (by lia)
    have hdesc : Odd (2 * n - i) := by
      apply (Nat.odd_sub hin).mpr
      exact iff_of_false
        (Nat.not_odd_iff_even.mpr (even_two_mul n))
        (Nat.not_even_iff_odd.mpr hodd)
    rcases hdesc with ⟨r, hr⟩
    rw [hr, coeff_finiteFreeAdditiveEvenLift_two_mul_add_one]
    ring

private theorem finiteFreeAdditiveConvolutionCoeff_oddLift_eq_generalized
    (n k : ℕ) (p q : ℝ[X]) (hk : k ≤ n) :
    finiteFreeAdditiveConvolutionCoeff (2 * n + 1)
      (finiteFreeAdditiveOddLift p) (finiteFreeAdditiveOddLift q) (2 * k) =
      generalizedRectangularConvolutionCoeff (1 / 2 : ℝ) n p q k := by
  unfold finiteFreeAdditiveConvolutionCoeff generalizedRectangularConvolutionCoeff
  rw [sum_range_two_mul_add_one_eq_sum_range_two_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hkin : i + (k - i) ≤ n := by
      rw [Nat.add_sub_of_le hi']
      exact hk
    rw [show 2 * k - 2 * i = 2 * (k - i) by lia]
    rw [finiteFreeAdditiveConvolutionGamma_odd_eq_generalized n i (k - i) hkin]
    rw [show 2 * n + 1 - 2 * i = 2 * (n - i) + 1 by lia]
    rw [show 2 * n + 1 - 2 * (k - i) = 2 * (n - (k - i)) + 1 by lia]
    rw [coeff_finiteFreeAdditiveOddLift_two_mul_add_one,
      coeff_finiteFreeAdditiveOddLift_two_mul_add_one]
  · intro i hi hodd
    have hi' : i ≤ 2 * k := hi.trans (by lia)
    have hin : i ≤ 2 * n + 1 := hi'.trans (by lia)
    have hdesc : Even (2 * n + 1 - i) := by
      apply (Nat.even_sub hin).mpr
      exact iff_of_false
        (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one n))
        (Nat.not_even_iff_odd.mpr hodd)
    rw [coeff_finiteFreeAdditiveOddLift_of_even _ hdesc]
    ring

/-- Degree-`n` generalized rectangular additive convolution. -/
def generalizedRectangularAdditiveConvolution (α : ℝ) (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (generalizedRectangularConvolutionCoeff α n p q k) * X ^ (n - k)

/-- Coefficient extraction inside the generalized convolution's degree box. -/
theorem coeff_generalizedRectangularAdditiveConvolution_of_le (α : ℝ) (n : ℕ)
    (p q : ℝ[X]) {j : ℕ} (hj : j ≤ n) :
    (generalizedRectangularAdditiveConvolution α n p q).coeff j =
      generalizedRectangularConvolutionCoeff α n p q (n - j) := by
  unfold generalizedRectangularAdditiveConvolution
  rw [Polynomial.coeff_sum_range_C_mul_X_pow_sub]
  simp [hj]

/-- Coefficients outside the generalized convolution's degree box vanish. -/
theorem coeff_generalizedRectangularAdditiveConvolution_of_gt (α : ℝ) (n : ℕ)
    (p q : ℝ[X]) {j : ℕ} (hj : n < j) :
    (generalizedRectangularAdditiveConvolution α n p q).coeff j = 0 := by
  unfold generalizedRectangularAdditiveConvolution
  rw [Polynomial.coeff_sum_range_C_mul_X_pow_sub]
  simp [Nat.not_le.mpr hj]

/-- Generalized rectangular additive convolution stays in its degree box. -/
theorem natDegree_generalizedRectangularAdditiveConvolution_le (α : ℝ) (n : ℕ)
    (p q : ℝ[X]) :
    (generalizedRectangularAdditiveConvolution α n p q).natDegree ≤ n := by
  unfold generalizedRectangularAdditiveConvolution
  exact Polynomial.natDegree_sum_range_C_mul_X_pow_sub_le _ _

/-- At natural parameters, generalized rectangular additive convolution is the
existing rectangular additive convolution. -/
theorem generalizedRectangularAdditiveConvolution_nat_eq_rectangular (m n : ℕ)
    (p q : ℝ[X]) :
    generalizedRectangularAdditiveConvolution (m : ℝ) n p q =
      rectangularAdditiveConvolution m n p q := by
  unfold generalizedRectangularAdditiveConvolution rectangularAdditiveConvolution
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  unfold generalizedRectangularConvolutionCoeff rectangularConvolutionCoeff
  apply Finset.sum_congr rfl
  intro i hi
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hij : i + (k - i) ≤ n := by
    rw [Nat.add_sub_of_le hi']
    exact hk'
  rw [generalizedRectangularConvolutionGamma_nat_eq_rectangular m n i (k - i) hij]

/-- Finite-free additive convolution of even lifts is the even lift of the
generalized rectangular convolution at shift `-1 / 2`. -/
theorem finiteFreeAdditiveConvolution_evenLift_eq_generalized (n : ℕ) (p q : ℝ[X]) :
    finiteFreeAdditiveConvolution (2 * n)
      (finiteFreeAdditiveEvenLift p) (finiteFreeAdditiveEvenLift q) =
      finiteFreeAdditiveEvenLift
        (generalizedRectangularAdditiveConvolution (-(1 / 2 : ℝ)) n p q) := by
  ext j
  rcases Nat.even_or_odd j with hj | hj
  · rcases hj with ⟨r, rfl⟩
    rw [show r + r = 2 * r by ring]
    rw [coeff_finiteFreeAdditiveEvenLift_two_mul]
    by_cases hr : r ≤ n
    · rw [coeff_finiteFreeAdditiveConvolution_of_le _ _ _ (by lia)]
      rw [show 2 * n - 2 * r = 2 * (n - r) by lia]
      rw [finiteFreeAdditiveConvolutionCoeff_evenLift_eq_generalized n (n - r) p q
        (Nat.sub_le n r)]
      rw [coeff_generalizedRectangularAdditiveConvolution_of_le _ _ _ _ hr]
    · rw [coeff_finiteFreeAdditiveConvolution_of_gt _ _ _ (by lia)]
      rw [coeff_generalizedRectangularAdditiveConvolution_of_gt _ _ _ _ (by lia)]
  · rcases hj with ⟨r, rfl⟩
    rw [coeff_finiteFreeAdditiveEvenLift_two_mul_add_one]
    exact coeff_finiteFreeAdditiveConvolution_evenLift_even n r p q

/-- Finite-free additive convolution of odd lifts is the odd lift of the
generalized rectangular convolution at shift `1 / 2`. -/
theorem finiteFreeAdditiveConvolution_oddLift_eq_generalized (n : ℕ) (p q : ℝ[X]) :
    finiteFreeAdditiveConvolution (2 * n + 1)
      (finiteFreeAdditiveOddLift p) (finiteFreeAdditiveOddLift q) =
      finiteFreeAdditiveOddLift
        (generalizedRectangularAdditiveConvolution (1 / 2 : ℝ) n p q) := by
  ext j
  rcases Nat.even_or_odd j with hj | hj
  · rcases hj with ⟨r, rfl⟩
    rw [show r + r = 2 * r by ring]
    rw [coeff_finiteFreeAdditiveOddLift_of_even _ (even_two_mul r)]
    exact coeff_finiteFreeAdditiveConvolution_oddLift_odd n r p q
  · rcases hj with ⟨r, rfl⟩
    rw [coeff_finiteFreeAdditiveOddLift_two_mul_add_one]
    by_cases hr : r ≤ n
    · rw [coeff_finiteFreeAdditiveConvolution_of_le _ _ _ (by lia)]
      rw [show 2 * n + 1 - (2 * r + 1) = 2 * (n - r) by lia]
      rw [finiteFreeAdditiveConvolutionCoeff_oddLift_eq_generalized n (n - r) p q
        (Nat.sub_le n r)]
      rw [coeff_generalizedRectangularAdditiveConvolution_of_le _ _ _ _ hr]
    · rw [coeff_finiteFreeAdditiveConvolution_of_gt _ _ _ (by lia)]
      rw [coeff_generalizedRectangularAdditiveConvolution_of_gt _ _ _ _ (by lia)]

end

end RealRooted
