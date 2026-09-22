import RealRooted.JacobiDeformation.AppellJacobiOperator
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialOperator

/-!
# Concrete Jacobi transport of the finite Appell kernel

This module uses ordinary univariate polynomial differentiation.  The library
Jacobi operator is the negative of the positive operator in the proof note.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The Bernstein monomial used in the concrete Jacobi transport. -/
def jacobiBernstein (i j : ℕ) : ℝ[X] := X ^ i * (1 - X) ^ j

/-- The library Jacobi operator on a Bernstein monomial.  It is the negative
of the positive `D` in the proof note, hence the three signs are reversed. -/
theorem jacobiDifferentialOperator_jacobiBernstein (c d : ℝ) (i j : ℕ) :
    jacobiDifferentialOperator c (c + d) (jacobiBernstein i j) =
      C ((i : ℝ) * ((i : ℝ) + c - 1)) * jacobiBernstein (i - 1) j +
        C ((j : ℝ) * ((j : ℝ) + d - 1)) * jacobiBernstein i (j - 1) -
          C (((i + j : ℕ) : ℝ) * ((i + j : ℕ) + c + d - 1)) *
            jacobiBernstein i j := by
  cases i with
  | zero =>
      cases j with
      | zero =>
          simp [jacobiBernstein, jacobiDifferentialOperator]
      | succ j =>
          cases j with
          | zero =>
              simp [jacobiBernstein, jacobiDifferentialOperator]
              ring
          | succ j =>
              simp [jacobiBernstein, jacobiDifferentialOperator, derivative_mul,
                derivative_pow]
              ring
  | succ i =>
      cases i with
      | zero =>
          cases j with
          | zero =>
              simp [jacobiBernstein, jacobiDifferentialOperator]
              ring
          | succ j =>
              cases j with
              | zero =>
                  norm_num [jacobiBernstein, jacobiDifferentialOperator,
                    derivative_mul]
                  rw [C_ofNat]
                  ring
              | succ j =>
                  simp [jacobiBernstein, jacobiDifferentialOperator, derivative_mul,
                    derivative_pow]
                  ring
      | succ i =>
          cases j with
          | zero =>
              simp [jacobiBernstein, jacobiDifferentialOperator, derivative_mul,
                derivative_pow]
              ring
          | succ j =>
              cases j with
              | zero =>
                  simp [jacobiBernstein, jacobiDifferentialOperator, derivative_mul,
                    derivative_pow]
                  ring
              | succ j =>
                  simp [jacobiBernstein, jacobiDifferentialOperator, derivative_mul,
                    derivative_pow]
                  ring

/-- The actual Appell kernel after fixing its second Jacobi coordinate. -/
def appellJacobiKernel (m : ℕ) (b c d z : ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    C (appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j) *
      jacobiBernstein i j

/-- Evaluating the fixed-coordinate ordinary polynomial recovers the actual
finite Appell kernel at `x = r*z`, `y = (1-r)*(1-z)`. -/
theorem eval_appellJacobiKernel (m : ℕ) (b c d r z : ℝ) :
    (appellJacobiKernel m b c d z).eval r =
      appellKernelValue m b c d (r * z) ((1 - r) * (1 - z)) := by
  unfold appellJacobiKernel appellKernelValue
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [eval_mul, eval_C, jacobiBernstein, eval_pow, eval_X, eval_sub,
    eval_one]
  rw [mul_pow, mul_pow]
  ring

/-- A coefficient beyond the finite Appell triangle is zero. -/
theorem appellKernelCoefficient_eq_zero_of_lt {m i j : ℕ} {b c d : ℝ}
    (hm : m < i + j) : appellKernelCoefficient m b c d i j = 0 := by
  simp [appellKernelCoefficient, Nat.not_le_of_lt hm]

private theorem sum_range_shift_aux (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f i) =
      f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- A finite sum can be shifted when its first and next-after-last terms
vanish.  This is the reindexing form needed for Appell lowering terms. -/
theorem sum_range_shift_of_boundary_zero (f : ℕ → ℝ) (n : ℕ)
    (hzero : f 0 = 0) (htop : f (n + 1) = 0) :
    (∑ i ∈ Finset.range (n + 1), f i) =
      ∑ i ∈ Finset.range (n + 1), f (i + 1) := by
  rw [sum_range_shift_aux, hzero, zero_add, Finset.sum_range_succ, htop,
    add_zero]

private theorem jacobiDifferentialOperator_finset_sum (a s : ℝ)
    (u : Finset ℕ) (f : ℕ → ℝ[X]) :
    jacobiDifferentialOperator a s (∑ i ∈ u, f i) =
      ∑ i ∈ u, jacobiDifferentialOperator a s (f i) := by
  induction u using Finset.induction_on with
  | empty => simp [jacobiDifferentialOperator_zero]
  | insert i u hi ih =>
      simp [hi, jacobiDifferentialOperator_add, ih]

private theorem jacobiBernstein_succ_left (i j : ℕ) :
    jacobiBernstein (i + 1) j = X * jacobiBernstein i j := by
  simp [jacobiBernstein, pow_succ]
  ring

private theorem jacobiBernstein_succ_right (i j : ℕ) :
    jacobiBernstein i (j + 1) = (1 - X) * jacobiBernstein i j := by
  simp [jacobiBernstein, pow_succ]
  ring

/-- Applying the actual library Jacobi operator to the fixed-coordinate kernel
is the finite sum of the three Bernstein action terms. -/
theorem jacobiDifferentialOperator_appellJacobiKernel (m : ℕ) (b c d z : ℝ) :
    jacobiDifferentialOperator c (c + d) (appellJacobiKernel m b c d z) =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        C (appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j) *
          (C ((i : ℝ) * ((i : ℝ) + c - 1)) * jacobiBernstein (i - 1) j +
            C ((j : ℝ) * ((j : ℝ) + d - 1)) * jacobiBernstein i (j - 1) -
              C (((i + j : ℕ) : ℝ) * ((i + j : ℕ) + c + d - 1)) *
                jacobiBernstein i j) := by
  rw [appellJacobiKernel, jacobiDifferentialOperator_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [jacobiDifferentialOperator_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [jacobiDifferentialOperator_C_mul,
    jacobiDifferentialOperator_jacobiBernstein]

private theorem iLowering_fixed_second_coordinate (m : ℕ) (b c d r z : ℝ)
    (j : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
          ((i : ℝ) * ((i : ℝ) + c - 1)) *
            (jacobiBernstein (i - 1) j).eval r) -
      (∑ i ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * r ^ i * (1 - r) ^ j *
          ((i : ℝ) * ((i : ℝ) + c - 1)) *
            (jacobiBernstein (i - 1) j).eval z) =
      (z - r) * ∑ i ∈ Finset.range (m + 1),
        appellLeftOperatorCoefficient m b c d i j * (r * z) ^ i *
          ((1 - r) * (1 - z)) ^ j := by
  let leftTerm : ℕ → ℝ := fun i =>
    appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
      ((i : ℝ) * ((i : ℝ) + c - 1)) * (jacobiBernstein (i - 1) j).eval r
  let rightTerm : ℕ → ℝ := fun i =>
    appellKernelCoefficient m b c d i j * r ^ i * (1 - r) ^ j *
      ((i : ℝ) * ((i : ℝ) + c - 1)) * (jacobiBernstein (i - 1) j).eval z
  have hleft_zero : leftTerm 0 = 0 := by simp [leftTerm]
  have hright_zero : rightTerm 0 = 0 := by simp [rightTerm]
  have hleft_top : leftTerm (m + 1) = 0 := by
    simp only [leftTerm]
    rw [show appellKernelCoefficient m b c d (m + 1) j = 0 by
      exact appellKernelCoefficient_eq_zero_of_lt (by lia)]
    ring
  have hright_top : rightTerm (m + 1) = 0 := by
    simp only [rightTerm]
    rw [show appellKernelCoefficient m b c d (m + 1) j = 0 by
      exact appellKernelCoefficient_eq_zero_of_lt (by lia)]
    ring
  have hleft := sum_range_shift_of_boundary_zero leftTerm m hleft_zero hleft_top
  have hright := sum_range_shift_of_boundary_zero rightTerm m hright_zero hright_top
  change (∑ i ∈ Finset.range (m + 1), leftTerm i) -
      ∑ i ∈ Finset.range (m + 1), rightTerm i = _
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [leftTerm, rightTerm, appellLeftOperatorCoefficient,
    Nat.add_sub_cancel, jacobiBernstein, eval_mul, eval_X,
    eval_pow, eval_sub, eval_one]
  rw [mul_pow, mul_pow]
  push_cast
  ring

private theorem jLowering_fixed_first_coordinate (m : ℕ) (b c d r z : ℝ)
    (i : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
          ((j : ℝ) * ((j : ℝ) + d - 1)) *
            (jacobiBernstein i (j - 1)).eval r) -
      (∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * r ^ i * (1 - r) ^ j *
          ((j : ℝ) * ((j : ℝ) + d - 1)) *
            (jacobiBernstein i (j - 1)).eval z) =
      (r - z) * ∑ j ∈ Finset.range (m + 1),
        appellRightOperatorCoefficient m b c d i j * (r * z) ^ i *
          ((1 - r) * (1 - z)) ^ j := by
  let leftTerm : ℕ → ℝ := fun j =>
    appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
      ((j : ℝ) * ((j : ℝ) + d - 1)) * (jacobiBernstein i (j - 1)).eval r
  let rightTerm : ℕ → ℝ := fun j =>
    appellKernelCoefficient m b c d i j * r ^ i * (1 - r) ^ j *
      ((j : ℝ) * ((j : ℝ) + d - 1)) * (jacobiBernstein i (j - 1)).eval z
  have hleft_zero : leftTerm 0 = 0 := by simp [leftTerm]
  have hright_zero : rightTerm 0 = 0 := by simp [rightTerm]
  have hleft_top : leftTerm (m + 1) = 0 := by
    simp only [leftTerm]
    rw [show appellKernelCoefficient m b c d i (m + 1) = 0 by
      exact appellKernelCoefficient_eq_zero_of_lt (by lia)]
    ring
  have hright_top : rightTerm (m + 1) = 0 := by
    simp only [rightTerm]
    rw [show appellKernelCoefficient m b c d i (m + 1) = 0 by
      exact appellKernelCoefficient_eq_zero_of_lt (by lia)]
    ring
  have hleft := sum_range_shift_of_boundary_zero leftTerm m hleft_zero hleft_top
  have hright := sum_range_shift_of_boundary_zero rightTerm m hright_zero hright_top
  change (∑ j ∈ Finset.range (m + 1), leftTerm j) -
      ∑ j ∈ Finset.range (m + 1), rightTerm j = _
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [leftTerm, rightTerm, appellRightOperatorCoefficient,
    Nat.add_sub_cancel, jacobiBernstein, eval_mul, eval_sub,
    eval_one, eval_pow, eval_X]
  rw [mul_pow, mul_pow]
  push_cast
  ring

private theorem iLowering_difference (m : ℕ) (b c d r z : ℝ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
          ((i : ℝ) * ((i : ℝ) + c - 1)) *
            (jacobiBernstein (i - 1) j).eval r) -
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * r ^ i * (1 - r) ^ j *
          ((i : ℝ) * ((i : ℝ) + c - 1)) *
            (jacobiBernstein (i - 1) j).eval z) =
      (z - r) * appellXOperatorValue m b c d (r * z) ((1 - r) * (1 - z)) := by
  conv_lhs =>
    congr
    · rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  unfold appellXOperatorValue
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Finset.mul_sum] using
    iLowering_fixed_second_coordinate m b c d r z j

private theorem jLowering_difference (m : ℕ) (b c d r z : ℝ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
          ((j : ℝ) * ((j : ℝ) + d - 1)) *
            (jacobiBernstein i (j - 1)).eval r) -
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * r ^ i * (1 - r) ^ j *
          ((j : ℝ) * ((j : ℝ) + d - 1)) *
            (jacobiBernstein i (j - 1)).eval z) =
      (r - z) * appellYOperatorValue m b c d (r * z) ((1 - r) * (1 - z)) := by
  rw [← Finset.sum_sub_distrib]
  unfold appellYOperatorValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact jLowering_fixed_first_coordinate m b c d r z i

private theorem eval_jacobiDifferentialOperator_appellJacobiKernel
    (m : ℕ) (b c d r z : ℝ) :
    (jacobiDifferentialOperator c (c + d) (appellJacobiKernel m b c d z)).eval r =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
          (((i : ℝ) * ((i : ℝ) + c - 1)) *
              (jacobiBernstein (i - 1) j).eval r +
            ((j : ℝ) * ((j : ℝ) + d - 1)) *
              (jacobiBernstein i (j - 1)).eval r -
            (((i + j : ℕ) : ℝ) * ((i + j : ℕ) + c + d - 1)) *
              (jacobiBernstein i j).eval r) := by
  rw [jacobiDifferentialOperator_appellJacobiKernel]
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [eval_mul, eval_add, eval_sub, eval_C]

private theorem eval_jacobiDifferentialOperator_appellJacobiKernel_split
    (m : ℕ) (b c d r z : ℝ) :
    (jacobiDifferentialOperator c (c + d) (appellJacobiKernel m b c d z)).eval r =
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
          ((i : ℝ) * ((i : ℝ) + c - 1)) *
            (jacobiBernstein (i - 1) j).eval r) +
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
          ((j : ℝ) * ((j : ℝ) + d - 1)) *
            (jacobiBernstein i (j - 1)).eval r) -
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
          (((i + j : ℕ) : ℝ) * ((i + j : ℕ) + c + d - 1)) *
            (jacobiBernstein i j).eval r) := by
  rw [eval_jacobiDifferentialOperator_appellJacobiKernel]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem diagonal_action_difference (m : ℕ) (b c d r z : ℝ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j *
          (((i + j : ℕ) : ℝ) * ((i + j : ℕ) + c + d - 1)) *
            (jacobiBernstein i j).eval r) -
      (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        appellKernelCoefficient m b c d i j * r ^ i * (1 - r) ^ j *
          (((i + j : ℕ) : ℝ) * ((i + j : ℕ) + c + d - 1)) *
            (jacobiBernstein i j).eval z) = 0 := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro j _
  simp only [jacobiBernstein, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  ring

/-- The actual finite Appell kernel has equal evaluated Jacobi differential
actions in its two coordinates. -/
theorem eval_jacobiDifferentialOperator_appellJacobiKernel_eq
    (m : ℕ) (b : ℝ) {c d r z : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (jacobiDifferentialOperator c (c + d) (appellJacobiKernel m b c d z)).eval r =
      (jacobiDifferentialOperator c (c + d) (appellJacobiKernel m b c d r)).eval z := by
  have hi := iLowering_difference m b c d r z
  have hj := jLowering_difference m b c d r z
  have hdiag := diagonal_action_difference m b c d r z
  have hres := appellJacobi_chainResidual_eq_zero m b hc hd (r := r) (z := z)
  unfold appellXOperatorValue at hi hres
  unfold appellYOperatorValue at hj hres
  rw [eval_jacobiDifferentialOperator_appellJacobiKernel_split,
    eval_jacobiDifferentialOperator_appellJacobiKernel_split]
  rw [← sub_eq_zero]
  linear_combination hi + hj - hdiag - hres

end RealRooted.JacobiDeformation
