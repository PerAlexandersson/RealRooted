import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import RealRooted.JacobiDeformation.Basic
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.DifferentialOperator

/-!
# The finite Appell kernel and its Jacobi transport

With `b = m + s - 1 + δ`, the finite Appell kernel is

`G(x, y) = (-1) ^ m ∑_{i + j ≤ m} (-m)_{i + j} (b)_{i + j} / ((c)_i (d)_j i! j!) ·
  x ^ i y ^ j`,

stored by its coefficient array `appellKernelCoefficient`.  It satisfies
`x G_xx + c G_x = y G_yy + d G_y` coefficientwise.  Substituting
`x = r z` and `y = (1 - r)(1 - z)`, the chain rule turns this into equality of
the two shifted-Jacobi differential operators acting in `r` and in `z` on the
kernel `K_δ(r, z) = G(r z, (1 - r)(1 - z))` (`appellJacobiKernel` is its
polynomial in `r` for fixed `z`).  Hence the
expansion of `K_δ` in a Jacobi eigenbasis is diagonal
(`RealRooted.JacobiDeformation.KernelExpansion`).

The last two sections identify the kernel with the Jacobi deformation: its
evaluation at the scalar coordinates attached to an image value `ξ` is the
deformation polynomial evaluated at `ξ`.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## The finite Appell coefficient identity

A coefficient array is used deliberately: it is the smallest representation
needed for the finite Appell calculation.
-/

/-- The coefficient of `x^i y^j` in the finite Appell kernel.
It is zero outside the triangle `i + j ≤ m`. -/
def appellKernelCoefficient (m : ℕ) (b c d : ℝ) (i j : ℕ) : ℝ :=
  if i + j ≤ m then
    (-1 : ℝ) ^ m * risingFactorial (-(m : ℝ)) (i + j) *
        risingFactorial b (i + j) /
      (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial)
  else 0

/-- The `xGₓₓ + cGₓ` coefficient of the finite Appell kernel. -/
def appellLeftOperatorCoefficient (m : ℕ) (b c d : ℝ) (i j : ℕ) : ℝ :=
  ((i : ℝ) + 1) * ((i : ℝ) + c) * appellKernelCoefficient m b c d (i + 1) j

/-- The `yGᵧᵧ + dGᵧ` coefficient of the finite Appell kernel. -/
def appellRightOperatorCoefficient (m : ℕ) (b c d : ℝ) (i j : ℕ) : ℝ :=
  ((j : ℝ) + 1) * ((j : ℝ) + d) * appellKernelCoefficient m b c d i (j + 1)

/-- The finite Appell coefficients satisfy the recurrence obtained by
coefficientwise differentiation of the two-variable kernel. -/
theorem appellKernelCoefficient_recurrence {m i j : ℕ} {b c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hijm : i + j + 1 ≤ m) :
    appellLeftOperatorCoefficient m b c d i j =
      appellRightOperatorCoefficient m b c d i j := by
  have hil : i + 1 + j ≤ m := by lia
  have hjr : i + (j + 1) ≤ m := by lia
  have hci : risingFactorial c i ≠ 0 := (risingFactorial_pos i hc).ne'
  have hdj : risingFactorial d j ≠ 0 := (risingFactorial_pos j hd).ne'
  have hci_add : (i : ℝ) + c ≠ 0 := by positivity
  have hdj_add : (j : ℝ) + d ≠ 0 := by positivity
  simp only [appellLeftOperatorCoefficient, appellRightOperatorCoefficient,
    appellKernelCoefficient, hil, hjr, ite_true]
  rw [risingFactorial_succ c i, risingFactorial_succ d j]
  norm_num [Nat.factorial_succ]
  field_simp [hci, hdj, hci_add, hdj_add]
  ring_nf

/-- The finite Appell kernel has equal coefficients after the two
Jacobi operator actions.  This is the finite identity
`xGₓₓ + cGₓ = yGᵧᵧ + dGᵧ`. -/
theorem appellKernel_operator_coefficient_identity (m : ℕ) (b : ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (i j : ℕ) :
    appellLeftOperatorCoefficient m b c d i j =
      appellRightOperatorCoefficient m b c d i j := by
  by_cases hijm : i + j + 1 ≤ m
  · exact appellKernelCoefficient_recurrence hc hd hijm
  · have hil : ¬(i + 1 + j ≤ m) := by lia
    have hjr : ¬(i + (j + 1) ≤ m) := by lia
    simp [appellLeftOperatorCoefficient, appellRightOperatorCoefficient,
      appellKernelCoefficient, hil, hjr]

/-! ## The scalar Appell boundary coefficient

We simplify the `i = 0` coefficient of the finite Appell kernel without
imposing positivity on the remaining denominator parameter.
-/

/-- The `i = 0` Appell coefficient has the signed binomial--Pochhammer form
inside the finite triangle. -/
theorem appellKernelCoefficient_zero_left (m j : ℕ) (b c d : ℝ) (hj : j ≤ m) :
    appellKernelCoefficient m b c d 0 j =
      (-1 : ℝ) ^ (m + j) * (m.choose j : ℝ) * risingFactorial b j /
        risingFactorial d j := by
  have hdesc : (m.descFactorial j : ℝ) =
      (j.factorial : ℝ) * (m.choose j : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose m j
  have hfactorial : (j.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  rw [appellKernelCoefficient]
  simp only [show 0 + j ≤ m by simpa using hj, ↓reduceIte]
  simp only [zero_add, risingFactorial_zero, Nat.factorial_zero, Nat.cast_one,
    one_mul, mul_one]
  rw [risingFactorial_neg_natCast, hdesc]
  calc
    (-1 : ℝ) ^ m * ((-1 : ℝ) ^ j * ((j.factorial : ℝ) * (m.choose j : ℝ))) *
          risingFactorial b j /
        (risingFactorial d j * (j.factorial : ℝ)) =
      (((-1 : ℝ) ^ m * (-1 : ℝ) ^ j * (m.choose j : ℝ) *
          risingFactorial b j) * (j.factorial : ℝ)) /
        (risingFactorial d j * (j.factorial : ℝ)) := by ring
    _ = (-1 : ℝ) ^ m * (-1 : ℝ) ^ j * (m.choose j : ℝ) *
          risingFactorial b j / risingFactorial d j := by
      rw [mul_div_mul_right _ _ hfactorial]
    _ = (-1 : ℝ) ^ (m + j) * (m.choose j : ℝ) * risingFactorial b j /
          risingFactorial d j := by
      rw [← pow_add]

/-! ## Appell residual at Jacobi coordinates

We evaluate the finite Appell residual at `x = r * z`,
`y = (1 - r) * (1 - z)`.  The resulting zero is the right-hand side of the
chain-rule identity
`(D_r - D_z) G(r z, (1 - r)(1 - z)) = (r - z)(x G_xx + c G_x - y G_yy - d G_y)`
for the two Jacobi operator actions.
-/

/-- The finite Appell kernel, viewed as a finite polynomial function of
its two independent coordinates. -/
def appellKernelValue (m : ℕ) (b c d x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    appellKernelCoefficient m b c d i j * x ^ i * y ^ j

/-- The coefficient form of `xGₓₓ + cGₓ` for the finite Appell kernel. -/
def appellXOperatorValue (m : ℕ) (b c d x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    appellLeftOperatorCoefficient m b c d i j * x ^ i * y ^ j

/-- The coefficient form of `yGᵧᵧ + dGᵧ` for the finite Appell kernel. -/
def appellYOperatorValue (m : ℕ) (b c d x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    appellRightOperatorCoefficient m b c d i j * x ^ i * y ^ j

/-- The finite Appell coefficient recurrence gives the equality of its two
formal differential expressions. -/
theorem appellXOperatorValue_eq_appellYOperatorValue (m : ℕ) (b : ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (x y : ℝ) :
    appellXOperatorValue m b c d x y = appellYOperatorValue m b c d x y := by
  unfold appellXOperatorValue appellYOperatorValue
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [appellKernel_operator_coefficient_identity m b hc hd i j]

/-- At the Jacobi coordinate substitution, the Appell chain-rule residual
vanishes.  This is the right-hand side of
`(D_r - D_z) G(r*z, (1-r)*(1-z))`. -/
theorem appellJacobi_chainResidual_eq_zero (m : ℕ) (b : ℝ) {c d r z : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    (r - z) *
        (appellXOperatorValue m b c d (r * z) ((1 - r) * (1 - z)) -
          appellYOperatorValue m b c d (r * z) ((1 - r) * (1 - z))) = 0 := by
  rw [appellXOperatorValue_eq_appellYOperatorValue m b hc hd]
  ring

/-! ## The scalar Appell-coordinate summand bridge

An Appell coefficient at the two scalar coordinates is one Jacobi-deformation
summand, with its remaining power of `xi` explicit.
-/

/-- Evaluating one Appell kernel coefficient at the two scalar
coordinates gives the corresponding deformation summand. -/
theorem appellKernelCoefficient_coordinate_eq_summand (m i j : ℕ)
    (δ c d U V xi r z : ℝ) (hij : i + j ≤ m)
    (hU : xi * r * z = -U) (hV : xi * (1 - r) * (1 - z) = -V) :
    (-1 : ℝ) ^ m * xi ^ m *
        appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d i j *
          (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
      summand m δ c d U V i j * xi ^ (m - i - j) := by
  have hsplit : xi ^ m = xi ^ (i + j) * xi ^ (m - i - j) := by
    rw [← pow_add]
    congr 1
    lia
  have hU_pow : xi ^ i * (r * z) ^ i = (-U) ^ i := by
    calc
      xi ^ i * (r * z) ^ i = (xi * (r * z)) ^ i := (mul_pow _ _ _).symm
      _ = (-U) ^ i := by rw [show xi * (r * z) = xi * r * z by ring, hU]
  have hV_pow : xi ^ j * ((1 - r) * (1 - z)) ^ j = (-V) ^ j := by
    calc
      xi ^ j * ((1 - r) * (1 - z)) ^ j =
          (xi * ((1 - r) * (1 - z))) ^ j := (mul_pow _ _ _).symm
      _ = (-V) ^ j := by
        rw [show xi * ((1 - r) * (1 - z)) = xi * (1 - r) * (1 - z) by ring, hV]
  have hcoordinates : xi ^ (i + j) * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
      (-1 : ℝ) ^ (i + j) * U ^ i * V ^ j := by
    calc
      xi ^ (i + j) * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
          (xi ^ i * (r * z) ^ i) *
            (xi ^ j * ((1 - r) * (1 - z)) ^ j) := by
        rw [pow_add]
        ring
      _ = (-U) ^ i * (-V) ^ j := by rw [hU_pow, hV_pow]
      _ = (-1 : ℝ) ^ (i + j) * U ^ i * V ^ j := by
        rw [neg_pow U i, neg_pow V j]
        calc
          (-1 : ℝ) ^ i * U ^ i * ((-1 : ℝ) ^ j * V ^ j) =
              ((-1 : ℝ) ^ i * (-1 : ℝ) ^ j) * U ^ i * V ^ j := by ring
          _ = (-1 : ℝ) ^ (i + j) * U ^ i * V ^ j := by rw [pow_add]
  have hxi_coordinates : xi ^ m * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
      (-1 : ℝ) ^ (i + j) * U ^ i * V ^ j * xi ^ (m - i - j) := by
    calc
      xi ^ m * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
          (xi ^ (i + j) * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j) *
            xi ^ (m - i - j) := by
        rw [hsplit]
        ring
      _ = (-1 : ℝ) ^ (i + j) * U ^ i * V ^ j * xi ^ (m - i - j) := by
        rw [hcoordinates]
  have hnegative : risingFactorial (-(m : ℝ)) (i + j) =
      (-1 : ℝ) ^ (i + j) * (m.descFactorial (i + j) : ℝ) := by
    rw [risingFactorial, ascPochhammer_eval_neg_eq_descPochhammer,
      descPochhammer_eval_eq_descFactorial]
  have hfactorial : ((m - (i + j)).factorial : ℝ) *
      (m.descFactorial (i + j) : ℝ) = (m.factorial : ℝ) := by
    have hfactorial' := Nat.factorial_mul_descFactorial hij
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hfactorial'
  have hfactorial_ne : ((m - (i + j)).factorial : ℝ) ≠ 0 := by
    positivity
  have hratio : (m.descFactorial (i + j) : ℝ) =
      (m.factorial : ℝ) / ((m - (i + j)).factorial : ℝ) := by
    apply (eq_div_iff hfactorial_ne).2
    simpa [mul_comm] using hfactorial
  have hsub : m - i - j = m - (i + j) := by lia
  have hkernel :
      (-1 : ℝ) ^ m * xi ^ m *
          ((-1 : ℝ) ^ m * ((-1 : ℝ) ^ (i + j) * (m.descFactorial (i + j) : ℝ)) *
            risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial)) *
          (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
        (m.descFactorial (i + j) : ℝ) / ((i.factorial : ℝ) * (j.factorial : ℝ)) *
          (risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
            (risingFactorial c i * risingFactorial d j)) *
          U ^ i * V ^ j * xi ^ (m - i - j) := by
    calc
      (-1 : ℝ) ^ m * xi ^ m *
          ((-1 : ℝ) ^ m * ((-1 : ℝ) ^ (i + j) * (m.descFactorial (i + j) : ℝ)) *
            risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial)) *
          (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
          ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m * (-1 : ℝ) ^ (i + j)) *
            (m.descFactorial (i + j) : ℝ) *
            risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial) *
            (xi ^ m * (r * z) ^ i * ((1 - r) * (1 - z)) ^ j) := by
        ring
      _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m * (-1 : ℝ) ^ (i + j)) *
            (m.descFactorial (i + j) : ℝ) *
            risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j * i.factorial * j.factorial) *
            ((-1 : ℝ) ^ (i + j) * U ^ i * V ^ j * xi ^ (m - i - j)) := by
        rw [hxi_coordinates]
      _ = (m.descFactorial (i + j) : ℝ) / ((i.factorial : ℝ) * (j.factorial : ℝ)) *
            (risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
              (risingFactorial c i * risingFactorial d j)) *
            U ^ i * V ^ j * xi ^ (m - i - j) := by
        ring_nf
        rw [show (-1 : ℝ) ^ (m * 2) = 1 by
              rw [Nat.mul_comm, pow_mul]
              norm_num,
          show (-1 : ℝ) ^ (i * 2) = 1 by
              rw [Nat.mul_comm, pow_mul]
              norm_num,
          show (-1 : ℝ) ^ (j * 2) = 1 by
              rw [Nat.mul_comm, pow_mul]
              norm_num]
        ring
  calc
    (-1 : ℝ) ^ m * xi ^ m *
        appellKernelCoefficient m ((m : ℝ) + c + d - 1 + δ) c d i j *
          (r * z) ^ i * ((1 - r) * (1 - z)) ^ j =
        (m.descFactorial (i + j) : ℝ) / ((i.factorial : ℝ) * (j.factorial : ℝ)) *
          (risingFactorial ((m : ℝ) + c + d - 1 + δ) (i + j) /
            (risingFactorial c i * risingFactorial d j)) *
          U ^ i * V ^ j * xi ^ (m - i - j) := by
      rw [appellKernelCoefficient, ite_eq_left hij, hnegative]
      exact hkernel
    _ = summand m δ c d U V i j * xi ^ (m - i - j) := by
      unfold summand
      rw [hsub, hratio]
      ring

/-! ## Jacobi transport of the finite Appell kernel

This section uses ordinary univariate polynomial differentiation.  The library
Jacobi operator `jacobiDifferentialOperator` is the negative of the positive
operator `D = -t(1 - t)∂² - (c - s t)∂` with eigenvalues `λ_j`.
-/

/-- The Bernstein monomial used in the concrete Jacobi transport. -/
def jacobiBernstein (i j : ℕ) : ℝ[X] := X ^ i * (1 - X) ^ j

/-- The library Jacobi operator on a Bernstein monomial.  It is the negative
of the positive operator `D`, hence the three signs are reversed. -/
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

/-- The Appell kernel after fixing its second Jacobi coordinate. -/
def appellJacobiKernel (m : ℕ) (b c d z : ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    C (appellKernelCoefficient m b c d i j * z ^ i * (1 - z) ^ j) *
      jacobiBernstein i j

/-- Evaluating the fixed-coordinate ordinary polynomial recovers the
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

/-- Applying the library Jacobi operator to the fixed-coordinate kernel
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

/-- The finite Appell kernel has equal evaluated Jacobi differential
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

/-! ## Degree and boundary of the Appell--Jacobi kernel -/

theorem natDegree_jacobiBernstein_le (i j : ℕ) :
    (jacobiBernstein i j).natDegree ≤ i + j := by
  have hX : (X ^ i : ℝ[X]).natDegree ≤ i := by
    simp
  have hOneSubX : (1 - X : ℝ[X]).natDegree ≤ 1 := by
    simp [sub_eq_add_neg]
  have hOneSubXPow : ((1 - X : ℝ[X]) ^ j).natDegree ≤ j := by
    simpa using Polynomial.natDegree_pow_le_of_le j hOneSubX
  unfold jacobiBernstein
  exact natDegree_mul_le.trans (Nat.add_le_add hX hOneSubXPow)

/-- The finite Appell--Jacobi kernel has degree at most its truncation
parameter. -/
theorem natDegree_appellJacobiKernel_le (m : ℕ) (b c d z : ℝ) :
    (appellJacobiKernel m b c d z).natDegree ≤ m := by
  unfold appellJacobiKernel
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro i _
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro j _
  by_cases hij : i + j ≤ m
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((natDegree_jacobiBernstein_le i j).trans hij)
  · rw [appellKernelCoefficient, ite_eq_right hij]
    simp

/-- At `z = 0`, the Appell--Jacobi kernel retains exactly its
`i = 0` Bernstein row, without expanding its coefficients. -/
theorem appellJacobiKernel_zero (m : ℕ) (b c d : ℝ) :
    appellJacobiKernel m b c d 0 =
      ∑ j ∈ Finset.range (m + 1),
        C (appellKernelCoefficient m b c d 0 j) * (1 - X) ^ j := by
  rw [appellJacobiKernel, Finset.sum_eq_single 0]
  · simp [jacobiBernstein]
  · intro i _ hi0
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    simp [jacobiBernstein, hi_pos.ne']
  · simp

/-! ## Appell coordinates and the Jacobi deformation polynomial

The finite triangular reindexing converts the scalar Appell-coordinate
identity into an equality of polynomial evaluations.
-/

private theorem sum_antidiagonal_triangle (m : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l, f ij.1 ij.2 (m - l)) =
      ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
        if i + j ≤ m then f i j (m - i - j) else 0 := by
  calc
    (∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l, f ij.1 ij.2 (m - l)) =
        ∑ x ∈ (range (m + 1)).sigma antidiagonal,
          f x.2.1 x.2.2 (m - x.1) := by
      rw [Finset.sum_sigma']
    _ = ∑ ij ∈ ((range (m + 1) ×ˢ range (m + 1)).filter fun ij => ij.1 + ij.2 ≤ m),
          f ij.1 ij.2 (m - ij.1 - ij.2) := by
      refine Finset.sum_bij (fun x _ => x.2) ?_ ?_ ?_ ?_
      · rintro ⟨l, ij⟩ h
        rcases Finset.mem_sigma.mp h with ⟨hl, hij⟩
        have hl' := Finset.mem_range.mp hl
        have hsum := Finset.mem_antidiagonal.mp hij
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩
        · lia
        · lia
        · lia
      · rintro ⟨l, ij⟩ h ⟨l', ij'⟩ h' heq
        rcases Finset.mem_sigma.mp h with ⟨_, hij⟩
        rcases Finset.mem_sigma.mp h' with ⟨_, hij'⟩
        dsimp at heq
        subst ij'
        have hsum := Finset.mem_antidiagonal.mp hij
        have hsum' := Finset.mem_antidiagonal.mp hij'
        have hll : l = l' := by lia
        subst l'
        rfl
      · intro ij hij
        rcases Finset.mem_filter.mp hij with ⟨hprod, hsum⟩
        refine ⟨⟨ij.1 + ij.2, ij⟩, Finset.mem_sigma.mpr ?_, rfl⟩
        refine ⟨Finset.mem_range.mpr ?_, Finset.mem_antidiagonal.mpr rfl⟩
        exact by lia
      · rintro ⟨l, ij⟩ h
        rcases Finset.mem_sigma.mp h with ⟨_, hij⟩
        have hsum := Finset.mem_antidiagonal.mp hij
        dsimp
        congr 1
        lia
    _ = ∑ ij ∈ range (m + 1) ×ˢ range (m + 1),
          if ij.1 + ij.2 ≤ m then f ij.1 ij.2 (m - ij.1 - ij.2) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
          if i + j ≤ m then f i j (m - i - j) else 0 := by
      rw [Finset.sum_product]

private theorem sum_range_reverse_antidiagonal (m : ℕ) (xi : ℝ)
    (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ range (m + 1), ∑ ij ∈ antidiagonal (m - k), f ij.1 ij.2 * xi ^ k) =
      ∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l, f ij.1 ij.2 * xi ^ (m - l) := by
  let g : ℕ → ℝ := fun l => ∑ ij ∈ antidiagonal l, f ij.1 ij.2 * xi ^ (m - l)
  calc
    (∑ k ∈ range (m + 1), ∑ ij ∈ antidiagonal (m - k), f ij.1 ij.2 * xi ^ k) =
        ∑ k ∈ range (m + 1), g (m - k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp only [g]
      have hkm : k ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
      rw [Nat.sub_sub_self hkm]
    _ = ∑ l ∈ range (m + 1), g l := by
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect g (m + 1)
    _ = ∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l, f ij.1 ij.2 * xi ^ (m - l) := by
      rfl

/-- The Jacobi deformation evaluated at `xi` is the Appell
Jacobi kernel at the scalar coordinate substitution. -/
theorem polynomial_eval_eq_appellJacobiKernel_coordinates (m : ℕ)
    (δ c d U V xi r z : ℝ) (hU : xi * r * z = -U)
    (hV : xi * (1 - r) * (1 - z) = -V) :
    (polynomial m δ c d U V).eval xi =
      (-1 : ℝ) ^ m * xi ^ m *
        (appellJacobiKernel m ((m : ℝ) + c + d - 1 + δ) c d z).eval r := by
  calc
    (polynomial m δ c d U V).eval xi =
        ∑ k ∈ range (m + 1), ∑ ij ∈ antidiagonal (m - k),
          summand m δ c d U V ij.1 ij.2 * xi ^ k := by
      unfold polynomial
      rw [eval_finsetSum]
      refine Finset.sum_congr rfl ?_
      intro k _
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      rw [Finset.sum_mul]
    _ = ∑ l ∈ range (m + 1), ∑ ij ∈ antidiagonal l,
          summand m δ c d U V ij.1 ij.2 * xi ^ (m - l) :=
      sum_range_reverse_antidiagonal m xi (summand m δ c d U V)
    _ = ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
          if i + j ≤ m then summand m δ c d U V i j * xi ^ (m - i - j) else 0 :=
      sum_antidiagonal_triangle m (fun i j k => summand m δ c d U V i j * xi ^ k)
    _ = (-1 : ℝ) ^ m * xi ^ m *
          appellKernelValue m ((m : ℝ) + c + d - 1 + δ) c d
            (r * z) ((1 - r) * (1 - z)) := by
      unfold appellKernelValue
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hij : i + j ≤ m
      · rw [ite_eq_left hij]
        have h := appellKernelCoefficient_coordinate_eq_summand
          m i j δ c d U V xi r z hij hU hV
        ring_nf at h ⊢
        exact h.symm
      · rw [ite_eq_right hij, appellKernelCoefficient, ite_eq_right hij]
        ring
    _ = (-1 : ℝ) ^ m * xi ^ m *
          (appellJacobiKernel m ((m : ℝ) + c + d - 1 + δ) c d z).eval r := by
      rw [eval_appellJacobiKernel]

end RealRooted.JacobiDeformation
