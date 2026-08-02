import RealRooted.Mathlib.Analysis.SpecialFunctions.ExpIntegral
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Integral
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix
import RealRooted.Mathlib.LinearAlgebra.Vandermonde

/-!
# Karlin's finite Gaussian matrices

This file starts the formalization of Karlin, *Total Positivity*, Vol. I,
Chapter V, Section 1, Proposition 1.1.  Karlin uses the Gaussian matrix

`F(a) i j = exp (-a * (i - j) ^ 2)`.

The proposition has two parts: `F(a)` tends to the identity as `a` tends to
positive infinity, and `F(a)` is strictly totally positive when `a > 0`.
This file proves the first part.  The second part requires the source's
strict-total-positivity theorem for the exponential kernel `exp (x * y)`;
it is intentionally not assumed here.
-/

public section

open Filter Topology

namespace Matrix

/-- Karlin's finite Gaussian matrix from Proposition V.1.1. -/
noncomputable def gaussianMatrix (n : ℕ) (a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (-a * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2)

@[simp] lemma gaussianMatrix_apply (n : ℕ) (a : ℝ) (i j : Fin n) :
    gaussianMatrix n a i j =
      Real.exp (-a * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2) :=
  rfl

@[simp] lemma gaussianMatrix_apply_self (n : ℕ) (a : ℝ) (i : Fin n) :
    gaussianMatrix n a i i = 1 := by
  simp

lemma gaussianMatrix_apply_pos (n : ℕ) (a : ℝ) (i j : Fin n) :
    0 < gaussianMatrix n a i j :=
  Real.exp_pos _

/-- Karlin's Gaussian matrix converges entrywise to the identity as its
parameter tends to positive infinity. -/
theorem tendsto_gaussianMatrix_atTop (n : ℕ) :
    Tendsto (gaussianMatrix n) atTop
      (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  change Tendsto
    (fun a => (gaussianMatrix n a : Fin n → Fin n → ℝ)) atTop
    (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ))
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  by_cases hij : i = j
  · subst j
    simp only [gaussianMatrix_apply_self, one_apply, if_pos]
    exact tendsto_const_nhds
  · have hcast :
        (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ≠ 0 := by
      rw [sub_ne_zero]
      intro heq
      have hval : (i : ℕ) = (j : ℕ) := by
        exact_mod_cast heq
      exact hij (Fin.ext hval)
    have hsquare :
        0 < (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 :=
      sq_pos_of_ne_zero hcast
    have hneg :
        -(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 < 0 :=
      neg_lt_zero.mpr hsquare
    have hlinear :
        Tendsto
          (fun a : ℝ =>
            a * -(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2)
          atTop atBot :=
      tendsto_id.atTop_mul_const_of_neg hneg
    have hexp :=
      Real.tendsto_exp_atBot.comp hlinear
    convert hexp using 1
    · funext a
      simp only [Function.comp_apply, gaussianMatrix_apply]
      ring_nf
    · simp [hij]

/-- The finite restriction of Karlin's exponential kernel `exp (x * y)`. -/
noncomputable def exponentialKernelMatrix {i j : Type*}
    (x : i → ℝ) (y : j → ℝ) : Matrix i j ℝ :=
  fun i j => Real.exp (x i * y j)

@[simp] lemma exponentialKernelMatrix_apply {i j : Type*}
    (x : i → ℝ) (y : j → ℝ) (r : i) (c : j) :
    exponentialKernelMatrix x y r c = Real.exp (x r * y c) :=
  rfl

/-- Translating all first coordinates multiplies the exponential-kernel
determinant by an explicit positive column factor. -/
theorem det_exponentialKernelMatrix_add_const_left {q : ℕ}
    (x y : Fin q → ℝ) (c : ℝ) :
    (exponentialKernelMatrix (fun i => x i + c) y).det =
      (∏ j, Real.exp (c * y j)) *
        (exponentialKernelMatrix x y).det := by
  have hmatrix :
      exponentialKernelMatrix (fun i => x i + c) y =
        of fun i j =>
          Real.exp (c * y j) * exponentialKernelMatrix x y i j := by
    ext i j
    simp only [exponentialKernelMatrix_apply, of_apply]
    rw [show (x i + c) * y j = c * y j + x i * y j by ring,
      Real.exp_add]
  rw [hmatrix, det_mul_row]

/-- Translating all second coordinates multiplies the exponential-kernel
determinant by an explicit positive row factor. -/
theorem det_exponentialKernelMatrix_add_const_right {q : ℕ}
    (x y : Fin q → ℝ) (c : ℝ) :
    (exponentialKernelMatrix x (fun j => y j + c)).det =
      (∏ i, Real.exp (x i * c)) *
        (exponentialKernelMatrix x y).det := by
  have hmatrix :
      exponentialKernelMatrix x (fun j => y j + c) =
        of fun i j =>
          Real.exp (x i * c) * exponentialKernelMatrix x y i j := by
    ext i j
    simp only [exponentialKernelMatrix_apply, of_apply]
    rw [show x i * (y j + c) = x i * c + x i * y j by ring,
      Real.exp_add]
  rw [hmatrix, det_mul_column]

theorem det_exponentialKernelMatrix_add_const_left_pos_iff {q : ℕ}
    (x y : Fin q → ℝ) (c : ℝ) :
    0 < (exponentialKernelMatrix (fun i => x i + c) y).det ↔
      0 < (exponentialKernelMatrix x y).det := by
  rw [det_exponentialKernelMatrix_add_const_left]
  exact mul_pos_iff_of_pos_left (by positivity)

theorem det_exponentialKernelMatrix_add_const_right_pos_iff {q : ℕ}
    (x y : Fin q → ℝ) (c : ℝ) :
    0 < (exponentialKernelMatrix x (fun j => y j + c)).det ↔
      0 < (exponentialKernelMatrix x y).det := by
  rw [det_exponentialKernelMatrix_add_const_right]
  exact mul_pos_iff_of_pos_left (by positivity)

/-- The transpose of the Wronskian matrix of the functions
`t ↦ exp (y i * t)`. -/
noncomputable def exponentialWronskianMatrix {q : ℕ}
    (y : Fin q → ℝ) (t : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => iteratedDeriv (j : ℕ) (fun s => Real.exp (y i * s)) t

@[simp] lemma exponentialWronskianMatrix_apply {q : ℕ}
    (y : Fin q → ℝ) (t : ℝ) (i j : Fin q) :
    exponentialWronskianMatrix y t i j =
      y i ^ (j : ℕ) * Real.exp (t * y i) := by
  rw [exponentialWronskianMatrix,
    congrFun (iteratedDeriv_exp_const_mul (j : ℕ) (y i)) t]
  congr 2
  exact mul_comm _ _

/-- Karlin's exponential Wronskian is a positive exponential factor times a
Vandermonde determinant. -/
theorem det_exponentialWronskianMatrix_eq {q : ℕ}
    (y : Fin q → ℝ) (t : ℝ) :
    (exponentialWronskianMatrix y t).det =
      (∏ i, Real.exp (t * y i)) * (vandermonde y).det := by
  have hmatrix :
      exponentialWronskianMatrix y t =
        of fun i j =>
          Real.exp (t * y i) * vandermonde y i j := by
    ext i j
    simp only [exponentialWronskianMatrix_apply, of_apply,
      vandermonde_apply]
    ring
  rw [hmatrix, det_mul_column]

/-- The exponential Wronskian has the positive orientation required in
Karlin's extended-determinant argument. -/
theorem det_exponentialWronskianMatrix_pos {q : ℕ}
    {y : Fin q → ℝ} (hy : StrictMono y) (t : ℝ) :
    0 < (exponentialWronskianMatrix y t).det := by
  rw [det_exponentialWronskianMatrix_eq]
  exact mul_pos (by positivity) (det_vandermonde_pos_of_strictMono hy)

/-- A Gaussian minor is an exponential-kernel minor times positive row and
column factors. This is the algebraic reduction in Karlin's proof of
Proposition V.1.1. -/
theorem det_gaussianMatrix_submatrix_eq {n q : ℕ} (a : ℝ)
    (rows cols : Fin q → Fin n) :
    ((gaussianMatrix n a).submatrix rows cols).det =
      (∏ i, Real.exp (-a * (((rows i : Fin n) : ℕ) : ℝ) ^ 2)) *
      (∏ j, Real.exp (-a * (((cols j : Fin n) : ℕ) : ℝ) ^ 2)) *
      (exponentialKernelMatrix
        (fun i => 2 * a * (((rows i : Fin n) : ℕ) : ℝ))
        (fun j => (((cols j : Fin n) : ℕ) : ℝ))).det := by
  let rowFactor : Fin q → ℝ :=
    fun i => Real.exp (-a * (((rows i : Fin n) : ℕ) : ℝ) ^ 2)
  let colFactor : Fin q → ℝ :=
    fun j => Real.exp (-a * (((cols j : Fin n) : ℕ) : ℝ) ^ 2)
  let E : Matrix (Fin q) (Fin q) ℝ :=
    exponentialKernelMatrix
      (fun i => 2 * a * (((rows i : Fin n) : ℕ) : ℝ))
      (fun j => (((cols j : Fin n) : ℕ) : ℝ))
  have hmatrix :
      (gaussianMatrix n a).submatrix rows cols =
        of fun i j => rowFactor i * (colFactor j * E i j) := by
    ext i j
    simp only [submatrix_apply, gaussianMatrix_apply, of_apply, rowFactor,
      colFactor, E, exponentialKernelMatrix_apply]
    rw [show
      -a * ((((rows i : Fin n) : ℕ) : ℝ) -
          (((cols j : Fin n) : ℕ) : ℝ)) ^ 2 =
        -a * (((rows i : Fin n) : ℕ) : ℝ) ^ 2 +
          (-a * (((cols j : Fin n) : ℕ) : ℝ) ^ 2 +
            (2 * a * (((rows i : Fin n) : ℕ) : ℝ)) *
              (((cols j : Fin n) : ℕ) : ℝ)) by ring]
    rw [Real.exp_add, Real.exp_add]
  have hcol :
      (of fun i j => colFactor j * E i j).det =
        (∏ j, colFactor j) * E.det :=
    det_mul_row colFactor E
  rw [hmatrix, det_mul_column]
  change
    (∏ i, rowFactor i) *
        (of fun i j => colFactor j * E i j).det =
      _
  rw [hcol]
  dsimp only [rowFactor, colFactor, E]
  ring

/-- Transfer positivity from the exponential-kernel minor to the corresponding
Gaussian minor.

The hypothesis is intentionally explicit: it is exactly Karlin III.1's
strict-total-positivity input. Keeping that analytic boundary visible lets us
formalize the Gaussian factorization without assuming Proposition V.1.1. -/
theorem det_gaussianMatrix_submatrix_pos_of_exponentialKernel {n q : ℕ}
    (a : ℝ) (rows cols : Fin q → Fin n)
    (hkernel :
      0 < (exponentialKernelMatrix
        (fun i => 2 * a * (((rows i : Fin n) : ℕ) : ℝ))
        (fun j => (((cols j : Fin n) : ℕ) : ℝ))).det) :
    0 < ((gaussianMatrix n a).submatrix rows cols).det := by
  rw [det_gaussianMatrix_submatrix_eq]
  positivity

end Matrix
