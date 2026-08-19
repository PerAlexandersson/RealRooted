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
This file proves Gaussian convergence and strict positivity of all strictly
ordered finite minors using Karlin.s exponential-kernel argument.
-/

public section

open scoped Interval

open Filter MeasureTheory Topology

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
      have hval : (i : ℕ) = (j : ℕ) := by exact_mod_cast heq
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

/-- Adjacent exponential-kernel row differences are interval integrals. -/
lemma exponentialKernelMatrix_succ_sub_castSucc_eq_intervalIntegral {n : ℕ}
    (x : Fin (n + 1) → ℝ) (y : Fin n → ℝ) (i j : Fin n) :
    exponentialKernelMatrix x y i.succ j -
        exponentialKernelMatrix x y i.castSucc j =
      ∫ t in x i.castSucc..x i.succ, y j * Real.exp (t * y j) := by
  rw [Real.intervalIntegral_mul_exp_mul]
  rfl

/-- The adjacent-difference determinant is a restricted-volume product integral. -/
theorem det_adjacentRowDiff_exponentialKernelMatrix_eq_integral {n : ℕ}
    (x : Fin (n + 1) → ℝ) (y : Fin n → ℝ) (hx : StrictMono x) :
    (Matrix.of fun i j =>
      exponentialKernelMatrix x y i.succ j -
        exponentialKernelMatrix x y i.castSucc j).det =
      ∫ t : Fin n → ℝ,
        (Matrix.of fun i j => y j * Real.exp (t i * y j)).det
          ∂Measure.pi (fun i =>
            volume.restrict (Set.Ioc (x i.castSucc) (x i.succ))) := by
  let μ : Fin n → Measure ℝ := fun i =>
    volume.restrict (Set.Ioc (x i.castSucc) (x i.succ))
  let f : Fin n → ℝ → Fin n → ℝ := fun _ t j =>
    y j * Real.exp (t * y j)
  have hf : ∀ i j, Integrable (fun t => f i t j) (μ i) := by
    intro i j
    change IntegrableOn (fun t => f i t j)
      (Set.Ioc (x i.castSucc) (x i.succ)) volume
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le
      (hx i.castSucc_lt_succ).le]
    exact
      (continuous_const.mul
        (Real.continuous_exp.comp (continuous_id.mul continuous_const))).intervalIntegrable _ _
  have hmatrix :
      Matrix.of (fun i j =>
        exponentialKernelMatrix x y i.succ j -
          exponentialKernelMatrix x y i.castSucc j) =
        Matrix.of fun i j => ∫ t, f i t j ∂μ i := by
    ext i j
    simp only [Matrix.of_apply]
    rw [exponentialKernelMatrix_succ_sub_castSucc_eq_intervalIntegral]
    rw [intervalIntegral.integral_of_le (hx i.castSucc_lt_succ).le]
  rw [hmatrix, det_integral_rows_eq_integral_det μ f hf]

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

/-- The adjacent-difference determinant is positive under the smaller-minor hypothesis. -/
theorem det_adjacentRowDiff_exponentialKernelMatrix_pos {n : ℕ}
    (x : Fin (n + 1) → ℝ) (y : Fin n → ℝ) (hx : StrictMono x)
    (hy : ∀ j, 0 < y j)
    (hdet : ∀ t : Fin n → ℝ, StrictMono t →
      0 < (exponentialKernelMatrix t y).det) :
    0 < (Matrix.of fun i j =>
      exponentialKernelMatrix x y i.succ j -
        exponentialKernelMatrix x y i.castSucc j).det := by
  rw [det_adjacentRowDiff_exponentialKernelMatrix_eq_integral x y hx]
  let μ : Fin n → Measure ℝ := fun i =>
    volume.restrict (Set.Ioc (x i.castSucc) (x i.succ))
  let f : Fin n → ℝ → Fin n → ℝ := fun _ t j =>
    y j * Real.exp (t * y j)
  have hf : ∀ i j, Integrable (fun t => f i t j) (μ i) := by
    intro i j
    change IntegrableOn (fun t => f i t j)
      (Set.Ioc (x i.castSucc) (x i.succ)) volume
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le
      (hx i.castSucc_lt_succ).le]
    exact
      (continuous_const.mul
        (Real.continuous_exp.comp (continuous_id.mul continuous_const))).intervalIntegrable _ _
  have hbox : ∀ᵐ t ∂Measure.pi μ,
      ∀ i, t i ∈ Set.Ioc (x i.castSucc) (x i.succ) := by
    rw [Filter.eventually_all]
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually
      (ae_restrict_mem measurableSet_Ioc)
  have hpoint_pos : ∀ᵐ t ∂Measure.pi μ,
      0 < (Matrix.of fun i j => f i (t i) j).det := by
    filter_upwards [hbox] with t ht
    have htmono : StrictMono t := by
      intro i j hij
      exact (ht i).2.trans_lt
        ((hx.monotone (Fin.mk_le_mk.mpr (Nat.succ_le_of_lt hij))).trans_lt (ht j).1)
    rw [show Matrix.of (fun i j => f i (t i) j) =
        Matrix.of fun i j =>
          y j * exponentialKernelMatrix t y i j by
      ext i j
      rfl,
      Matrix.det_mul_row]
    exact mul_pos (Finset.prod_pos fun j _ => hy j) (hdet t htmono)
  have hdetInt : Integrable
      (fun t : Fin n → ℝ => (Matrix.of fun i j => f i (t i) j).det)
      (Measure.pi μ) :=
    integrable_det_rows μ f hf
  have hsupp : Function.support
      (fun t : Fin n → ℝ => (Matrix.of fun i j => f i (t i) j).det) =ᵐ[Measure.pi μ]
      Set.univ := hpoint_pos.mono fun t ht => by
    apply propext
    change ((Matrix.of fun i j => f i (t i) j).det ≠ 0) ↔ True
    exact iff_true_intro ht.ne'
  rw [integral_pos_iff_support_of_nonneg_ae
    (hpoint_pos.mono fun _ h => h.le) hdetInt,
    measure_congr hsupp, Measure.pi_univ]
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  simpa [μ, Real.volume_Ioc] using hx i.castSucc_lt_succ

/-- Strictly ordered exponential-kernel minors are positive. -/
theorem det_exponentialKernelMatrix_pos {q : ℕ}
    {x y : Fin q → ℝ} (hx : StrictMono x) (hy : StrictMono y) :
    0 < (exponentialKernelMatrix x y).det := by
  induction q with
  | zero => simp
  | succ n ih =>
      let y0 : Fin (n + 1) → ℝ := fun j => y j - y 0
      have hy0 : StrictMono y0 := fun _ _ hij =>
        sub_lt_sub_right (hy hij) _
      have hy00 : y0 0 = 0 := by simp [y0]
      have hy_eq : y = fun j => y0 j + y 0 := by
        funext j
        simp [y0]
      rw [hy_eq]
      apply (det_exponentialKernelMatrix_add_const_right_pos_iff
        x y0 (y 0)).2
      have hfirst : ∀ i, exponentialKernelMatrix x y0 i 0 = 1 := by
        intro i
        change Real.exp (x i * y0 0) = 1
        rw [hy00]
        simp
      rw [det_eq_det_adjacentRowDiff_of_firstColumn_eq_one _ hfirst]
      let yTail : Fin n → ℝ := fun j => y0 j.succ
      have hyTail : StrictMono yTail := hy0.comp Fin.strictMono_succ
      have hyTail_pos : ∀ j, 0 < yTail j := by
        intro j
        exact hy00 ▸ hy0 (by simp)
      exact det_adjacentRowDiff_exponentialKernelMatrix_pos
        x yTail hx hyTail_pos (fun t ht => ih ht hyTail)

/-- Strictly ordered minors of Karlin's Gaussian matrix are positive. -/
theorem det_gaussianMatrix_submatrix_pos {n q : ℕ}
    (a : ℝ) (rows cols : Fin q → Fin n) (ha : 0 < a)
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 < ((gaussianMatrix n a).submatrix rows cols).det := by
  apply det_gaussianMatrix_submatrix_pos_of_exponentialKernel a rows cols
  apply det_exponentialKernelMatrix_pos
  · exact (Nat.strictMono_cast.comp
      (Fin.val_strictMono.comp hrows)).const_mul (by positivity)
  · exact Nat.strictMono_cast.comp (Fin.val_strictMono.comp hcols)

end Matrix
