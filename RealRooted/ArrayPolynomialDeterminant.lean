import RealRooted.Mathlib.LinearAlgebra.Matrix.Compound
import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularStrictification
import RealRooted.Mathlib.LinearAlgebra.Matrix.SpectrumClosed
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Charpoly
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import RealRooted.PFPolynomial
import RealRooted.PolyaFrequencyConvolution

open Matrix
open Filter Topology

noncomputable section

namespace RealRooted

/-!
# Determinant matrices for array-counting polynomials

This file collects the finite totally nonnegative matrices used in the
determinant proof of real-rootedness for `A262704`.
-/

/-- A row-and-column scaled lower-ones matrix. -/
def scaledLowerFin (N : ℕ) (d : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  .of fun i j => if j ≤ i then d i / d j else 0

lemma scaledLowerFin_eq_scaleRowsCols (N : ℕ) (d : Fin (N + 1) → ℝ) :
    scaledLowerFin N d =
      Matrix.of fun i j => d i * ((d j)⁻¹ * lowerOnesFin N i j) := by
  ext i j
  by_cases hji : j ≤ i
  · simp [scaledLowerFin, lowerOnesFin, hji, div_eq_mul_inv]
  · simp [scaledLowerFin, lowerOnesFin, hji]

/-- Positive diagonal scalings of the lower-ones matrix are totally
nonnegative. -/
theorem scaledLowerFin_isTotallyNonneg (N : ℕ) (d : Fin (N + 1) → ℝ)
    (hd : ∀ i, 0 < d i) : (scaledLowerFin N d).IsTotallyNonneg := by
  rw [scaledLowerFin_eq_scaleRowsCols]
  exact (lowerOnesFin_isTotallyNonneg N).scaleRowsCols d (fun i => (d i)⁻¹)
    (fun i => (hd i).le) (fun i => inv_nonneg.mpr (hd i).le)

lemma scaledLowerFin_transpose_blockTriangular (N : ℕ)
    (d : Fin (N + 1) → ℝ) : (scaledLowerFin N d)ᵀ.BlockTriangular id := by
  intro i j hji
  have hij : ¬ i ≤ j := not_le_of_gt hji
  simp [scaledLowerFin, hij]

/-- Every scaled lower-ones matrix with nonzero scaling values has determinant
one. -/
@[simp] theorem scaledLowerFin_det (N : ℕ) (d : Fin (N + 1) → ℝ)
    (hd : ∀ i, d i ≠ 0) :
    (scaledLowerFin N d).det = 1 := by
  rw [← Matrix.det_transpose]
  rw [Matrix.det_of_upperTriangular (scaledLowerFin_transpose_blockTriangular N d)]
  simp [scaledLowerFin, hd]

/-- The cumulative products of the lower-bidiagonal weights
`u i = 1 / (i ^ 2 * (i - 1))`. -/
def arrayUScale {N : ℕ} (i : Fin (N + 1)) : ℝ :=
  (((Nat.factorial (i + 1) : ℝ) ^ 2 * (Nat.factorial i : ℝ)))⁻¹

/-- The cumulative products of the lower-bidiagonal weights
`v i = 1 / (i * (i - 1) ^ 2)`. -/
def arrayVScale {N : ℕ} (i : Fin (N + 1)) : ℝ :=
  (((Nat.factorial (i + 1) : ℝ) * (Nat.factorial i : ℝ) ^ 2))⁻¹

lemma arrayUScale_pos {N : ℕ} (i : Fin (N + 1)) : 0 < arrayUScale i := by
  simp only [arrayUScale]
  positivity

lemma arrayVScale_pos {N : ℕ} (i : Fin (N + 1)) : 0 < arrayVScale i := by
  simp only [arrayVScale]
  positivity

/-- The totally nonnegative kernel `B⁻¹` in the determinant proof. -/
def arrayKernelFin (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  scaledLowerFin N arrayVScale * scaledLowerFin N arrayUScale

theorem arrayKernelFin_isTotallyNonneg (N : ℕ) :
    (arrayKernelFin N).IsTotallyNonneg := by
  exact (scaledLowerFin_isTotallyNonneg N arrayVScale arrayVScale_pos).mul
    (scaledLowerFin_isTotallyNonneg N arrayUScale arrayUScale_pos)

@[simp] theorem arrayKernelFin_det (N : ℕ) : (arrayKernelFin N).det = 1 := by
  rw [arrayKernelFin, Matrix.det_mul, scaledLowerFin_det, scaledLowerFin_det]
  · norm_num
  · exact fun i => (arrayUScale_pos i).ne'
  · exact fun i => (arrayVScale_pos i).ne'

/-- A finite upper-bidiagonal matrix, with diagonal `a` and superdiagonal
one. At `a = 0` this is the upper shift matrix. -/
def upperBidiagonalFin (N : ℕ) (a : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  ((bidiagonal a).submatrix Fin.val Fin.val)ᵀ

@[simp] lemma upperBidiagonalFin_apply (N : ℕ) (a : ℝ)
    (i j : Fin (N + 1)) :
    upperBidiagonalFin N a i j =
      if j = i then a else if j.val = i.val + 1 then 1 else 0 := by
  simp only [upperBidiagonalFin, transpose_apply, submatrix_apply, bidiagonal_apply]
  by_cases hij : j = i
  · subst j
    simp
  · have hval : j.val ≠ i.val := fun h => hij (Fin.ext h)
    simp [hij, hval]

theorem upperBidiagonalFin_isTotallyNonneg (N : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (upperBidiagonalFin N a).IsTotallyNonneg := by
  exact (((bidiagonal_isTotallyNonneg a ha).submatrix
    Fin.val_strictMono Fin.val_strictMono).toRect.transpose).toSquare

lemma upperBidiagonalFin_blockTriangular (N : ℕ) (a : ℝ) :
    (upperBidiagonalFin N a).BlockTriangular id := by
  intro i j hji
  have hne : j ≠ i := ne_of_lt hji
  have hsucc : j.val ≠ i.val + 1 := by
    have hval : j.val < i.val := Fin.lt_def.mp hji
    lia
  simp [upperBidiagonalFin_apply, hne, hsucc]

@[simp] theorem upperBidiagonalFin_det (N : ℕ) (a : ℝ) :
    (upperBidiagonalFin N a).det = a ^ (N + 1) := by
  rw [Matrix.det_of_upperTriangular (upperBidiagonalFin_blockTriangular N a)]
  simp [upperBidiagonalFin_apply]

/-- The invertible perturbation of `B⁻¹ S` used before Gaussian
strictification. -/
def arrayPerturbedKernelFin (N : ℕ) (a : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  arrayKernelFin N * upperBidiagonalFin N a

theorem arrayPerturbedKernelFin_isTotallyNonneg (N : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (arrayPerturbedKernelFin N a).IsTotallyNonneg :=
  (arrayKernelFin_isTotallyNonneg N).mul (upperBidiagonalFin_isTotallyNonneg N a ha)

@[simp] theorem arrayPerturbedKernelFin_det (N : ℕ) (a : ℝ) :
    (arrayPerturbedKernelFin N a).det = a ^ (N + 1) := by
  rw [arrayPerturbedKernelFin, Matrix.det_mul, arrayKernelFin_det,
    upperBidiagonalFin_det, one_mul]

theorem arrayPerturbedKernelFin_mulVec_injective (N : ℕ) (a : ℝ) (ha : a ≠ 0) :
    Function.Injective (arrayPerturbedKernelFin N a).mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    arrayPerturbedKernelFin_det]
  exact pow_ne_zero _ ha

/-- Gaussian strictification of the invertible perturbed kernel. -/
def gaussianArrayKernelFin (N : ℕ) (a δ : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  gaussianMatrix (N + 1) a * arrayPerturbedKernelFin N δ

theorem gaussianArrayKernelFin_isTotallyNonneg (N : ℕ) (a δ : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) : (gaussianArrayKernelFin N a δ).IsTotallyNonneg := by
  intro q rows cols hrows hcols
  exact (Matrix.IsTotallyNonnegRect.det_gaussianMatrix_mul_pos_of_injective
    (arrayPerturbedKernelFin_isTotallyNonneg N δ hδ.le).toRect
    (arrayPerturbedKernelFin_mulVec_injective N δ hδ.ne') ha hrows hcols).le

theorem gaussianArrayKernelFin_minors_pos (N : ℕ) (a δ : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) {q : ℕ}
    {rows cols : Fin q → Fin (N + 1)}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 < ((gaussianArrayKernelFin N a δ).submatrix rows cols).det := by
  exact Matrix.IsTotallyNonnegRect.det_gaussianMatrix_mul_pos_of_injective
    (arrayPerturbedKernelFin_isTotallyNonneg N δ hδ.le).toRect
    (arrayPerturbedKernelFin_mulVec_injective N δ hδ.ne') ha hrows hcols

theorem gaussianArrayKernelFin_charpoly_factorization (N : ℕ) (a δ : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) :
    ∃ μ : Fin (N + 1) → ℝ, (∀ i, 0 < μ i) ∧
      (gaussianArrayKernelFin N a δ).charpoly =
        ∏ i, (Polynomial.X - Polynomial.C (μ i)) := by
  apply exists_charpoly_eq_prod_of_pow_compound_pos
    (gaussianArrayKernelFin_isTotallyNonneg N a δ ha hδ) (k := 1) one_pos
  intro q hq hqN s t
  rw [pow_one, compound_apply]
  exact gaussianArrayKernelFin_minors_pos N a δ ha hδ
    (strictMono_powersetEnum s) (strictMono_powersetEnum t)

private theorem complex_charpoly_roots_pos_of_factorization
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {μ : Fin n → ℝ}
    (hμ : ∀ i, 0 < μ i)
    (hfact : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (μ i))) :
    ∀ z ∈ ((A.map (algebraMap ℝ ℂ)).charpoly.roots),
      ∃ r : ℝ, 0 < r ∧ (r : ℂ) = z := by
  open Polynomial in
  have hfactC : (A.map (algebraMap ℝ ℂ)).charpoly =
      ∏ i, ((X : ℂ[X]) - C (μ i : ℂ)) := by
    rw [Matrix.charpoly_map, hfact, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    simp
  intro z hz
  rw [hfactC] at hz
  open Polynomial in
  have hmulti :
      (∏ i, ((X : ℂ[X]) - C (μ i : ℂ))) =
        ((Finset.univ.val.map fun i => (μ i : ℂ)).map
          fun x => (X : ℂ[X]) - C x).prod := by
    rw [Finset.prod, Multiset.map_map]
    rfl
  rw [hmulti, Polynomial.roots_multiset_prod_X_sub_C] at hz
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hz
  exact ⟨μ i, hμ i, rfl⟩

theorem gaussianArrayKernelFin_complex_roots_pos (N : ℕ) (a δ : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) :
    ∀ z ∈ (((gaussianArrayKernelFin N a δ).map
      (algebraMap ℝ ℂ)).charpoly.roots),
      ∃ r : ℝ, 0 < r ∧ (r : ℂ) = z := by
  obtain ⟨μ, hμ, hfact⟩ := gaussianArrayKernelFin_charpoly_factorization N a δ ha hδ
  exact complex_charpoly_roots_pos_of_factorization hμ hfact

/-- Removing the Gaussian strictifier preserves real nonnegative spectrum. -/
theorem arrayPerturbedKernelFin_complex_roots_nonneg (N : ℕ) (δ : ℝ)
    (hδ : 0 < δ) :
    ∀ z ∈ (((arrayPerturbedKernelFin N δ).map
      (algebraMap ℝ ℂ)).charpoly.roots),
      ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = z := by
  apply charpoly_roots_nonneg_real_of_tendsto
    (A := fun k => gaussianArrayKernelFin N ((k : ℝ) + 1) δ)
    (A₀ := arrayPerturbedKernelFin N δ)
  · have hparam : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hmat := (tendsto_gaussianMatrix_mul_atTop
      (arrayPerturbedKernelFin N δ)).comp hparam
    intro i j
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
      (show Tendsto
        (fun k : ℕ => gaussianArrayKernelFin N ((k : ℝ) + 1) δ) atTop
          (nhds (arrayPerturbedKernelFin N δ)) by
        change Tendsto
          ((fun a => gaussianMatrix (N + 1) a * arrayPerturbedKernelFin N δ) ∘
            fun k : ℕ => (k : ℝ) + 1) atTop
              (nhds (arrayPerturbedKernelFin N δ))
        exact hmat) i) j
  · intro k z hz
    obtain ⟨r, hr, hrz⟩ := gaussianArrayKernelFin_complex_roots_pos
      N ((k : ℝ) + 1) δ (by positivity) hδ z hz
    exact ⟨r, hr.le, hrz⟩

/-- The unperturbed totally nonnegative matrix `B⁻¹ S`. -/
def arrayKernelShiftFin (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  arrayPerturbedKernelFin N 0

/-- The actual determinant kernel has real nonnegative spectrum. This is the
specialized Gantmacher--Krein conclusion needed for `A262704`; it avoids any
general density theorem for totally nonnegative matrices. -/
theorem arrayKernelShiftFin_complex_roots_nonneg (N : ℕ) :
    ∀ z ∈ (((arrayKernelShiftFin N).map
      (algebraMap ℝ ℂ)).charpoly.roots),
      ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = z := by
  let δ : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  have hδ : Tendsto δ atTop (nhds 0) := by
    simpa [δ, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply charpoly_roots_nonneg_real_of_tendsto
    (A := fun k => arrayPerturbedKernelFin N (δ k))
    (A₀ := arrayKernelShiftFin N)
  · intro i j
    simp only [arrayPerturbedKernelFin, Matrix.mul_apply, arrayKernelShiftFin]
    apply tendsto_finsetSum
    intro x hx
    apply tendsto_const_nhds.mul
    simp only [upperBidiagonalFin_apply]
    by_cases hjx : j = x
    · simpa [hjx] using hδ
    · simp [hjx]
  · intro k z hz
    have hδpos : 0 < δ k := by
      simp only [δ]
      positivity
    exact arrayPerturbedKernelFin_complex_roots_nonneg N (δ k) hδpos z hz

private theorem charpoly_splits_of_complex_roots_real
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hroots : ∀ z ∈ ((A.map (algebraMap ℝ ℂ)).charpoly.roots),
      ∃ r : ℝ, (r : ℂ) = z) : A.charpoly.Splits := by
  apply Polynomial.Splits.of_splits_map_of_injective
    (algebraMap ℝ ℂ).injective (IsAlgClosed.splits _)
  intro z hz
  have hz' : z ∈ (A.map (algebraMap ℝ ℂ)).charpoly.roots := by
    rwa [Matrix.charpoly_map]
  obtain ⟨r, hrz⟩ := hroots z hz'
  exact ⟨r, hrz⟩

private theorem det_one_add_X_smul_eq_reverse_charpoly_comp_neg_X
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C) =
      A.charpoly.reverse.comp (-Polynomial.X) := by
  open Polynomial in
  rw [Matrix.reverse_charpoly]
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_neg, Polynomial.eval_X]
  rw [Matrix.charpolyRev, ← Polynomial.coe_evalRingHom,
    RingHom.map_det, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The normalized determinant polynomial `det (I + X * B⁻¹ S)`. -/
def arrayDetPolynomialFin (N : ℕ) : Polynomial ℝ :=
  Matrix.det (1 + (Polynomial.X : Polynomial ℝ) •
    (arrayKernelShiftFin N).map Polynomial.C)

theorem arrayKernelShiftFin_isTotallyNonneg (N : ℕ) :
    (arrayKernelShiftFin N).IsTotallyNonneg :=
  arrayPerturbedKernelFin_isTotallyNonneg N 0 (by norm_num)

theorem arrayDetPolynomialFin_hasNonnegCoeffs (N : ℕ) :
    HasNonnegCoeffs (arrayDetPolynomialFin N) := by
  intro k
  rw [arrayDetPolynomialFin, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  exact Finset.sum_nonneg fun s _ =>
    (arrayKernelShiftFin_isTotallyNonneg N).principalMinor_nonneg s

theorem arrayDetPolynomialFin_splits (N : ℕ) :
    (arrayDetPolynomialFin N).Splits := by
  rw [arrayDetPolynomialFin,
    det_one_add_X_smul_eq_reverse_charpoly_comp_neg_X]
  apply (DegreeDropReversal.splits_reverse ?_).comp_of_natDegree_le_one
  · simp
  · exact charpoly_splits_of_complex_roots_real fun z hz => by
      obtain ⟨r, hr, hrz⟩ := arrayKernelShiftFin_complex_roots_nonneg N z hz
      exact ⟨r, hrz⟩

/-- The normalized determinant polynomial is Pólya-frequency. -/
theorem arrayDetPolynomialFin_isPFPolynomial (N : ℕ) :
    IsPFPolynomial (arrayDetPolynomialFin N) :=
  IsPFPolynomial.of_realRooted_nonneg
    (arrayDetPolynomialFin_hasNonnegCoeffs N) (arrayDetPolynomialFin_splits N)

end RealRooted
