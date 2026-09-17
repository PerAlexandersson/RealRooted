import RealRooted.BrandenLeite.Regularization
import RealRooted.BrandenVecchi.ChowContinuity
import RealRooted.BrandenVecchi.ChowGeometricScaling
import RealRooted.BrandenVecchi.ChowTotallyNonneg

/-!
# Projective regularization of zero-prefix Chow symbols

The raw Toeplitz Chow construction does not preserve splitness after inserting
a finite zero prefix.  This file instead records the graded regularization
with coefficient symbol `(1 + z)^N a(epsilon * z)`.  It has unit origin for
every parameter, specializes at zero to the finite binomial symbol, and for a
nonzero parameter is the geometric scaling of the unit-normalized
`(epsilon + z)^N a(z)` approximation.
-/

open Filter Matrix Polynomial Topology

namespace RealRooted.BrandenVecchi

noncomputable section

/-- Coefficients of the projectively regularized symbol
`(1 + z)^N a(epsilon * z)`. -/
def projectiveRegularizedSequence
    (N : ℕ) (a : ℕ → ℝ) (epsilon : ℝ) : ℕ → ℝ :=
  BrandenLeite.regularizedSequence N (geometricScale epsilon a) 1

/-- The unit-origin normalization of `(epsilon + X)^N a(X)` for nonzero
`epsilon`. -/
def unitNormalizedRegularizedSequence
    (N : ℕ) (a : ℕ → ℝ) (epsilon : ℝ) : ℕ → ℝ :=
  fun d => (epsilon ^ N)⁻¹ * BrandenLeite.regularizedSequence N a epsilon d

/-- The coefficient sequence of `(1 + X)^N`. -/
def binomialSymbolCoeff (N : ℕ) : ℕ → ℝ :=
  fun d => (N.choose d : ℝ)

theorem binomialSymbolCoeff_eq_shiftedPowerCoeffs (N : ℕ) :
    binomialSymbolCoeff N = BrandenLeite.shiftedPowerCoeffs N 1 := by
  funext d
  simp only [binomialSymbolCoeff, BrandenLeite.shiftedPowerCoeffs]
  rw [Polynomial.coeff_X_add_C_pow]
  simp

/-- The rank-`n` Chow row of the finite binomial symbol `(1 + X)^N`. -/
def binomialSymbolChow (N n : ℕ) : ℝ[X] :=
  chowPolynomial (toeplitz (binomialSymbolCoeff N)) n

/-- The projectively regularized rank-`n` Chow row. -/
def projectiveRegularizedChow
    (N : ℕ) (a : ℕ → ℝ) (epsilon : ℝ) (n : ℕ) : ℝ[X] :=
  chowPolynomial (toeplitz (projectiveRegularizedSequence N a epsilon)) n

@[simp]
theorem projectiveRegularizedSequence_zero
    (N : ℕ) (a : ℕ → ℝ) (epsilon : ℝ) :
    projectiveRegularizedSequence N a epsilon 0 = a 0 := by
  simp [projectiveRegularizedSequence,
    BrandenLeite.regularizedSequence_zero, geometricScale]

/-- The special fiber depends only on the initial tail coefficient. -/
theorem projectiveRegularizedSequence_at_zero
    (N : ℕ) (a : ℕ → ℝ) (d : ℕ) :
    projectiveRegularizedSequence N a 0 d =
      (N.choose d : ℝ) * a 0 := by
  simp only [projectiveRegularizedSequence,
    BrandenLeite.regularizedSequence, natCauchyConvolution,
    BrandenLeite.shiftedPowerCoeffs, geometricScale]
  rw [Finset.sum_eq_single d]
  · rw [Polynomial.coeff_X_add_C_pow]
    simp
  · intro b hb hbd
    have hb_lt : b < d := by
      have := Finset.mem_range.mp hb
      lia
    simp [show d - b ≠ 0 by lia]
  · simp

theorem projectiveRegularizedSequence_at_zero_eq_binomial
    {a : ℕ → ℝ} (ha0 : a 0 = 1) (N : ℕ) :
    projectiveRegularizedSequence N a 0 = binomialSymbolCoeff N := by
  funext d
  simp [projectiveRegularizedSequence_at_zero, binomialSymbolCoeff, ha0]

@[simp]
theorem projectiveRegularizedChow_at_zero
    {a : ℕ → ℝ} (ha0 : a 0 = 1) (N n : ℕ) :
    projectiveRegularizedChow N a 0 n = binomialSymbolChow N n := by
  simp [projectiveRegularizedChow, binomialSymbolChow,
    projectiveRegularizedSequence_at_zero_eq_binomial ha0]

@[simp]
theorem projectiveRegularizedSequence_zero_prefix
    (a : ℕ → ℝ) (epsilon : ℝ) :
    projectiveRegularizedSequence 0 a epsilon = geometricScale epsilon a := by
  funext d
  simp only [projectiveRegularizedSequence,
    BrandenLeite.regularizedSequence, natCauchyConvolution,
    BrandenLeite.shiftedPowerCoeffs, pow_zero, geometricScale]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb0
    simp [Polynomial.coeff_one, hb0]
  · simp

/-- Every fixed regularized coefficient converges to its binomial special
fiber as `epsilon` tends to zero. -/
theorem tendsto_projectiveRegularizedSequence
    {I : Type*} {l : Filter I} {epsilon : I → ℝ}
    (hepsilon : Tendsto epsilon l (𝓝 0))
    (N : ℕ) (a : ℕ → ℝ) (d : ℕ) :
    Tendsto (fun k => projectiveRegularizedSequence N a (epsilon k) d) l
      (𝓝 ((N.choose d : ℝ) * a 0)) := by
  rw [← projectiveRegularizedSequence_at_zero N a d]
  unfold projectiveRegularizedSequence BrandenLeite.regularizedSequence
    natCauchyConvolution
  apply tendsto_finsetSum
  intro i _
  exact tendsto_const_nhds.mul
    ((hepsilon.pow (d - i)).mul_const (a (d - i)))

/-- Fixed Chow coefficients converge to those of the finite binomial special
fiber. -/
theorem tendsto_coeff_projectiveRegularizedChow
    {I : Type*} {l : Filter I} {epsilon : I → ℝ}
    (hepsilon : Tendsto epsilon l (𝓝 0))
    {a : ℕ → ℝ} (ha0 : a 0 = 1) (N n d : ℕ) :
    Tendsto
      (fun k => (projectiveRegularizedChow N a (epsilon k) n).coeff d) l
      (𝓝 ((binomialSymbolChow N n).coeff d)) := by
  simpa [projectiveRegularizedChow, binomialSymbolChow] using
    tendsto_coeff_chowPolynomial_toeplitz
      (fun k => projectiveRegularizedSequence N a (epsilon k))
      (binomialSymbolCoeff N) n
      (fun m _ => by
        simpa [binomialSymbolCoeff, ha0] using
          tendsto_projectiveRegularizedSequence hepsilon N a m) d

/-- Nonnegative projective parameters preserve the PF property. -/
theorem projectiveRegularizedSequence_isPolyaFreqSeq
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (N : ℕ) :
    IsPolyaFreqSeq (projectiveRegularizedSequence N a epsilon) := by
  exact BrandenLeite.regularizedSequence_isPolyaFreqSeq
    (ha.geometricScale epsilon hepsilon) N zero_le_one

/-- Division-free comparison of the two epsilon regularizations. -/
theorem geometricScale_regularizedSequence
    (N : ℕ) (a : ℕ → ℝ) (epsilon : ℝ) :
    geometricScale epsilon (BrandenLeite.regularizedSequence N a epsilon) =
      fun d => epsilon ^ N * projectiveRegularizedSequence N a epsilon d := by
  funext d
  simp only [geometricScale, projectiveRegularizedSequence,
    BrandenLeite.regularizedSequence, natCauchyConvolution,
    BrandenLeite.shiftedPowerCoeffs]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_add_C_pow]
  have hkd : k ≤ d := by
    have := Finset.mem_range.mp hk
    lia
  by_cases hkN : k ≤ N
  · have hpow : epsilon ^ d * epsilon ^ (N - k) =
        epsilon ^ N * epsilon ^ (d - k) := by
      rw [← pow_add, ← pow_add]
      congr 1
      lia
    simp only [one_pow, one_mul]
    calc
      epsilon ^ d *
          (epsilon ^ (N - k) * (N.choose k : ℝ) * a (d - k)) =
          (epsilon ^ d * epsilon ^ (N - k)) *
            (N.choose k : ℝ) * a (d - k) := by ring
      _ = epsilon ^ N * epsilon ^ (d - k) *
            (N.choose k : ℝ) * a (d - k) := by rw [hpow]
      _ = epsilon ^ N *
          ((N.choose k : ℝ) * (epsilon ^ (d - k) * a (d - k))) := by ring
  · have hNk : N < k := lt_of_not_ge hkN
    rw [Nat.choose_eq_zero_of_lt hNk]
    simp

@[simp]
theorem unitNormalizedRegularizedSequence_zero
    {N : ℕ} {a : ℕ → ℝ} {epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    unitNormalizedRegularizedSequence N a epsilon 0 = a 0 := by
  simp [unitNormalizedRegularizedSequence,
    BrandenLeite.regularizedSequence_zero, pow_ne_zero N hepsilon]

/-- For nonzero epsilon, the projective family is geometric scaling of the
unit-origin normalization of the paper's raw approximant. -/
theorem geometricScale_unitNormalizedRegularizedSequence
    {epsilon : ℝ} (hepsilon : epsilon ≠ 0) (N : ℕ) (a : ℕ → ℝ) :
    geometricScale epsilon
        (unitNormalizedRegularizedSequence N a epsilon) =
      projectiveRegularizedSequence N a epsilon := by
  funext d
  have hscale := congrFun
    (geometricScale_regularizedSequence N a epsilon) d
  simp only [geometricScale] at hscale ⊢
  rw [unitNormalizedRegularizedSequence]
  calc
    epsilon ^ d *
        ((epsilon ^ N)⁻¹ *
          BrandenLeite.regularizedSequence N a epsilon d) =
        (epsilon ^ N)⁻¹ *
          (epsilon ^ d *
            BrandenLeite.regularizedSequence N a epsilon d) := by ring
    _ = (epsilon ^ N)⁻¹ *
        (epsilon ^ N * projectiveRegularizedSequence N a epsilon d) := by
      rw [hscale]
    _ = projectiveRegularizedSequence N a epsilon d := by
      simp [pow_ne_zero N hepsilon]

/-- At each positive parameter, rank homogeneity supplies exactly the scalar
`epsilon ^ n`; the Chow variable itself is not rescaled. -/
theorem projectiveRegularizedChow_eq_scaled_normalized
    {epsilon : ℝ} (hepsilon : epsilon ≠ 0)
    (N : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    projectiveRegularizedChow N a epsilon n =
      C (epsilon ^ n) *
        chowPolynomial
          (toeplitz (unitNormalizedRegularizedSequence N a epsilon)) n := by
  rw [projectiveRegularizedChow,
    ← geometricScale_unitNormalizedRegularizedSequence hepsilon N a]
  exact chowPolynomial_toeplitz_geometricScale epsilon
    (unitNormalizedRegularizedSequence N a epsilon) n

theorem toeplitz_projectiveRegularizedSequence_isLowerUnitriangular
    {a : ℕ → ℝ} (ha0 : a 0 = 1) (N : ℕ) (epsilon : ℝ) :
    LowerTriangularMatrix.IsLowerUnitriangular
      (toeplitz (projectiveRegularizedSequence N a epsilon)) := by
  constructor
  · intro i j hij
    simp [toeplitz_apply, Nat.not_le_of_lt hij]
  · intro n
    simp [toeplitz_apply, ha0]

/-- Every projectively regularized Chow row is PF. -/
theorem projectiveRegularizedChow_isPFPolynomial
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (ha0 : a 0 = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (N n : ℕ) :
    IsPFPolynomial (projectiveRegularizedChow N a epsilon n) := by
  rw [projectiveRegularizedChow]
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact chowPolynomial_nonnegCoeffs_of_isTotallyNonneg
      (toeplitz_projectiveRegularizedSequence_isLowerUnitriangular
        ha0 N epsilon)
      (projectiveRegularizedSequence_isPolyaFreqSeq ha hepsilon N) n
  · exact chowPolynomial_eq_zero_or_splits_of_isTotallyNonneg
      (toeplitz_projectiveRegularizedSequence_isLowerUnitriangular
        ha0 N epsilon)
      (projectiveRegularizedSequence_isPolyaFreqSeq ha hepsilon N) n

/-- Consecutive projectively regularized Chow rows are in zero-aware proper
position. -/
theorem projectiveRegularizedChow_prec0_succ
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (ha0 : a 0 = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (N n : ℕ) :
    Interl (projectiveRegularizedChow N a epsilon n)
      (projectiveRegularizedChow N a epsilon (n + 1)) := by
  rw [projectiveRegularizedChow, projectiveRegularizedChow]
  exact chowPolynomial_prec0_succ_of_isTotallyNonneg
    (toeplitz_projectiveRegularizedSequence_isLowerUnitriangular
      ha0 N epsilon)
    (projectiveRegularizedSequence_isPolyaFreqSeq ha hepsilon N) n

/-- The finite binomial special-fiber Chow row is PF. -/
theorem binomialSymbolChow_isPFPolynomial (N n : ℕ) :
    IsPFPolynomial (binomialSymbolChow N n) := by
  have hone : IsPolyaFreqSeq (fun _ : ℕ => (1 : ℝ)) := by
    simpa using geometric_isPolyaFreqSeq (1 : ℝ) zero_le_one
  have h := projectiveRegularizedChow_isPFPolynomial
    hone (a := fun _ : ℕ => (1 : ℝ)) (by simp)
    (epsilon := 0) (by norm_num) N n
  simpa using h

theorem binomialSymbolChow_eq_zero_or_splits (N n : ℕ) :
    binomialSymbolChow N n = 0 ∨ (binomialSymbolChow N n).Splits :=
  (binomialSymbolChow_isPFPolynomial N n).eq_zero_or_splits

/-- Consecutive finite binomial special-fiber rows are in zero-aware proper
position. -/
theorem binomialSymbolChow_prec0_succ (N n : ℕ) :
    Interl (binomialSymbolChow N n) (binomialSymbolChow N (n + 1)) := by
  have hone : IsPolyaFreqSeq (fun _ : ℕ => (1 : ℝ)) := by
    simpa using geometric_isPolyaFreqSeq (1 : ℝ) zero_le_one
  have h := projectiveRegularizedChow_prec0_succ
    hone (a := fun _ : ℕ => (1 : ℝ)) (by simp)
    (epsilon := 0) (by norm_num) N n
  simpa using h

end

end RealRooted.BrandenVecchi
