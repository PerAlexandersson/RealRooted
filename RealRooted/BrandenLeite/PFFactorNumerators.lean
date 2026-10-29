module

public import RealRooted.BrandenLeite.SourceBorderKernel
public import RealRooted.BrandenLeite.ToeplitzComposition
public import RealRooted.BrandenLeite.TwoKernelAlgebra
import RealRooted.PFPolynomial
import RealRooted.BrandenLeite.KernelClosure
import RealRooted.BrandenLeite.TwoKernel
import RealRooted.BrandenLeite.ConstantDiagonal
import RealRooted.BrandenLeite.DiagonalTail
import RealRooted.BrandenLeite.Theorem37
import RealRooted.BrandenLeite.ZeroConstant
import RealRooted.Mathlib.Algebra.Polynomial.Coeff
import RealRooted.PFPolynomial.Closure

/-!
# Numerators associated with two Pólya-frequency factors

We formalize the positive-constant-term part of issue #2160.  For coefficient
sequences `g` and `h`, `pfFactorNumerator g h n` is the coefficient of `z^n`
in

`g(z) / (1 - X * (g(z) * h(z) - g(0) * h(0)))`.

The main result identifies these rows with the regularized kernel rows of the
finite Toeplitz factors.  The total-nonnegative source-border theorem of
Brändén--Saud Leite then gives Pólya-frequency rows and consecutive
zero-aware interlacing.  See Brändén--Saud Leite, arXiv:2412.06595v3,
§§3--4.
-/

@[expose] public section

open Filter Matrix Polynomial BigOperators Topology

namespace RealRooted.BrandenLeite

noncomputable section

/-- The `n`th numerator row associated with coefficient sequences `g` and
`h`.  The constant term is removed from their product before the geometric
series is formed. -/
def pfFactorNumerator (g h : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ q ∈ Finset.range (n + 1),
    C (PowerSeries.coeff n
      (PowerSeries.mk g *
        positivePartSeries
          (fun k ↦ PowerSeries.coeff k
            (PowerSeries.mk g * PowerSeries.mk h)) ^ q)) * X ^ q

/-- Every PF-factor numerator has degree at most its coefficient index. -/
theorem natDegree_pfFactorNumerator_le (g h : ℕ → ℝ) (n : ℕ) :
    (pfFactorNumerator g h n).natDegree ≤ n := by
  unfold pfFactorNumerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q hq
  exact (Polynomial.natDegree_C_mul_X_pow_le _ q).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hq))

/-- The coefficient formula expressing the numerator row as the coefficient
of `g(z) * (g(z)h(z) - g(0)h(0)) ^ q`. -/
theorem coeff_pfFactorNumerator (g h : ℕ → ℝ) (n q : ℕ) :
    (pfFactorNumerator g h n).coeff q =
      PowerSeries.coeff n
        (PowerSeries.mk g *
          positivePartSeries
            (fun k ↦ PowerSeries.coeff k
              (PowerSeries.mk g * PowerSeries.mk h)) ^ q) := by
  unfold pfFactorNumerator
  simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
  rw [Polynomial.coeff_sum_range_monomial]
  by_cases hq : q ≤ n
  · simp [hq]
  · rw [ite_eq_right (by lia)]
    symm
    rw [PowerSeries.coeff_mul, Finset.sum_eq_zero]
    intro p hp
    rw [coeff_pow_eq_zero_of_lt
      (constantCoeff_positivePartSeries
        (fun k ↦ PowerSeries.coeff k
          (PowerSeries.mk g * PowerSeries.mk h))) (by
        have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        lia), mul_zero]

/-- The initial numerator row is the constant coefficient of the first
factor. -/
@[simp]
theorem pfFactorNumerator_zero (g h : ℕ → ℝ) :
    pfFactorNumerator g h 0 = C (g 0) := by
  ext q
  rw [coeff_pfFactorNumerator]
  cases q with
  | zero => simp
  | succ q =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff,
        constantCoeff_positivePartSeries]

/-- With unit first factor, the PF-factor numerator is the ordinary
Brändén--Saud Leite composition row of the positive-order part. -/
theorem pfFactorNumerator_one_eq_compositionRow (h : ℕ → ℝ) (n : ℕ) :
    pfFactorNumerator
        (fun k ↦ PowerSeries.coeff k (1 : PowerSeries ℝ)) h n =
      compositionRow (positivePartSeries h) n := by
  have hs : positivePartSeries
      (fun k ↦ PowerSeries.coeff k (PowerSeries.mk h)) =
      positivePartSeries h := by
    ext k
    simp [coeff_positivePartSeries]
  ext q
  rw [coeff_pfFactorNumerator,
    coeff_compositionRow (constantCoeff_positivePartSeries h)]
  simp only [mk_coeff_eq, one_mul, hs]

/-- The strict-lower part of a finite Toeplitz product is the finite Toeplitz
matrix of the positive-order part of the product series. -/
private theorem strictLowerPart_finiteToeplitz_mul
    (g h : ℕ → ℝ) (N : ℕ) :
    Matrix.strictLowerPart (finiteToeplitz g N * finiteToeplitz h N) =
      finiteToeplitz
        (fun k ↦ PowerSeries.coeff k
          (positivePartSeries
            (fun m ↦ PowerSeries.coeff m
              (PowerSeries.mk g * PowerSeries.mk h)))) N := by
  rw [finiteToeplitz_mul]
  ext i j
  by_cases hji : j < i
  · rw [Matrix.strictLowerPart_apply_of_lt _ hji,
      finiteToeplitz_apply, finiteToeplitz_apply, ite_eq_left hji.le]
    rw [coeff_positivePartSeries_of_pos _
      (Nat.sub_pos_of_lt (Fin.mk_lt_mk.mp hji)), ite_eq_left hji.le]
  · rw [Matrix.strictLowerPart_apply_of_not_lt _ hji]
    rw [finiteToeplitz_apply]
    by_cases hle : j ≤ i
    · have hij : i = j := le_antisymm (le_of_not_gt hji) hle
      subst j
      simp
    · simp [hle]

/-- The root interval in the chain-polynomial theorem after undoing a
positive constant-diagonal normalization. -/
private theorem roots_chainPolynomial_mem_Icc_of_pos_constantDiagonal
    {δ : ℝ} {A : LowerTriangularMatrix ℝ} (hδ : 0 < δ)
    (hlower : LowerTriangularMatrix.IsLowerTriangular A)
    (hdiag : ∀ n, A n n = δ) (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    ∀ x ∈ (chainPolynomial A n).roots, x ∈ Set.Icc (-δ⁻¹) 0 := by
  let B := normalizeConstantDiagonal δ A
  have hunit : LowerTriangularMatrix.IsLowerUnitriangular B :=
    normalizeConstantDiagonal_unit hδ.ne' hlower hdiag
  have hB : Matrix.IsTotallyNonneg B :=
    normalizeConstantDiagonal_isTotallyNonneg hδ hA
  have heq : chainPolynomial A n =
      (chainPolynomial B n).comp (C δ * X) := by
    simpa [B] using
      chainPolynomial_comp_C_mul_X_normalizeConstantDiagonal hδ.ne' n
  intro x hx
  have hne : chainPolynomial A n ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hBne : chainPolynomial B n ≠ 0 := by
    intro hzero
    apply hne
    rw [heq, hzero, zero_comp]
  have hxroot : (chainPolynomial B n).IsRoot (δ * x) := by
    have hxeval := (Polynomial.mem_roots hne).mp hx
    rw [heq] at hxeval
    simpa using Polynomial.isRoot_comp.mp hxeval
  have hxbounds := roots_chainPolynomial_mem_Icc_of_isTotallyNonneg
    hunit hB n (δ * x) ((Polynomial.mem_roots hBne).mpr hxroot)
  constructor
  · rw [show -δ⁻¹ = (-1) / δ by simp [div_eq_mul_inv]]
    exact (div_le_iff₀ hδ).2 (by simpa [mul_comm] using hxbounds.1)
  · exact nonpos_of_mul_nonpos_left (by
      simpa [mul_comm] using hxbounds.2) hδ

/-- Roots of a regularized kernel row of two positive constant-diagonal lower
TN factors lie in the sharp interval determined by the product diagonal. -/
theorem roots_regularizedKernelRow_mem_Icc
    {N : ℕ} {g η : ℝ}
    {G H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hg : 0 < g) (hη : 0 < η)
    (hG : G.IsTotallyNonneg) (hH : H.IsTotallyNonneg)
    (hGlower : ∀ i j, i < j → G i j = 0)
    (hHlower : ∀ i j, i < j → H i j = 0)
    (hGdiag : ∀ i, G i i = g) (hHdiag : ∀ i, H i i = η)
    (i : Fin (N + 1)) :
    ∀ x ∈ (regularizedKernelRow G H i).roots,
      x ∈ Set.Icc (-(g * η)⁻¹) 0 := by
  let S := sourceBorder (g * η) G H
  let A := Matrix.diagonalTail (g * η) S
  have hcert := sourceBorder_certificate hg hη hG hH hGlower hHlower
    hGdiag hHdiag
  have hlower : LowerTriangularMatrix.IsLowerTriangular A :=
    diagonalTail_isLowerTriangular hcert.2.1
  have hdiag : ∀ n, A n n = g * η :=
    fun _ ↦ Matrix.diagonalTail_apply_diagonal (g * η) S hcert.2.2
  have hA : Matrix.IsTotallyNonneg A :=
    hcert.1.diagonalTail (mul_pos hg hη).le
  have hchain : chainPolynomial A (i.val + 1) =
      X * regularizedKernelRow G H i := by
    calc
      chainPolynomial A (i.val + 1) =
          chainPolynomial (Matrix.toLowerTriangularMatrix S)
            (i.val + 1) := by
        exact chainPolynomial_diagonalTail_eq_toLowerTriangularMatrix
          (g * η) S (by lia)
      _ = X * regularizedKernelRow G H i :=
        chainPolynomial_sourceBorder_eq_X_mul_regularizedKernelRow
          (g * η) G H i
  intro x hx
  have hrowne : regularizedKernelRow G H i ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hchainne : chainPolynomial A (i.val + 1) ≠ 0 := by
    rw [hchain]
    exact mul_ne_zero X_ne_zero hrowne
  have hxroot : (chainPolynomial A (i.val + 1)).IsRoot x := by
    rw [hchain, Polynomial.IsRoot.def, Polynomial.eval_mul]
    have hxrow := (Polynomial.mem_roots hrowne).mp hx
    simp only [Polynomial.eval_X, mul_eq_zero]
    exact Or.inr hxrow
  exact roots_chainPolynomial_mem_Icc_of_pos_constantDiagonal
    (mul_pos hg hη) hlower hdiag hA (i.val + 1) x
      ((Polynomial.mem_roots hchainne).mpr hxroot)

/-- Entrywise convergence of both finite factors gives coefficientwise
convergence of their regularized kernel rows. -/
theorem tendsto_coeff_regularizedKernelRow_of_tendsto
    {N : ℕ}
    {G H : ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    {G₀ H₀ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hG : ∀ i j, Filter.Tendsto (fun m ↦ G m i j) Filter.atTop (𝓝 (G₀ i j)))
    (hH : ∀ i j, Filter.Tendsto (fun m ↦ H m i j) Filter.atTop (𝓝 (H₀ i j)))
    (i : Fin (N + 1)) (q : ℕ) :
    Filter.Tendsto
      (fun m ↦ (regularizedKernelRow (G m) (H m) i).coeff q)
      Filter.atTop
      (𝓝 ((regularizedKernelRow G₀ H₀ i).coeff q)) := by
  by_cases hq : q < N + 1
  · rw [coeff_regularizedKernelRow, ite_eq_left hq]
    simp_rw [coeff_regularizedKernelRow, ite_eq_left hq]
    have hGmat : Filter.Tendsto G Filter.atTop (𝓝 G₀) :=
      tendsto_pi_nhds.mpr fun a ↦ tendsto_pi_nhds.mpr (hG a)
    have hHmat : Filter.Tendsto H Filter.atTop (𝓝 H₀) :=
      tendsto_pi_nhds.mpr fun a ↦ tendsto_pi_nhds.mpr (hH a)
    have hGHmat : Filter.Tendsto (fun m ↦ G m * H m) Filter.atTop
        (𝓝 (G₀ * H₀)) := hGmat.mul hHmat
    have hLmat : Filter.Tendsto
        (fun m ↦ Matrix.strictLowerPart (G m * H m)) Filter.atTop
        (𝓝 (Matrix.strictLowerPart (G₀ * H₀))) := by
      apply tendsto_pi_nhds.mpr
      intro a
      apply tendsto_pi_nhds.mpr
      intro b
      have hab := tendsto_pi_nhds.mp
        (tendsto_pi_nhds.mp hGHmat a) b
      by_cases hba : b < a
      · simpa [Matrix.strictLowerPart, hba] using hab
      · simp [Matrix.strictLowerPart, hba]
    have hresult : Filter.Tendsto
        (fun m ↦ Matrix.strictLowerPart (G m * H m) ^ q * G m)
        Filter.atTop
        (𝓝 (Matrix.strictLowerPart (G₀ * H₀) ^ q * G₀)) :=
      (hLmat.pow q).mul hGmat
    exact tendsto_pi_nhds.mp
      (tendsto_pi_nhds.mp hresult i) 0
  · simp [coeff_regularizedKernelRow, hq]

/-- A numerator row is the corresponding row of every finite Toeplitz
regularized-kernel construction containing that index. -/
theorem pfFactorNumerator_eq_regularizedKernelRow_fin
    (g h : ℕ → ℝ) {N : ℕ} (i : Fin (N + 1)) :
    pfFactorNumerator g h i.val =
      regularizedKernelRow (finiteToeplitz g N) (finiteToeplitz h N) i := by
  ext q
  rw [coeff_regularizedKernelRow]
  by_cases hq : q < N + 1
  · rw [ite_eq_left hq, strictLowerPart_finiteToeplitz_mul]
    rw [finiteToeplitz_pow, finiteToeplitz_mul, finiteToeplitz_apply]
    simp only [Fin.zero_le, ite_true, mk_coeff_eq]
    rw [mul_comm]
    unfold pfFactorNumerator
    simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
    rw [Polynomial.coeff_sum_range_monomial]
    by_cases hqi : q ≤ i.val
    · simp [hqi]
    · rw [ite_eq_right (by lia)]
      symm
      rw [PowerSeries.coeff_mul, Finset.sum_eq_zero]
      intro p hp
      rw [coeff_pow_eq_zero_of_lt
        (constantCoeff_positivePartSeries
          (fun m ↦ PowerSeries.coeff m
            (PowerSeries.mk g * PowerSeries.mk h))) (by
          have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          lia), mul_zero]
  · rw [ite_eq_right hq]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact (natDegree_pfFactorNumerator_le g h i.val).trans_lt (by lia)

/-- Pointwise convergence of both factors gives coefficientwise convergence
of every fixed numerator row. -/
theorem tendsto_coeff_pfFactorNumerator
    {g h : ℕ → ℕ → ℝ} {g₀ h₀ : ℕ → ℝ}
    (hg : ∀ i, Tendsto (fun m ↦ g m i) atTop (𝓝 (g₀ i)))
    (hh : ∀ i, Tendsto (fun m ↦ h m i) atTop (𝓝 (h₀ i)))
    (n q : ℕ) :
    Tendsto (fun m ↦ (pfFactorNumerator (g m) (h m) n).coeff q)
      atTop (𝓝 ((pfFactorNumerator g₀ h₀ n).coeff q)) := by
  have hG : ∀ i j,
      Tendsto (fun m ↦ finiteToeplitz (g m) n i j) atTop
        (𝓝 (finiteToeplitz g₀ n i j)) := by
    intro i j
    by_cases hji : j ≤ i
    · simpa [finiteToeplitz_apply, hji] using hg (i.val - j.val)
    · simp [hji]
  have hH : ∀ i j,
      Tendsto (fun m ↦ finiteToeplitz (h m) n i j) atTop
        (𝓝 (finiteToeplitz h₀ n i j)) := by
    intro i j
    by_cases hji : j ≤ i
    · simpa [finiteToeplitz_apply, hji] using hh (i.val - j.val)
    · simp [hji]
  have htendsto := tendsto_coeff_regularizedKernelRow_of_tendsto
    hG hH (Fin.last n) q
  simpa only [← pfFactorNumerator_eq_regularizedKernelRow_fin,
    Fin.val_last] using htendsto

/-- Positive-constant PF factors give a PF numerator row.  This includes
nonnegative coefficients, zero-aware real-rootedness, and nonpositive roots. -/
theorem pfFactorNumerator_isPFPolynomial_of_pos
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (hg0 : 0 < g 0) (hh0 : 0 < h 0) (n : ℕ) :
    IsPFPolynomial (pfFactorNumerator g h n) := by
  have hrow := regularizedKernelRow_isPFPolynomial hg0 hh0
    (finiteToeplitz_isTotallyNonneg hg n)
    (finiteToeplitz_isTotallyNonneg hh n)
    (fun i j hij ↦ by
      rw [finiteToeplitz_apply, ite_eq_right (not_le_of_gt hij)])
    (fun i j hij ↦ by
      rw [finiteToeplitz_apply, ite_eq_right (not_le_of_gt hij)])
    (fun i ↦ by simp)
    (fun i ↦ by simp)
    (Fin.last n)
  rw [← pfFactorNumerator_eq_regularizedKernelRow_fin g h (Fin.last n)] at hrow
  simpa using hrow

/-- PF factors, including factors with zero constant term and the zero
sequence, give a PF numerator row. -/
theorem pfFactorNumerator_isPFPolynomial
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (n : ℕ) : IsPFPolynomial (pfFactorNumerator g h n) := by
  obtain ⟨a, haPF, ha0, halim⟩ := exists_pf_pos_zero_approximation_of_pf hg
  obtain ⟨b, hbPF, hb0, hblim⟩ := exists_pf_pos_zero_approximation_of_pf hh
  apply IsPFPolynomial.of_coeff_tendsto
    (fun k ↦ pfFactorNumerator_isPFPolynomial_of_pos
      (haPF k) (hbPF k) (ha0 k) (hb0 k) n)
  exact tendsto_coeff_pfFactorNumerator halim hblim n

/-- If both PF factors have positive constant term, every root of the `n`th
numerator lies in `[-1 / (g(0)h(0)), 0]`. -/
theorem roots_pfFactorNumerator_mem_Icc_of_pos
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (hg0 : 0 < g 0) (hh0 : 0 < h 0) (n : ℕ) :
    ∀ x ∈ (pfFactorNumerator g h n).roots,
      x ∈ Set.Icc (-((g 0) * h 0)⁻¹) 0 := by
  have hroots := roots_regularizedKernelRow_mem_Icc hg0 hh0
    (finiteToeplitz_isTotallyNonneg hg n)
    (finiteToeplitz_isTotallyNonneg hh n)
    (fun i j hij ↦ by
      rw [finiteToeplitz_apply, ite_eq_right (not_le_of_gt hij)])
    (fun i j hij ↦ by
      rw [finiteToeplitz_apply, ite_eq_right (not_le_of_gt hij)])
    (fun i ↦ by simp)
    (fun i ↦ by simp)
    (Fin.last n)
  rw [← pfFactorNumerator_eq_regularizedKernelRow_fin g h (Fin.last n)] at hroots
  simpa using hroots

/-- Numerator rows of positive-constant PF factors consecutively interlace in
the zero-aware weak relation. -/
theorem interl_pfFactorNumerator_succ_of_pos
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (hg0 : 0 < g 0) (hh0 : 0 < h 0) (n : ℕ) :
    Interl (pfFactorNumerator g h n)
      (pfFactorNumerator g h (n + 1)) := by
  have hinterl := interl_regularizedKernelRow_succ hg0 hh0
    (finiteToeplitz_isTotallyNonneg hg (n + 1))
    (finiteToeplitz_isTotallyNonneg hh (n + 1))
    (fun i j hij ↦ by
      rw [finiteToeplitz_apply, ite_eq_right (not_le_of_gt hij)])
    (fun i j hij ↦ by
      rw [finiteToeplitz_apply, ite_eq_right (not_le_of_gt hij)])
    (fun i ↦ by simp)
    (fun i ↦ by simp)
    (Fin.last n)
  rw [← pfFactorNumerator_eq_regularizedKernelRow_fin g h
      (Fin.last n).castSucc,
    ← pfFactorNumerator_eq_regularizedKernelRow_fin g h
      (Fin.last n).succ] at hinterl
  simpa using hinterl

/-- Numerator rows of arbitrary PF factors consecutively interlace, with the
zero-aware convention covering vanishing rows. -/
theorem interl_pfFactorNumerator_succ
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (n : ℕ) :
    Interl (pfFactorNumerator g h n)
      (pfFactorNumerator g h (n + 1)) := by
  obtain ⟨a, haPF, ha0, halim⟩ := exists_pf_pos_zero_approximation_of_pf hg
  obtain ⟨b, hbPF, hb0, hblim⟩ := exists_pf_pos_zero_approximation_of_pf hh
  apply interl_of_pf_coeff_tendsto_of_natDegree_le
    (fun k ↦ pfFactorNumerator_isPFPolynomial_of_pos
      (haPF k) (hbPF k) (ha0 k) (hb0 k) n)
    (fun k ↦ pfFactorNumerator_isPFPolynomial_of_pos
      (haPF k) (hbPF k) (ha0 k) (hb0 k) (n + 1))
    (fun k ↦ interl_pfFactorNumerator_succ_of_pos
      (haPF k) (hbPF k) (ha0 k) (hb0 k) n)
    (fun _ ↦ (natDegree_pfFactorNumerator_le _ _ n).trans
      (Nat.le_succ n))
    (fun _ ↦ natDegree_pfFactorNumerator_le _ _ (n + 1))
    (tendsto_coeff_pfFactorNumerator halim hblim n)
    (tendsto_coeff_pfFactorNumerator halim hblim (n + 1))

/-- Positive-constant PF factors satisfy the complete rowwise PF and
consecutive-interlacing criterion. -/
theorem pfFactorNumerators_pf_and_interl_of_pos
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h)
    (hg0 : 0 < g 0) (hh0 : 0 < h 0) :
    (∀ n, IsPFPolynomial (pfFactorNumerator g h n)) ∧
      ∀ n, Interl (pfFactorNumerator g h n)
        (pfFactorNumerator g h (n + 1)) :=
  ⟨pfFactorNumerator_isPFPolynomial_of_pos hg hh hg0 hh0,
    interl_pfFactorNumerator_succ_of_pos hg hh hg0 hh0⟩

/-- Arbitrary PF factors satisfy the complete rowwise PF and
consecutive-interlacing criterion, including zero constants and zero rows. -/
theorem pfFactorNumerators_pf_and_interl
    {g h : ℕ → ℝ} (hg : IsPolyaFreqSeq g) (hh : IsPolyaFreqSeq h) :
    (∀ n, IsPFPolynomial (pfFactorNumerator g h n)) ∧
      ∀ n, Interl (pfFactorNumerator g h n)
        (pfFactorNumerator g h (n + 1)) :=
  ⟨pfFactorNumerator_isPFPolynomial hg hh,
    interl_pfFactorNumerator_succ hg hh⟩

end

end RealRooted.BrandenLeite
