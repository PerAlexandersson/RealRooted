import RealRooted.BrandenLeite.DiagonalTail
import RealRooted.Hadamard.Grace
import RealRooted.PFPolynomial.Closure
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Coefficient limits of finite kernel rows

Finite matrix multiplication and powers are continuous in the entrywise
topology.  We combine that fact with the finite source-border chain theorem to
pass PF and proper-position certificates to strictly lower kernel rows.
-/

open Filter Matrix Polynomial Topology

namespace RealRooted.BrandenLeite

noncomputable section

/-- Entrywise convergence of finite matrices gives coefficientwise convergence
of every regularized kernel row. -/
theorem tendsto_coeff_regularizedKernelRow
    {N : ℕ} (G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    {H : ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    {K : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hH : ∀ i j, Tendsto (fun m => H m i j) atTop (𝓝 (K i j)))
    (i : Fin (N + 1)) (q : ℕ) :
    Tendsto (fun m => (regularizedKernelRow G (H m) i).coeff q) atTop
      (𝓝 ((regularizedKernelRow G K i).coeff q)) := by
  by_cases hq : q < N + 1
  · rw [coeff_regularizedKernelRow, ite_eq_left hq]
    simp_rw [coeff_regularizedKernelRow, ite_eq_left hq]
    have hHmat : Tendsto H atTop (𝓝 K) := by
      exact tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr (hH a)
    have hGHmat : Tendsto (fun m => G * H m) atTop (𝓝 (G * K)) :=
      tendsto_const_nhds.mul hHmat
    have hLmat : Tendsto
        (fun m => Matrix.strictLowerPart (G * H m)) atTop
        (𝓝 (Matrix.strictLowerPart (G * K))) := by
      apply tendsto_pi_nhds.mpr
      intro a
      apply tendsto_pi_nhds.mpr
      intro b
      have hab := (tendsto_pi_nhds.mp
        (tendsto_pi_nhds.mp hGHmat a) b)
      by_cases hba : b < a
      · simpa [Matrix.strictLowerPart, hba] using hab
      · simp [Matrix.strictLowerPart, hba]
    have hresult : Tendsto
        (fun m => Matrix.strictLowerPart (G * H m) ^ q * G) atTop
        (𝓝 (Matrix.strictLowerPart (G * K) ^ q * G)) :=
      (hLmat.pow q).mul tendsto_const_nhds
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hresult i) 0
  · have hq' : ¬q < N + 1 := hq
    simp [coeff_regularizedKernelRow, hq']

/-- Every regularized row in a positive finite approximation is PF. -/
theorem regularizedKernelRow_isPFPolynomial
    {N : ℕ} {g η : ℝ}
    {G H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hg : 0 < g) (hη : 0 < η)
    (hG : G.IsTotallyNonneg) (hH : H.IsTotallyNonneg)
    (hGlower : ∀ i j, i < j → G i j = 0)
    (hHlower : ∀ i j, i < j → H i j = 0)
    (hGdiag : ∀ i, G i i = g) (hHdiag : ∀ i, H i i = η)
    (i : Fin (N + 1)) :
    IsPFPolynomial (regularizedKernelRow G H i) := by
  have hcert := sourceBorder_certificate hg hη hG hH hGlower hHlower
    hGdiag hHdiag
  have hchain := chainPolynomial_toLowerTriangularMatrix_isPFPolynomial
    (mul_pos hg hη) hcert.1 hcert.2.1 hcert.2.2
    (show i.val + 1 < N + 2 by lia)
  change IsPFPolynomial
    (chainPolynomial (sourceBorderLowerTriangularMatrix (g * η) G H)
      (i.val + 1)) at hchain
  rw [chainPolynomial_sourceBorder_eq_X_mul_regularizedKernelRow
    (g * η) G H i] at hchain
  exact isPFPolynomial_of_X_mul hchain

/-- Consecutive regularized rows in a positive finite approximation are in
zero-aware proper position. -/
theorem prec0_regularizedKernelRow_succ
    {N : ℕ} {g η : ℝ}
    {G H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hg : 0 < g) (hη : 0 < η)
    (hG : G.IsTotallyNonneg) (hH : H.IsTotallyNonneg)
    (hGlower : ∀ i j, i < j → G i j = 0)
    (hHlower : ∀ i j, i < j → H i j = 0)
    (hGdiag : ∀ i, G i i = g) (hHdiag : ∀ i, H i i = η)
    (i : Fin N) :
    Interl (regularizedKernelRow G H i.castSucc)
      (regularizedKernelRow G H i.succ) := by
  have hcert := sourceBorder_certificate hg hη hG hH hGlower hHlower
    hGdiag hHdiag
  have hchain := prec0_chainPolynomial_toLowerTriangularMatrix_succ
    (n := i.val + 1) (mul_pos hg hη) hcert.1 hcert.2.1 hcert.2.2
    (show i.val + 1 + 1 < N + 2 by lia)
  change Interl
    (chainPolynomial (sourceBorderLowerTriangularMatrix (g * η) G H)
      (i.castSucc.val + 1))
    (chainPolynomial (sourceBorderLowerTriangularMatrix (g * η) G H)
      (i.succ.val + 1)) at hchain
  rw [chainPolynomial_sourceBorder_eq_X_mul_regularizedKernelRow
      (g * η) G H i.castSucc,
    chainPolynomial_sourceBorder_eq_X_mul_regularizedKernelRow
      (g * η) G H i.succ] at hchain
  apply hchain.of_mul_X_both_of_nonneg
  · exact (regularizedKernelRow_isPFPolynomial hg hη hG hH hGlower
      hHlower hGdiag hHdiag i.castSucc).hasNonnegCoeffs
  · exact (regularizedKernelRow_isPFPolynomial hg hη hG hH hGlower
      hHlower hGdiag hHdiag i.succ).hasNonnegCoeffs

/-- Strictly lower entrywise limits of positive-diagonal TN approximations
have PF kernel rows and consecutive zero-aware proper position. -/
theorem kernelRows_pf_and_prec0_of_tendsto
    {N : ℕ} {g : ℝ} {η : ℕ → ℝ}
    {G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    {H : ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    {K : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hg : 0 < g) (hη : ∀ m, 0 < η m)
    (hG : G.IsTotallyNonneg) (hH : ∀ m, (H m).IsTotallyNonneg)
    (hGlower : ∀ i j, i < j → G i j = 0)
    (hHlower : ∀ m i j, i < j → H m i j = 0)
    (hKstrict : ∀ i j, i.val ≤ j.val → K i j = 0)
    (hGdiag : ∀ i, G i i = g) (hHdiag : ∀ m i, H m i i = η m)
    (hlim : ∀ i j, Tendsto (fun m => H m i j) atTop (𝓝 (K i j))) :
    (∀ i, IsPFPolynomial (kernelRow G K i)) ∧
      ∀ i : Fin N, Interl (kernelRow G K i.castSucc)
        (kernelRow G K i.succ) := by
  have hKlower : ∀ i j, i < j → K i j = 0 := by
    intro i j hij
    exact hKstrict i j (Fin.mk_le_mk.mpr hij.le)
  have hGKdiag : ∀ i, (G * K) i i = 0 := by
    intro i
    exact Matrix.mul_apply_eq_zero_of_le_of_lower_strictLower G K hGlower
      hKstrict (le_refl i.val)
  have hregularized_eq : ∀ i, regularizedKernelRow G K i = kernelRow G K i :=
    fun i => regularizedKernelRow_eq_kernelRow_of_diagonal_zero G K hGlower
      hKlower hGKdiag i
  constructor
  · intro i
    rw [← hregularized_eq i]
    apply IsPFPolynomial.of_coeff_tendsto
      (fun m => regularizedKernelRow_isPFPolynomial hg (hη m) hG (hH m)
        hGlower (hHlower m) hGdiag (hHdiag m) i)
    exact tendsto_coeff_regularizedKernelRow G hlim i
  · intro i
    rw [← hregularized_eq i.castSucc, ← hregularized_eq i.succ]
    apply prec0_of_pf_coeff_tendsto_of_natDegree_le
      (fun m => regularizedKernelRow_isPFPolynomial hg (hη m) hG (hH m)
        hGlower (hHlower m) hGdiag (hHdiag m) i.castSucc)
      (fun m => regularizedKernelRow_isPFPolynomial hg (hη m) hG (hH m)
        hGlower (hHlower m) hGdiag (hHdiag m) i.succ)
      (fun m => prec0_regularizedKernelRow_succ hg (hη m) hG (hH m)
        hGlower (hHlower m) hGdiag (hHdiag m) i)
      (fun m => (natDegree_regularizedKernelRow_le_row G (H m) hGlower
        i.castSucc).trans (Nat.le_succ i.val))
      (fun m => natDegree_regularizedKernelRow_le_row G (H m) hGlower i.succ)
      (tendsto_coeff_regularizedKernelRow G hlim i.castSucc)
      (tendsto_coeff_regularizedKernelRow G hlim i.succ)

end

end RealRooted.BrandenLeite
