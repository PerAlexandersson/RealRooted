import RealRooted.JacobiDeformation.Kernel
import RealRooted.SpectralProduct

/-!
# Newton-factor signs for Hermitian matrices

Let `A` be an entrywise nonnegative real symmetric `(N + 1) × (N + 1)` matrix
with simple spectrum whose increasing eigenvalues are the Jacobi eigenvalues
`λ_0 = 0 < λ_1 < ⋯ < λ_N`.  The Newton factors `Λ_k(A) = ∏_{l < k} (A - λ_l)`
are then the increasing spectral products of `RealRooted.SpectralProduct`,
hence entrywise nonnegative (Micchelli--Willoughby); they vanish for `k > N` by
Cayley--Hamilton, and `Λ_1(A) = A`.  Consequently the Newton polynomial of the
kernel weights, whose coefficients are nonnegative with `a_1 > 0`, evaluates
at `A` to a matrix that is strictly positive at every entry where `A` is.
The Newton degree may exceed the matrix dimension.
-/

open Finset Matrix Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## Spectral signs for the finite Jacobi kernel

The results below take the ordered-spectrum identity as a hypothesis and
retain the simple-spectrum hypothesis of the finite Micchelli--Willoughby
theorem; the Jacobi-specific diagonalization is supplied in
`RealRooted.JacobiDeformation.SpectralKernel`.
-/

/-- The Jacobi Newton polynomial is the ordered roots product of the first
`k` quadratic spectral nodes. -/
theorem newtonPolynomial_eq_rootsProduct (s : ℝ) (k : ℕ) :
    newtonPolynomial s k =
      rootsProduct (List.ofFn fun i : Fin k => eigenvalue s i) := by
  rw [newtonPolynomial, rootsProduct_eq_map_prod, List.map_ofFn,
    List.prod_ofFn]
  exact (Fin.prod_univ_eq_prod_range
    (fun i : ℕ => X - C (eigenvalue s i)) k).symm

/-- Matrix evaluation of a Jacobi Newton polynomial is the corresponding
initial spectral product once the increasing spectrum is identified. -/
theorem aeval_newtonPolynomial_eq_spectralInitialRoots {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (s : ℝ)
    (hspectrum : ∀ k, increasingEigenvalues A hA k = eigenvalue s k)
    (k : Fin (N + 1)) :
    aeval A (newtonPolynomial s k) =
      (spectralInitialRoots (increasingEigenvalues A hA) k |>.map
        fun r => A - r • 1).prod := by
  rw [newtonPolynomial_eq_rootsProduct, Matrix.aeval_rootsProduct]
  congr 2
  unfold spectralInitialRoots
  exact congrArg List.ofFn <| funext fun i =>
    (hspectrum ⟨i, i.isLt.trans k.isLt⟩).symm

/-- Every in-range Jacobi Newton factor product is entrywise nonnegative for
an entrywise nonnegative Hermitian matrix with the stated simple spectrum. -/
theorem aeval_newtonPolynomial_entry_nonneg {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (hentry : ∀ i j, 0 ≤ A i j)
    (hsimple : StrictAnti (sortedEigenvalues A hA))
    (s : ℝ)
    (hspectrum : ∀ k, increasingEigenvalues A hA k = eigenvalue s k)
    (k : Fin (N + 1)) (i j : Fin (N + 1)) :
    0 ≤ (aeval A (newtonPolynomial s k)) i j := by
  rw [aeval_newtonPolynomial_eq_spectralInitialRoots A hA s hspectrum k]
  exact spectralProduct_entrywise_nonneg A hA hentry hsimple k i j

/-- The full-size Jacobi Newton product vanishes by Cayley--Hamilton when the
ordered spectrum is the quadratic Jacobi spectrum. -/
theorem aeval_newtonPolynomial_succ_eq_zero {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (s : ℝ)
    (hspectrum : ∀ k, increasingEigenvalues A hA k = eigenvalue s k) :
    aeval A (newtonPolynomial s (N + 1)) = 0 := by
  have hpoly : newtonPolynomial s (N + 1) = A.charpoly := by
    calc
      newtonPolynomial s (N + 1) =
          rootsProduct (List.ofFn fun k : Fin (N + 1) => eigenvalue s k) :=
        newtonPolynomial_eq_rootsProduct s (N + 1)
      _ = rootsProduct
          (List.ofFn fun k : Fin (N + 1) => increasingEigenvalues A hA k) := by
        congr 2
        exact funext fun k => (hspectrum k).symm
      _ = A.charpoly := (charpoly_eq_rootsProduct_increasingEigenvalues A hA).symm
  rw [hpoly, Matrix.aeval_self_charpoly]

private theorem aeval_C_mul_apply {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (c : ℝ) (p : ℝ[X]) (i j : n) :
    (aeval A (C c * p)) i j = c * (aeval A p) i j := by
  rw [map_mul, aeval_C]
  simp [Matrix.mul_apply, Matrix.algebraMap_matrix_apply]

/-- A positive Newton combination of the Jacobi spectral products is strictly
positive at an entry where the matrix itself is strictly positive.  The final
`k = N + 1` factor is included in the polynomial and vanishes by
Cayley--Hamilton; strictness comes from the `k = 1` summand. -/
theorem aeval_weightNewtonPolynomial_entry_pos {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (hentry : ∀ i j, 0 ≤ A i j)
    (hsimple : StrictAnti (sortedEigenvalues A hA))
    {δ s : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s)
    (hspectrum : ∀ k, increasingEigenvalues A hA k = eigenvalue s k)
    (i j : Fin (N + 1)) (hij : 0 < A i j) :
    0 < (aeval A (weightNewtonPolynomial (N + 1) δ s)) i j := by
  rw [weightNewtonPolynomial, map_sum, Matrix.sum_apply]
  apply Finset.sum_pos'
  · intro k hk
    simp only [Finset.mem_range] at hk
    rw [aeval_C_mul_apply]
    have hcoeff : 0 < newtonCoefficient (N + 1) δ s k :=
      newtonCoefficient_pos (by lia) hδ hδ1 hs
    by_cases htop : k = N + 1
    · subst k
      rw [aeval_newtonPolynomial_succ_eq_zero A hA s hspectrum]
      simp
    · have hkN : k < N + 1 := by lia
      exact mul_nonneg hcoeff.le
        (aeval_newtonPolynomial_entry_nonneg A hA hentry hsimple s hspectrum
          ⟨k, hkN⟩ i j)
  · refine ⟨1, Finset.mem_range.mpr (by lia), ?_⟩
    rw [aeval_C_mul_apply]
    have hcoeff : 0 < newtonCoefficient (N + 1) δ s 1 :=
      newtonCoefficient_one_pos (by lia) hδ hδ1 hs
    have hone : aeval A (newtonPolynomial s 1) = A := by
      simp [newtonPolynomial, eigenvalue]
    rw [hone]
    exact mul_pos hcoeff hij

/-! ## Newton kernel signs above matrix dimension

The Newton weight degree may exceed the number of spectral nodes.  The extra
Newton factors vanish after matrix evaluation, so the strict entrywise sign
argument remains valid.
-/

/-- Every Newton factor at or above the matrix dimension vanishes under the
matrix evaluation determined by the exact quadratic spectrum. -/
theorem aeval_newtonPolynomial_eq_zero_of_dimension_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (s : ℝ)
    (hspectrum : ∀ k, increasingEigenvalues A hA k = eigenvalue s k)
    {k : ℕ} (hNk : N + 1 ≤ k) :
    aeval A (newtonPolynomial s k) = 0 := by
  induction k, hNk using Nat.le_induction with
  | base =>
      exact aeval_newtonPolynomial_succ_eq_zero A hA s hspectrum
  | succ k _ ih =>
      rw [newtonPolynomial_succ, map_mul, ih, zero_mul]

/-- A positive degree-`m` Newton weight has a strictly positive matrix entry
when `m` is at least the matrix dimension: factors above that dimension vanish
and the `k = 1` term remains strictly positive. -/
theorem aeval_weightNewtonPolynomial_entry_pos_of_dimension_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (hentry : ∀ i j, 0 ≤ A i j)
    (hsimple : StrictAnti (sortedEigenvalues A hA))
    {m : ℕ} (hm : N + 1 ≤ m) {δ s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s)
    (hspectrum : ∀ k, increasingEigenvalues A hA k = eigenvalue s k)
    (i j : Fin (N + 1)) (hij : 0 < A i j) :
    0 < (aeval A (weightNewtonPolynomial m δ s)) i j := by
  rw [weightNewtonPolynomial, map_sum, Matrix.sum_apply]
  apply Finset.sum_pos'
  · intro k hk
    simp only [Finset.mem_range] at hk
    rw [aeval_C_mul_apply]
    have hcoeff : 0 < newtonCoefficient m δ s k :=
      newtonCoefficient_pos (by lia) hδ hδ1 hs
    by_cases hlarge : N + 1 ≤ k
    · rw [aeval_newtonPolynomial_eq_zero_of_dimension_le A hA s hspectrum hlarge]
      simp
    · exact mul_nonneg hcoeff.le
        (aeval_newtonPolynomial_entry_nonneg A hA hentry hsimple s hspectrum
          ⟨k, by lia⟩ i j)
  · refine ⟨1, Finset.mem_range.mpr (by lia), ?_⟩
    rw [aeval_C_mul_apply]
    have hcoeff : 0 < newtonCoefficient m δ s 1 :=
      newtonCoefficient_one_pos (by lia) hδ hδ1 hs
    have hone : aeval A (newtonPolynomial s 1) = A := by
      simp [newtonPolynomial, eigenvalue]
    rw [hone]
    exact mul_pos hcoeff hij

end RealRooted.JacobiDeformation
