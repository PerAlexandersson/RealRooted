import RealRooted.JacobiDeformation.KernelSign

/-!
# Newton kernel signs above matrix dimension

The Newton weight degree may exceed the number of spectral nodes.  The extra
Newton factors vanish after matrix evaluation, so the strict entrywise sign
argument remains valid.
-/

open Finset Matrix Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

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

private theorem aeval_C_mul_apply_restriction {n : Type*}
    [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (c : ℝ) (p : ℝ[X]) (i j : n) :
    (aeval A (C c * p)) i j = c * (aeval A p) i j := by
  rw [map_mul, aeval_C]
  simp [Matrix.mul_apply, Matrix.algebraMap_matrix_apply]

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
    rw [aeval_C_mul_apply_restriction]
    have hcoeff : 0 < newtonCoefficient m δ s k :=
      newtonCoefficient_pos (by lia) hδ hδ1 hs
    by_cases hlarge : N + 1 ≤ k
    · rw [aeval_newtonPolynomial_eq_zero_of_dimension_le A hA s hspectrum hlarge]
      simp
    · exact mul_nonneg hcoeff.le
        (aeval_newtonPolynomial_entry_nonneg A hA hentry hsimple s hspectrum
          ⟨k, by lia⟩ i j)
  · refine ⟨1, Finset.mem_range.mpr (by lia), ?_⟩
    rw [aeval_C_mul_apply_restriction]
    have hcoeff : 0 < newtonCoefficient m δ s 1 :=
      newtonCoefficient_one_pos (by lia) hδ hδ1 hs
    have hone : aeval A (newtonPolynomial s 1) = A := by
      simp [newtonPolynomial, eigenvalue]
    rw [hone]
    exact mul_pos hcoeff hij

end RealRooted.JacobiDeformation
