import RealRooted.PolyaFrequency.EventuallyPolynomial
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer.Closure
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.FinTruncation

/-!
# Causal forward differences with a positive initial value

This opt-in leaf applies the nonsingular finite Cryer closure to finite
Toeplitz truncations. The zero-prefix case remains separate.
-/

open Filter Polynomial Topology

namespace RealRooted

/-- A Pólya-frequency sequence with a nonzero eventual polynomial tail and
a positive initial value has a Pólya-frequency causal forward difference. -/
theorem IsPolyaFreqSeq.causalFwdDiff_of_eventually_polynomial_of_pos_zero
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) {p : ℝ[X]} (hp : p ≠ 0)
    (hap : ∀ᶠ k in atTop, a k = p.eval (k : ℝ)) (ha0 : 0 < a 0) :
    IsPolyaFreqSeq (Function.causalFwdDiff a) := by
  apply Matrix.IsTotallyNonneg.of_fin_truncations (toeplitz (Function.causalFwdDiff a))
    (fun N => (toeplitz (Function.causalFwdDiff a)).submatrix Fin.val Fin.val)
  · intro N i j
    rfl
  · intro N
    let B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
      (toeplitz (Function.causalFwdDiff a)).submatrix Fin.val Fin.val
    change B.IsTotallyNonneg
    apply Matrix.HasNonnegInitialColumnMinors.isTotallyNonneg_of_upper_zero_of_det_ne_zero B
    · intro m hm rows hrows
      have h := ha.causalFwdDiff_initialMinor_nonneg hp hap
        (rows := fun i => (rows i : ℕ)) (by
          intro i j hij
          exact Fin.lt_def.mpr (hrows hij))
      change 0 ≤ (B.submatrix rows (Fin.castLE hm)).det
      convert h using 1
      rfl
    · intro i j hij
      simp [B, toeplitz_apply, Nat.not_le_of_gt (Fin.lt_def.mp hij)]
    · have hlower : B.BlockTriangular OrderDual.toDual := by
        intro i j hij
        simp only [B, Matrix.submatrix_apply, toeplitz_apply]
        exact if_neg (Nat.not_le_of_gt (Fin.lt_def.mp hij))
      rw [Matrix.det_of_lowerTriangular B hlower]
      rw [Finset.prod_ne_zero_iff]
      intro i _
      simp [B, toeplitz_apply, Function.causalFwdDiff, ne_of_gt ha0]

end RealRooted
