/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Positive semidefiniteness from a determinant condition

If `det (1 + x • M) ≠ 0` for all `x ∈ (-1, 1)`, the eigenvalues of the real symmetric matrix `M`
lie in `[-1, 1]`, so `(1 + M) / 2` and `(1 - M) / 2` are positive semidefinite.

## Main statements

* `Matrix.IsHermitian.posSemidef_one_add_smul`: `1 + s • M` is positive semidefinite when all
  `1 + s * λ` (`λ` an eigenvalue of `M`) are nonnegative.
* `Matrix.IsHermitian.posSemidef_of_det_one_add_smul_ne_zero`: the determinant criterion above.
-/

public section

open Matrix

namespace Matrix.IsHermitian

variable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}

/-- `1 + s • M` is positive semidefinite when all `1 + s λ` (`λ` an eigenvalue of `M`) are
nonnegative. -/
theorem posSemidef_one_add_smul (hM : M.IsHermitian) (s : ℝ)
    (hs : ∀ i, 0 ≤ 1 + s * hM.eigenvalues i) : (1 + s • M).PosSemidef := by
  set U : Matrix (Fin d) (Fin d) ℝ := (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hspec : M = U * diagonal hM.eigenvalues * star U := by
    conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp [U]
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hD : diagonal (fun i => 1 + s * hM.eigenvalues i) = 1 + s • diagonal hM.eigenvalues := by
    ext i j; by_cases hij : i = j <;> simp [hij, diagonal]
  have : 1 + s • M = U * diagonal (fun i => 1 + s * hM.eigenvalues i) * Uᴴ := by
    rw [hD, ← star_eq_conjTranspose, mul_add, add_mul, mul_one, hUU, Matrix.mul_smul,
      Matrix.smul_mul, ← hspec]
  rw [this]
  exact PosSemidef.mul_mul_conjTranspose_same (posSemidef_diagonal_iff.mpr hs) U

/-- If `det (1 + x M) ≠ 0` for all `x ∈ (-1, 1)`, the eigenvalues of the symmetric matrix `M`
lie in `[-1, 1]`, so `(1 ± M) / 2` are positive semidefinite. -/
theorem posSemidef_of_det_one_add_smul_ne_zero (hM : M.IsHermitian)
    (h : ∀ x : ℝ, -1 < x → x < 1 → (1 + x • M).det ≠ 0) :
    ((1 / 2 : ℝ) • (1 + M)).PosSemidef ∧ ((1 / 2 : ℝ) • (1 - M)).PosSemidef := by
  have hev : ∀ i, |hM.eigenvalues i| ≤ 1 := by
    intro i
    by_contra hlt
    push Not at hlt
    set μ := hM.eigenvalues i with hμdef
    have hμ : μ ≠ 0 := by intro h0; rw [h0] at hlt; norm_num at hlt
    have hinv : |-μ⁻¹| < 1 := by
      rw [abs_neg, abs_inv]; exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨h1, h2⟩ := abs_lt.mp hinv
    apply h (-μ⁻¹) h1 h2
    rw [← exists_mulVec_eq_zero_iff]
    refine ⟨⇑(hM.eigenvectorBasis i), ?_, ?_⟩
    · intro h0
      apply hM.eigenvectorBasis.orthonormal.ne_zero i
      ext j
      simpa using congrFun h0 j
    · rw [add_mulVec, one_mulVec, smul_mulVec, hM.mulVec_eigenvectorBasis, smul_smul,
        ← hμdef, neg_mul, inv_mul_cancel₀ hμ, neg_smul, one_smul, add_neg_cancel]
  have half : (0 : ℝ) ≤ 1 / 2 := by norm_num
  refine ⟨PosSemidef.smul ?_ half, PosSemidef.smul ?_ half⟩
  · simpa using hM.posSemidef_one_add_smul 1 (fun i => by
      have := (abs_le.mp (hev i)).1; linarith)
  · simpa [sub_eq_add_neg] using hM.posSemidef_one_add_smul (-1) (fun i => by
      have := (abs_le.mp (hev i)).2; linarith)

end Matrix.IsHermitian
