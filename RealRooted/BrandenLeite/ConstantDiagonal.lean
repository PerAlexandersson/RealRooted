import RealRooted.BrandenLeite.Theorem37
import RealRooted.PFPolynomial

/-!
# Chain polynomials of positive constant-diagonal matrices

This file normalizes a lower-triangular matrix with positive constant
diagonal to a lower unitriangular matrix.  The associated chain polynomials
are related by a positive rescaling of the polynomial variable, so the
Brändén--Saud Leite Theorem 3.7 transfers to the unnormalized matrix.
-/

open Matrix Polynomial BigOperators

noncomputable section

namespace RealRooted.BrandenLeite

/-- Divide every matrix entry by a fixed scalar. -/
def normalizeConstantDiagonal (δ : ℝ) (A : LowerTriangularMatrix ℝ) :
    LowerTriangularMatrix ℝ :=
  fun i j => δ⁻¹ * A i j

/-- Scalar normalization preserves lower triangularity. -/
theorem normalizeConstantDiagonal_lower
    {δ : ℝ} {A : LowerTriangularMatrix ℝ}
    (hA : LowerTriangularMatrix.IsLowerTriangular A) :
    LowerTriangularMatrix.IsLowerTriangular
      (normalizeConstantDiagonal δ A) := by
  intro i j hij
  simp [normalizeConstantDiagonal, hA hij]

/-- Dividing a nonzero constant diagonal by itself gives a lower
unitriangular matrix. -/
theorem normalizeConstantDiagonal_unit
    {δ : ℝ} {A : LowerTriangularMatrix ℝ} (hδ : δ ≠ 0)
    (hA : LowerTriangularMatrix.IsLowerTriangular A)
    (hdiag : ∀ n, A n n = δ) :
    LowerTriangularMatrix.IsLowerUnitriangular
      (normalizeConstantDiagonal δ A) := by
  refine ⟨normalizeConstantDiagonal_lower hA, ?_⟩
  intro n
  simp [normalizeConstantDiagonal, hdiag n, hδ]

/-- Dividing by a positive scalar preserves total nonnegativity. -/
theorem normalizeConstantDiagonal_isTotallyNonneg
    {δ : ℝ} {A : LowerTriangularMatrix ℝ} (hδ : 0 < δ)
    (hA : Matrix.IsTotallyNonneg A) :
    Matrix.IsTotallyNonneg (normalizeConstantDiagonal δ A) := by
  change Matrix.IsTotallyNonneg (δ⁻¹ • A)
  exact hA.smul δ⁻¹ (inv_nonneg.mpr hδ.le)

/-- Chain polynomials before and after scalar matrix normalization differ by
the variable substitution X ↦ δ X. -/
theorem chainPolynomial_comp_C_mul_X_normalizeConstantDiagonal
    {δ : ℝ} {A : LowerTriangularMatrix ℝ} (hδ : δ ≠ 0) (n : ℕ) :
    chainPolynomial A n =
      (chainPolynomial (normalizeConstantDiagonal δ A) n).comp
        (C δ * X) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [chainPolynomial_succ, chainPolynomial_succ, mul_comp, X_comp]
          have hcomp :
              ((∑ k : Fin (n + 1),
                  C (normalizeConstantDiagonal δ A (n + 1) k) *
                    chainPolynomial (normalizeConstantDiagonal δ A) k).comp
                    (C δ * X)) =
                ∑ k : Fin (n + 1),
                  (C (normalizeConstantDiagonal δ A (n + 1) k) *
                    chainPolynomial (normalizeConstantDiagonal δ A) k).comp
                    (C δ * X) := by
            change Polynomial.compRingHom (C δ * X) (∑ k : Fin (n + 1),
                C (normalizeConstantDiagonal δ A (n + 1) k) *
                  chainPolynomial (normalizeConstantDiagonal δ A) k) = _
            exact map_sum (Polynomial.compRingHom (C δ * X)) _ _
          rw [hcomp]
          simp_rw [mul_comp, C_comp, ih _ (Fin.isLt _)]
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          simp only [normalizeConstantDiagonal]
          rw [map_mul]
          have hcancel : C δ * C δ⁻¹ = (1 : ℝ[X]) := by
            rw [← C_mul]
            simp [hδ]
          calc
            X * (C (A (n + 1) k) *
                (chainPolynomial (normalizeConstantDiagonal δ A) k).comp
                  (C δ * X)) =
                (C δ * C δ⁻¹) *
                  (X * (C (A (n + 1) k) *
                    (chainPolynomial (normalizeConstantDiagonal δ A) k).comp
                      (C δ * X))) := by rw [hcancel, one_mul]
            _ = C δ * X *
                (C δ⁻¹ * C (A (n + 1) k) *
                  (chainPolynomial (normalizeConstantDiagonal δ A) k).comp
                    (C δ * X)) := by ring

/-- The chain polynomials of a totally nonnegative lower-triangular matrix
with positive constant diagonal are Pólya-frequency polynomials. -/
theorem chainPolynomial_isPFPolynomial_of_pos_constantDiagonal
    {δ : ℝ} {A : LowerTriangularMatrix ℝ} (hδ : 0 < δ)
    (hlower : LowerTriangularMatrix.IsLowerTriangular A)
    (hdiag : ∀ n, A n n = δ) (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    IsPFPolynomial (chainPolynomial A n) := by
  let B := normalizeConstantDiagonal δ A
  have hunit : LowerTriangularMatrix.IsLowerUnitriangular B :=
    normalizeConstantDiagonal_unit hδ.ne' hlower hdiag
  have hB : Matrix.IsTotallyNonneg B :=
    normalizeConstantDiagonal_isTotallyNonneg hδ hA
  have hBpf : IsPFPolynomial (chainPolynomial B n) := by
    rcases chainPolynomial_eq_zero_or_splits_of_isTotallyNonneg
        hunit hB n with hzero | hsplits
    · simpa [hzero] using IsPFPolynomial.zero
    · exact IsPFPolynomial.of_realRooted_nonneg
        (chainPolynomial_hasNonnegCoeffs_of_isTotallyNonneg hunit hB n)
        hsplits
  rw [chainPolynomial_comp_C_mul_X_normalizeConstantDiagonal hδ.ne' n]
  simpa [B] using IsPFPolynomial.comp_C_mul_X_add_C
    (p := chainPolynomial B n) (a := δ) (d := 0) hδ (le_refl 0) hBpf

/-- Consecutive chain polynomials of a totally nonnegative lower-triangular
matrix with positive constant diagonal are in zero-aware proper position. -/
theorem prec0_chainPolynomial_succ_of_pos_constantDiagonal
    {δ : ℝ} {A : LowerTriangularMatrix ℝ} (hδ : 0 < δ)
    (hlower : LowerTriangularMatrix.IsLowerTriangular A)
    (hdiag : ∀ n, A n n = δ) (hA : Matrix.IsTotallyNonneg A) (n : ℕ) :
    Interl (chainPolynomial A n) (chainPolynomial A (n + 1)) := by
  let B := normalizeConstantDiagonal δ A
  have hunit : LowerTriangularMatrix.IsLowerUnitriangular B :=
    normalizeConstantDiagonal_unit hδ.ne' hlower hdiag
  have hB : Matrix.IsTotallyNonneg B :=
    normalizeConstantDiagonal_isTotallyNonneg hδ hA
  have hprec : Interl (chainPolynomial B n)
      (chainPolynomial B (n + 1)) :=
    prec0_chainPolynomial_succ_of_isTotallyNonneg hunit hB n
  rw [chainPolynomial_comp_C_mul_X_normalizeConstantDiagonal hδ.ne' n,
    chainPolynomial_comp_C_mul_X_normalizeConstantDiagonal hδ.ne' (n + 1)]
  rcases hprec with hzero | hzero | hprec
  · left
    have hzero' :
        chainPolynomial (normalizeConstantDiagonal δ A) n = 0 := by
      simpa [B] using hzero
    rw [hzero', zero_comp]
  · right
    left
    have hzero' :
        chainPolynomial (normalizeConstantDiagonal δ A) (n + 1) = 0 := by
      simpa [B] using hzero
    rw [hzero', zero_comp]
  · right
    right
    exact hprec.comp_C_mul_X hδ

end RealRooted.BrandenLeite
