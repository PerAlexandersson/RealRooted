import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Matrix.Permanent
import RealRooted.Multiaffine
import RealRooted.MultivariateStability.Diagonal

/-!
# Permanent polynomials and monotone matrix conventions

We define the multivariate and diagonal permanent polynomials used in the
monotone column permanent conjecture. The decreasing-column convention is
that of P. Brändén, J. Haglund, M. Visontai, and D. G. Wagner,
*Proof of the monotone column permanent conjecture*,
doi:10.1007/978-3-0348-0142-3_5, arXiv:1010.2565.
-/

open scoped BigOperators

namespace Matrix

/-- Every column is weakly decreasing as the row index increases. -/
def HasWeaklyDecreasingColumns {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ j i k, i ≤ k → A k j ≤ A i j

/-- Every column is weakly increasing as the row index increases. -/
def HasWeaklyIncreasingColumns {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ j i k, i ≤ k → A i j ≤ A k j

/-- Reverse the row order of a square matrix. -/
def reverseRows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i.rev j

/-- Reversing the rows twice recovers the original matrix. -/
@[simp] theorem reverseRows_reverseRows {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    reverseRows (reverseRows A) = A := by
  funext i j
  simp [reverseRows]

/-- Row reversal exchanges the increasing and decreasing conventions. -/
theorem hasWeaklyIncreasingColumns_reverseRows_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HasWeaklyIncreasingColumns (reverseRows A) ↔
      HasWeaklyDecreasingColumns A := by
  constructor
  · intro h j i k hik
    have hrev : k.rev ≤ i.rev := Fin.rev_le_rev.mpr hik
    simpa [reverseRows] using h j k.rev i.rev hrev
  · intro h j i k hik
    have hrev : k.rev ≤ i.rev := Fin.rev_le_rev.mpr hik
    simpa [reverseRows] using h j k.rev i.rev hrev

/-- A matrix has increasing columns exactly when its row reversal has
decreasing columns. -/
theorem hasWeaklyDecreasingColumns_reverseRows_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HasWeaklyDecreasingColumns (reverseRows A) ↔
      HasWeaklyIncreasingColumns A := by
  rw [← hasWeaklyIncreasingColumns_reverseRows_iff,
    reverseRows_reverseRows]

/-- Adding a constant to each whole column preserves and reflects the
decreasing-column condition. -/
theorem hasWeaklyDecreasingColumns_add_columnConstants_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    HasWeaklyDecreasingColumns (fun i j => A i j + c j) ↔
      HasWeaklyDecreasingColumns A := by
  constructor
  · intro h j i k hik
    exact (add_le_add_iff_right (c j)).mp (h j i k hik)
  · intro h j i k hik
    exact (add_le_add_iff_right (c j)).mpr (h j i k hik)

end Matrix

namespace RealRooted
namespace Permanent

noncomputable section

/-- The multivariate permanent `per(z_j + a_ij)`, with one variable for each
column. -/
def columnPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  Matrix.permanent fun i j => MvPolynomial.X j + MvPolynomial.C (A i j)

/-- The univariate permanent `per(z J + A)`. -/
def diagonalPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Polynomial ℝ :=
  Matrix.permanent fun i j => Polynomial.X + Polynomial.C (A i j)

/-- Renaming polynomial variables commutes with the permanent. -/
theorem rename_permanent {ι σ τ : Type*} [DecidableEq ι] [Fintype ι]
    (f : σ → τ) (M : Matrix ι ι (MvPolynomial σ ℝ)) :
    MvPolynomial.rename f M.permanent =
      Matrix.permanent (fun i j => MvPolynomial.rename f (M i j)) := by
  classical
  unfold Matrix.permanent
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  rw [map_prod]

/-- The multivariate column permanent is affine in every variable. -/
theorem columnPermanent_isMultiaffine {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (columnPermanent A).IsMultiaffine := by
  classical
  unfold columnPermanent Matrix.permanent
  apply MvPolynomial.IsMultiaffine.sum
  intro σ hσ j
  refine (MvPolynomial.degreeOf_prod_le j Finset.univ
    (fun i => MvPolynomial.X i + MvPolynomial.C (A (σ i) i))).trans ?_
  calc
    ∑ i, (MvPolynomial.X i + MvPolynomial.C (A (σ i) i) :
        MvPolynomial (Fin n) ℝ).degreeOf j ≤
        ∑ i, if i = j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      refine (MvPolynomial.degreeOf_add_le j _ _).trans ?_
      by_cases hij : i = j
      · subst i
        simp
      · simp [MvPolynomial.degreeOf_X, hij, Ne.symm hij]
    _ = 1 := by simp

/-- Diagonal restriction commutes with a product over a finite set. -/
theorem diagonal_finsetProd {ι σ : Type*}
    (s : Finset ι) (P : ι → MvPolynomial σ ℝ) :
    MvPolynomial.diagonal (∏ i ∈ s, P i) =
      ∏ i ∈ s, MvPolynomial.diagonal (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- Identifying all column variables gives `per(z J + A)`. -/
@[simp] theorem diagonal_columnPermanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial.diagonal (columnPermanent A) = diagonalPermanent A := by
  classical
  unfold columnPermanent diagonalPermanent Matrix.permanent
  rw [MvPolynomial.diagonal_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [diagonal_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  simp

/-- Stability of the multivariate permanent implies splitting of its
diagonal specialization. -/
theorem diagonalPermanent_splits_of_columnPermanent_stable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : MvRealStable (columnPermanent A)) :
    (diagonalPermanent A).Splits := by
  rw [← diagonal_columnPermanent]
  exact hA.diagonal_splits

/-- The coefficient of degree `n` in `per(X J + A)` is `n!`. -/
theorem diagonalPermanent_coeff_card {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (diagonalPermanent A).coeff n = n.factorial := by
  classical
  unfold diagonalPermanent Matrix.permanent
  rw [Polynomial.finsetSum_coeff]
  calc
    ∑ σ : Equiv.Perm (Fin n),
        (∏ i, (Polynomial.X + Polynomial.C (A (σ i) i))).coeff n =
        ∑ _σ : Equiv.Perm (Fin n), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      let P : Polynomial ℝ :=
        ∏ i, (Polynomial.X + Polynomial.C (A (σ i) i))
      have hmonic : P.Monic :=
        Polynomial.monic_prod_of_monic Finset.univ _ fun i hi =>
          Polynomial.monic_X_add_C _
      have hdegree : P.natDegree = n := by
        rw [Polynomial.natDegree_prod_of_monic]
        · simp
        · exact fun i hi => Polynomial.monic_X_add_C _
      change P.coeff n = 1
      calc
        P.coeff n = P.coeff P.natDegree := by rw [hdegree]
        _ = 1 := hmonic.coeff_natDegree
    _ = n.factorial := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
      simp

/-- The univariate permanent polynomial `per(X J + A)` is nonzero. -/
theorem diagonalPermanent_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    diagonalPermanent A ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun P : Polynomial ℝ => P.coeff n) hzero
  rw [diagonalPermanent_coeff_card] at hcoeff
  have hpositive : (0 : ℝ) < n.factorial := by positivity
  exact hpositive.ne' hcoeff

/-- The multivariate permanent polynomial `per(z_j + a_ij)` is nonzero. -/
theorem columnPermanent_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    columnPermanent A ≠ 0 := by
  intro hzero
  apply diagonalPermanent_ne_zero A
  rw [← diagonal_columnPermanent, hzero, MvPolynomial.diagonal_zero]

/-- Reversing all rows leaves the multivariate permanent unchanged. -/
@[simp] theorem columnPermanent_reverseRows {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    columnPermanent (Matrix.reverseRows A) = columnPermanent A := by
  unfold columnPermanent
  have hmatrix :
      (fun i j =>
          MvPolynomial.X j + MvPolynomial.C ((Matrix.reverseRows A) i j)) =
        Matrix.submatrix
          ((fun i j => MvPolynomial.X j + MvPolynomial.C (A i j)) :
            Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℝ))
          Fin.revPerm id := by
    funext i j
    rfl
  rw [hmatrix]
  exact Matrix.permanent_permute_cols Fin.revPerm _

/-- Reversing all rows leaves the univariate permanent unchanged. -/
@[simp] theorem diagonalPermanent_reverseRows {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    diagonalPermanent (Matrix.reverseRows A) = diagonalPermanent A := by
  unfold diagonalPermanent
  have hmatrix :
      (fun i j =>
          Polynomial.X + Polynomial.C ((Matrix.reverseRows A) i j)) =
        Matrix.submatrix
          ((fun i j => Polynomial.X + Polynomial.C (A i j)) :
            Matrix (Fin n) (Fin n) (Polynomial ℝ)) Fin.revPerm id := by
    funext i j
    rfl
  rw [hmatrix]
  exact Matrix.permanent_permute_cols Fin.revPerm _

/-- Renaming variables transports a column-permuted matrix back to the
original permanent. -/
theorem rename_columnPermanent_submatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (τ : Equiv.Perm (Fin n)) :
    MvPolynomial.rename τ (columnPermanent (A.submatrix id τ)) =
      columnPermanent A := by
  classical
  unfold columnPermanent
  simp only [Matrix.submatrix_apply, id_eq]
  rw [rename_permanent τ
    (fun i j : Fin n =>
      MvPolynomial.X j + MvPolynomial.C (A i (τ j)))]
  have hmatrix :
      (fun i j =>
        MvPolynomial.rename τ
          (MvPolynomial.X j + MvPolynomial.C (A i (τ j)))) =
        Matrix.submatrix
          (fun i j => MvPolynomial.X j + MvPolynomial.C (A i j)) id τ := by
    funext i j
    change MvPolynomial.rename τ
        (MvPolynomial.X j + MvPolynomial.C (A i (τ j))) =
      MvPolynomial.X (τ j) + MvPolynomial.C (A i (τ j))
    simp
  rw [hmatrix]
  exact Matrix.permanent_permute_rows τ _

end

end Permanent
end RealRooted
