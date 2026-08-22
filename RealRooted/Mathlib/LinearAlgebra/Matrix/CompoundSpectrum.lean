import RealRooted.Mathlib.LinearAlgebra.Matrix.Compound
import RealRooted.Mathlib.LinearAlgebra.Matrix.Triangularize
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The spectrum of a compound matrix

Over an algebraically closed field, the eigenvalues of the `q`-th compound
matrix `compound q A` are exactly the `q`-fold products of the eigenvalues of
`A` over increasing selections, with multiplicity.

The proof assembles the two halves proved elsewhere: `A` is conjugate to an
upper triangular matrix (`exists_unitsConj_blockTriangular`), the height
function of that triangular form is sorted into the index order by a
permutation conjugation, the characteristic polynomial of the compound of a
triangular matrix reads off the diagonal products
(`charpoly_compound_of_blockTriangular`), and compound characteristic
polynomials are invariant under conjugation (`charpoly_compound_conj`).

This is the spectral input for Gantmacher-Krein: a totally nonnegative matrix
has entrywise nonnegative compounds, so Perron-Frobenius applied to each
compound controls the products of eigenvalues.
-/

open Polynomial

namespace Matrix

variable {K : Type} [Field K]

/-- **Eigenvalues of compound matrices.**  Over an algebraically closed field
there is an enumeration `μ` of the eigenvalues of `A` (with multiplicity, as
the roots of the characteristic polynomial) such that for every `q` the
characteristic polynomial of `compound q A` has roots exactly the `q`-fold
products of the `μ i` over increasing selections. -/
theorem exists_charpoly_compound_eq_prod [IsAlgClosed K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    ∃ μ : Fin n → K,
      A.charpoly = ∏ i, (X - C (μ i)) ∧
      ∀ q, (compound q A).charpoly =
        ∏ s : Set.powersetCard (Fin n) q,
          (X - C (∏ k, μ (powersetEnum s k))) := by
  obtain ⟨P, b, hbinj, hbtri⟩ := exists_unitsConj_blockTriangular A
  set T : Matrix (Fin n) (Fin n) K := (P⁻¹).val * A * P.val with hTdef
  -- sort the height function into the index order
  set σ : Equiv.Perm (Fin n) := Tuple.sort b with hσdef
  have hmono : StrictMono (b ∘ σ) :=
    (Tuple.monotone_sort b).strictMono_of_injective (hbinj.comp σ.injective)
  set T' : Matrix (Fin n) (Fin n) K := T.submatrix σ σ with hT'def
  have hT'tri : T'.BlockTriangular id := fun i j hij => hbtri (hmono hij)
  -- the sorted triangular form is a conjugate of `T` by a permutation matrix
  set U : (Matrix (Fin n) (Fin n) K)ˣ := Matrix.permMatrixHom.toHomUnits σ⁻¹ with hUdef
  have hUval : U.val = σ.permMatrix K := by
    rw [hUdef]
    show Matrix.permMatrixHom σ⁻¹ = σ.permMatrix K
    rw [permMatrixHom_apply, inv_inv]
  have hUinv : (U⁻¹).val = σ⁻¹.permMatrix K := by
    rw [hUdef, ← map_inv, inv_inv]
    show Matrix.permMatrixHom σ = σ⁻¹.permMatrix K
    rw [permMatrixHom_apply]
  have hT'conj : T' = U.val * T * (U⁻¹).val := by
    rw [hUval, hUinv, hT'def, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix]
    simp [Equiv.Perm.inv_def]
  -- characteristic polynomials of all compounds transport along both conjugations
  have hchar : ∀ q, (compound q T').charpoly = (compound q A).charpoly := by
    intro q
    have h1 : (compound q T').charpoly = (compound q T).charpoly := by
      rw [hT'conj]
      exact charpoly_compound_conj U T
    have h2 : (compound q T).charpoly = (compound q A).charpoly := by
      have h3 := charpoly_compound_conj (q := q) P⁻¹ A
      rw [inv_inv] at h3
      rw [hTdef]
      exact h3
    rw [h1, h2]
  refine ⟨fun i => T' i i, ?_, ?_⟩
  · have hA_T : T.charpoly = A.charpoly := by
      rw [hTdef, Matrix.coe_units_inv]
      exact charpoly_units_conj' P A
    have hT'_T : T'.charpoly = T.charpoly := by
      rw [hT'conj, Matrix.coe_units_inv]
      exact charpoly_units_conj U T
    rw [← hA_T, ← hT'_T]
    exact charpoly_of_upperTriangular T' hT'tri
  · intro q
    rw [← hchar q, charpoly_compound_of_blockTriangular hT'tri q]

end Matrix
