import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Triangularization of matrices over an algebraically closed field

Every square matrix over an algebraically closed field is conjugate to an upper
triangular matrix.  The statement is index-type agnostic: the triangular shape
is witnessed by an injective height function `b : m → ℕ`, so no linear order on
the index type is required.

The proof is the classical induction: the characteristic polynomial has a root,
a root of the characteristic polynomial has an eigenvector, conjugating by an
invertible matrix whose `i₀`-th column is that eigenvector clears the `i₀`-th
column below the diagonal, and the complement `{a // a ≠ i₀}` recurses.  All
block bookkeeping goes through `Equiv.sumCompl` and `Matrix.fromBlocks`.

## Main results

* `Matrix.exists_mulVec_eq_smul`: a matrix over an algebraically closed field
  has an eigenvector.
* `Matrix.exists_unitsConj_blockTriangular`: every matrix over an algebraically
  closed field is conjugate to a matrix that is block triangular for an
  injective height function into `ℕ`.
-/

open Finset

namespace Matrix

variable {K : Type*} [Field K]

/-- Every matrix over an algebraically closed field has an eigenvector. -/
theorem exists_mulVec_eq_smul [IsAlgClosed K] {m : Type*} [Fintype m]
    [Nonempty m] (A : Matrix m m K) :
    ∃ (μ : K) (v : m → K), v ≠ 0 ∧ A *ᵥ v = μ • v := by
  classical
  obtain ⟨μ, hμ⟩ : ∃ μ, A.charpoly.IsRoot μ := by
    apply IsAlgClosed.exists_root
    rw [Polynomial.degree_eq_natDegree A.charpoly_monic.ne_zero, A.charpoly_natDegree_eq_dim]
    exact_mod_cast Fintype.card_ne_zero
  have hdet : (algebraMap K (Matrix m m K) μ - A).det = 0 := by
    have hspec : μ ∈ spectrum K A := mem_spectrum_of_isRoot_charpoly hμ
    rw [spectrum.mem_iff, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hspec
    exact hspec
  obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff).2 hdet
  refine ⟨μ, v, hv0, ?_⟩
  rw [sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec] at hv
  exact (sub_eq_zero.mp hv).symm

/-- The induction behind `exists_unitsConj_blockTriangular`, phrased over the
cardinality of the index type. -/
private theorem exists_unitsConj_blockTriangular_aux [IsAlgClosed K] :
    ∀ (N : ℕ) {m : Type} [Fintype m] [DecidableEq m], Fintype.card m = N →
      ∀ A : Matrix m m K,
        ∃ (P : (Matrix m m K)ˣ) (b : m → ℕ), Function.Injective b ∧
          ((P⁻¹).val * A * P.val).BlockTriangular b := by
  intro N
  induction N with
  | zero =>
    intro m _ _ hcard A
    have : IsEmpty m := Fintype.card_eq_zero_iff.1 hcard
    exact ⟨1, fun _ => 0, fun a => isEmptyElim a, fun i => isEmptyElim i⟩
  | succ n ih =>
    intro m _ _ hcard A
    have : Nonempty m := Fintype.card_pos_iff.1 (by lia)
    -- an eigenvector, and a coordinate where it does not vanish
    obtain ⟨μ, v, hv0, hAv⟩ := exists_mulVec_eq_smul A
    obtain ⟨i₀, hvi₀⟩ := Function.ne_iff.1 hv0
    -- conjugate by an invertible matrix whose `i₀`-th column is the eigenvector
    set P₀ : Matrix m m K := (1 : Matrix m m K).updateCol i₀ v with hP₀def
    have hdet : P₀.det = v i₀ := by
      have h1 : cramer (1 : Matrix m m K) v i₀ = v i₀ := by rw [cramer_one]; rfl
      rw [cramer_apply] at h1
      exact h1
    have hPunit : IsUnit P₀ :=
      (isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact hvi₀.isUnit)
    obtain ⟨P₁, hP₁⟩ := hPunit
    set M : Matrix m m K := (P₁⁻¹).val * A * P₁.val with hMdef
    -- the `i₀`-th column of the conjugated matrix vanishes off the diagonal
    have h1 : P₁.val *ᵥ Pi.single i₀ 1 = v := by
      rw [hP₁, mulVec_single_one]
      ext i
      simp [hP₀def]
    have h2 : (P₁⁻¹).val *ᵥ v = Pi.single i₀ 1 := by
      rw [← h1, mulVec_mulVec, Units.inv_mul, one_mulVec]
    have hcol : M *ᵥ Pi.single i₀ 1 = μ • Pi.single i₀ 1 := by
      rw [hMdef, ← mulVec_mulVec, ← mulVec_mulVec, h1, hAv, mulVec_smul, h2]
    have hMcol : ∀ i : m, i ≠ i₀ → M i i₀ = 0 := by
      intro i hi
      have h := congrFun hcol i
      rw [mulVec_single_one] at h
      simpa [Pi.single_apply, hi] using h
    -- pass to `{a // a = i₀} ⊕ {a // ¬a = i₀}` coordinates
    set e : {a : m // a = i₀} ⊕ {a : m // ¬a = i₀} ≃ m :=
      Equiv.sumCompl (fun a => a = i₀) with hedef
    set Nm : Matrix ({a : m // a = i₀} ⊕ {a : m // ¬a = i₀})
        ({a : m // a = i₀} ⊕ {a : m // ¬a = i₀}) K := M.submatrix e e with hNdef
    have hN21 : Nm.toBlocks₂₁ = 0 := by
      ext i j
      have hj : (j : m) = i₀ := j.prop
      have hi : (i : m) ≠ i₀ := i.prop
      simp only [toBlocks₂₁, of_apply, hNdef, submatrix_apply, hedef,
        Equiv.sumCompl_apply_inr, Equiv.sumCompl_apply_inl, zero_apply]
      rw [hj]
      exact hMcol _ hi
    have hcardS : Fintype.card {a : m // ¬a = i₀} = n := by
      have h1 : Fintype.card {a : m // a = i₀} = 1 := Fintype.card_subtype_eq i₀
      have h2 := Fintype.card_subtype_compl (fun a : m => a = i₀)
      rw [h1, hcard] at h2
      rw [h2]
      lia
    obtain ⟨Q, b', hb'inj, hb'tri⟩ := ih hcardS Nm.toBlocks₂₂
    -- the block conjugator, extended by the identity on the distinguished index
    set Et : Matrix ({a : m // a = i₀} ⊕ {a : m // ¬a = i₀})
        ({a : m // a = i₀} ⊕ {a : m // ¬a = i₀}) K :=
      fromBlocks 1 0 0 Q.val with hEtdef
    set Et' : Matrix ({a : m // a = i₀} ⊕ {a : m // ¬a = i₀})
        ({a : m // a = i₀} ⊕ {a : m // ¬a = i₀}) K :=
      fromBlocks 1 0 0 (Q⁻¹).val with hEt'def
    have hEE' : Et * Et' = 1 := by
      rw [hEtdef, hEt'def, fromBlocks_multiply]
      simp [← fromBlocks_one]
    have hE'E : Et' * Et = 1 := by
      rw [hEtdef, hEt'def, fromBlocks_multiply]
      simp [← fromBlocks_one]
    set E₁ : (Matrix m m K)ˣ :=
      ⟨Et.submatrix e.symm e.symm, Et'.submatrix e.symm e.symm,
        by rw [submatrix_mul_equiv Et Et' _ e.symm _, hEE', submatrix_one_equiv],
        by rw [submatrix_mul_equiv Et' Et _ e.symm _, hE'E, submatrix_one_equiv]⟩ with hE₁def
    -- the conjugated matrix in block coordinates
    have hG : Et' * Nm * Et =
        fromBlocks Nm.toBlocks₁₁ (Nm.toBlocks₁₂ * Q.val) 0
          ((Q⁻¹).val * Nm.toBlocks₂₂ * Q.val) := by
      conv_lhs => rw [← fromBlocks_toBlocks Nm, hN21]
      rw [hEtdef, hEt'def, fromBlocks_multiply, fromBlocks_multiply]
      simp [Matrix.mul_assoc]
    set c : ({a : m // a = i₀} ⊕ {a : m // ¬a = i₀}) → ℕ :=
      Sum.elim (fun _ => 0) (fun s => b' s + 1) with hcdef
    have hGtri : (Et' * Nm * Et).BlockTriangular c := by
      rw [hG]
      rintro (i | i) (j | j) hij
      · exact absurd hij (lt_irrefl 0)
      · exact absurd hij (Nat.not_lt_zero _)
      · simp [fromBlocks]
      · have hb : b' j < b' i := by
          simpa [hcdef] using hij
        simpa [fromBlocks] using hb'tri hb
    have hcinj : Function.Injective c := by
      rintro (i | i) (j | j) hij
      · exact congrArg Sum.inl (Subsingleton.elim i j)
      · exact absurd hij.symm (by simp [hcdef])
      · exact absurd hij (by simp [hcdef])
      · exact congrArg Sum.inr (hb'inj (by simpa [hcdef] using hij))
    -- assemble
    refine ⟨P₁ * E₁, c ∘ e.symm, hcinj.comp e.symm.injective, ?_⟩
    have hMN : M = Nm.submatrix e.symm e.symm := by
      rw [hNdef, submatrix_submatrix]
      simp
    have hexp : ((P₁ * E₁)⁻¹).val * A * (P₁ * E₁).val
        = (Et' * Nm * Et).submatrix e.symm e.symm := by
      rw [show (P₁ * E₁)⁻¹ = E₁⁻¹ * P₁⁻¹ from _root_.mul_inv_rev _ _, Units.val_mul,
        Units.val_mul]
      have hinv : (E₁⁻¹).val = Et'.submatrix e.symm e.symm := rfl
      have hval : E₁.val = Et.submatrix e.symm e.symm := rfl
      calc (E₁⁻¹).val * (P₁⁻¹).val * A * (P₁.val * E₁.val)
          = (E₁⁻¹).val * ((P₁⁻¹).val * A * P₁.val) * E₁.val := by
            simp only [Matrix.mul_assoc]
        _ = (E₁⁻¹).val * M * E₁.val := by rw [hMdef]
        _ = Et'.submatrix e.symm e.symm * Nm.submatrix e.symm e.symm *
              Et.submatrix e.symm e.symm := by rw [hinv, hval, hMN]
        _ = (Et' * Nm * Et).submatrix e.symm e.symm := by
            rw [submatrix_mul_equiv Et' Nm _ e.symm _,
              submatrix_mul_equiv (Et' * Nm) Et _ e.symm _]
    rw [hexp]
    exact fun i j hij => hGtri hij

/-- **Triangularization.**  Every square matrix over an algebraically closed
field is conjugate to an upper triangular matrix; the triangular shape is
witnessed by an injective height function into `ℕ`, so no linear order on the
index type is needed. -/
theorem exists_unitsConj_blockTriangular [IsAlgClosed K] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m K) :
    ∃ (P : (Matrix m m K)ˣ) (b : m → ℕ), Function.Injective b ∧
      ((P⁻¹).val * A * P.val).BlockTriangular b :=
  exists_unitsConj_blockTriangular_aux (Fintype.card m) rfl A

end Matrix
