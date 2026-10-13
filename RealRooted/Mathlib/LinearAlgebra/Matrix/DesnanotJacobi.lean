import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# The Desnanot--Jacobi determinant identity

This file proves Dodgson's condensation identity for a square matrix over an arbitrary
commutative ring.  Mathlib has the required block-determinant and generic-matrix tools, but no
statement of this identity.  Tau Ceti's `LinearAlgebra.Matrix.Condensation` contains Chiò's
different, one-corner condensation identity, so it does not directly supply this result.
-/

namespace Matrix

noncomputable section

private def extendInterior {n : ℕ} (p : Fin 2) : Fin n ⊕ Unit → Fin n ⊕ Fin 2 :=
  Sum.elim Sum.inl fun _ => Sum.inr p

private lemma desnanotJacobi_blocks_of_invertible {K : Type*} [Field K] {n : ℕ}
    (P : Matrix (Fin n ⊕ Fin 2) (Fin n ⊕ Fin 2) K)
    [Invertible (P.submatrix Sum.inl Sum.inl)] :
    P.det * (P.submatrix Sum.inl Sum.inl).det =
      (P.submatrix (extendInterior 0) (extendInterior 0)).det *
          (P.submatrix (extendInterior 1) (extendInterior 1)).det -
        (P.submatrix (extendInterior 0) (extendInterior 1)).det *
          (P.submatrix (extendInterior 1) (extendInterior 0)).det := by
  set A := P.submatrix Sum.inl Sum.inl
  have hblocks : ∀ p r : Fin 2, P.submatrix (extendInterior p) (extendInterior r) =
      fromBlocks A (Matrix.of fun i (_ : Unit) => P (Sum.inl i) (Sum.inr r))
        (Matrix.of fun (_ : Unit) j => P (Sum.inr p) (Sum.inl j))
        (Matrix.of fun _ _ => P (Sum.inr p) (Sum.inr r)) := by
    intro p r
    ext (i | i) (j | j) <;> simp [extendInterior, A, fromBlocks]
  have hP : P = fromBlocks A P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂ :=
    (fromBlocks_toBlocks P).symm
  have hminor : ∀ p r : Fin 2, (P.submatrix (extendInterior p) (extendInterior r)).det =
      A.det * (P.toBlocks₂₂ - P.toBlocks₂₁ * ⅟A * P.toBlocks₁₂) p r := by
    intro p r
    rw [hblocks, det_fromBlocks₁₁, det_unique (n := Unit)]
    congr 1
  rw [hminor, hminor, hminor, hminor]
  conv_lhs => rw [hP, det_fromBlocks₁₁, det_fin_two]
  ring

private lemma desnanotJacobi_blocks {K : Type*} [Field K] {n : ℕ}
    (P : Matrix (Fin n ⊕ Fin 2) (Fin n ⊕ Fin 2) K)
    (hA : (P.submatrix Sum.inl Sum.inl).det ≠ 0) :
    P.det * (P.submatrix Sum.inl Sum.inl).det =
      (P.submatrix (extendInterior 0) (extendInterior 0)).det *
          (P.submatrix (extendInterior 1) (extendInterior 1)).det -
        (P.submatrix (extendInterior 0) (extendInterior 1)).det *
          (P.submatrix (extendInterior 1) (extendInterior 0)).det :=
  @desnanotJacobi_blocks_of_invertible K _ n P
    (Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.2 hA))

private def interiorEquiv (n : ℕ) : Fin n ⊕ Fin 2 → Fin (n + 2) :=
  Sum.elim (fun i => i.castSucc.succ) fun p => if p = 0 then 0 else Fin.last _

private lemma interiorEquiv_bijective (n : ℕ) : Function.Bijective (interiorEquiv n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  rintro (i | i) (j | j) h <;>
    simp only [interiorEquiv, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, Fin.val_succ,
      Fin.val_castSucc] at h ⊢
  · simp only [Sum.inl.injEq, Fin.ext_iff]
    lia
  · exfalso
    have hi := i.isLt
    split at h <;> simp only [Fin.val_zero, Fin.val_last] at h <;> lia
  · exfalso
    have hj := j.isLt
    split at h <;> simp only [Fin.val_zero, Fin.val_last] at h <;> lia
  · fin_cases i <;> fin_cases j <;> simp_all

private def appendEquiv (n : ℕ) : Fin n ⊕ Unit → Fin (n + 1) :=
  Sum.elim Fin.castSucc fun _ => Fin.last n

private def prependEquiv (n : ℕ) : Fin n ⊕ Unit → Fin (n + 1) :=
  Sum.elim Fin.succ fun _ => 0

private lemma appendEquiv_bijective (n : ℕ) : Function.Bijective (appendEquiv n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  rintro (i | i) (j | j) h <;>
    simp only [appendEquiv, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, Fin.val_last,
      Fin.val_castSucc] at h ⊢
  · simp only [Sum.inl.injEq, Fin.ext_iff]
    lia
  · lia
  · lia

private lemma prependEquiv_bijective (n : ℕ) : Function.Bijective (prependEquiv n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  rintro (i | i) (j | j) h <;>
    simp only [prependEquiv, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, Fin.val_succ,
      Fin.val_zero] at h ⊢
  · simp only [Sum.inl.injEq, Fin.ext_iff]
    lia
  · lia
  · lia

private lemma det_submatrix_mul_swap {R : Type*} [CommRing R] {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X Y : Matrix κ κ R) (σ τ : ι ≃ κ) :
    (X.submatrix σ τ).det * (Y.submatrix τ σ).det = X.det * Y.det := by
  set π : Equiv.Perm κ := τ.symm.trans σ
  have hX : X.submatrix σ τ = (X.submatrix π id).submatrix τ τ := by
    ext i j
    simp [π]
  have hY : Y.submatrix τ σ = (Y.submatrix id π).submatrix τ τ := by
    ext i j
    simp [π]
  rw [hX, hY, det_submatrix_equiv_self, det_submatrix_equiv_self, det_permute,
    det_permute']
  have hsign : ((Equiv.Perm.sign π : ℤ) : R) * (Equiv.Perm.sign π : ℤ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  linear_combination (X.det * Y.det) * hsign

private def interior (n : ℕ) : Fin n → Fin (n + 2) := fun i => i.castSucc.succ

private lemma desnanotJacobi_field {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) K)
    (hA : (M.submatrix (interior n) (interior n)).det ≠ 0) :
    M.det * (M.submatrix (interior n) (interior n)).det =
      (M.submatrix Fin.succ Fin.succ).det *
          (M.submatrix Fin.castSucc Fin.castSucc).det -
        (M.submatrix Fin.succ Fin.castSucc).det *
          (M.submatrix Fin.castSucc Fin.succ).det := by
  set e := Equiv.ofBijective _ (interiorEquiv_bijective n)
  set σ := Equiv.ofBijective _ (appendEquiv_bijective n)
  set τ := Equiv.ofBijective _ (prependEquiv_bijective n)
  have h := desnanotJacobi_blocks (M.submatrix e e) hA
  have he0 : ∀ x, e (extendInterior 0 x) = Fin.castSucc (τ x) := by
    rintro (i | i) <;> simp [e, τ, extendInterior, interiorEquiv, prependEquiv]
  have he1 : ∀ x, e (extendInterior 1 x) = Fin.succ (σ x) := by
    rintro (i | i) <;> simp [e, σ, extendInterior, interiorEquiv, appendEquiv]
  have h00 : (M.submatrix e e).submatrix (extendInterior 0) (extendInterior 0) =
      (M.submatrix Fin.castSucc Fin.castSucc).submatrix τ τ := by
    ext i j
    simp [he0]
  have h11 : (M.submatrix e e).submatrix (extendInterior 1) (extendInterior 1) =
      (M.submatrix Fin.succ Fin.succ).submatrix σ σ := by
    ext i j
    simp [he1]
  have h01 : (M.submatrix e e).submatrix (extendInterior 0) (extendInterior 1) =
      (M.submatrix Fin.castSucc Fin.succ).submatrix τ σ := by
    ext i j
    simp [he0, he1]
  have h10 : (M.submatrix e e).submatrix (extendInterior 1) (extendInterior 0) =
      (M.submatrix Fin.succ Fin.castSucc).submatrix σ τ := by
    ext i j
    simp [he0, he1]
  rw [h00, h11, h01, h10, det_submatrix_equiv_self, det_submatrix_equiv_self,
    det_submatrix_equiv_self, mul_comm ((Matrix.submatrix _ τ σ).det),
    det_submatrix_mul_swap] at h
  have hcore : (M.submatrix e e).submatrix Sum.inl Sum.inl =
      M.submatrix (interior n) (interior n) := by
    ext i j
    simp [e, interiorEquiv, interior]
  rw [hcore] at h
  linear_combination h

private def desnanotJacobiDefect {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) : R :=
  M.det * (M.submatrix (interior n) (interior n)).det -
    ((M.submatrix Fin.succ Fin.succ).det *
        (M.submatrix Fin.castSucc Fin.castSucc).det -
      (M.submatrix Fin.succ Fin.castSucc).det *
        (M.submatrix Fin.castSucc Fin.succ).det)

private lemma desnanotJacobiDefect_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    f (desnanotJacobiDefect M) = desnanotJacobiDefect (f.mapMatrix M) := by
  simp only [desnanotJacobiDefect, map_sub, map_mul, RingHom.map_det]
  rfl

/-- The Desnanot--Jacobi identity (Dodgson condensation) over a commutative ring. -/
theorem det_mul_det_interior {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det * (M.submatrix (fun i : Fin n => i.castSucc.succ)
        (fun i : Fin n => i.castSucc.succ)).det =
      (M.submatrix Fin.succ Fin.succ).det *
          (M.submatrix Fin.castSucc Fin.castSucc).det -
        (M.submatrix Fin.succ Fin.castSucc).det *
          (M.submatrix Fin.castSucc Fin.succ).det := by
  change M.det * (M.submatrix (interior n) (interior n)).det = _
  suffices h : desnanotJacobiDefect M = 0 by
    unfold desnanotJacobiDefect at h
    exact sub_eq_zero.mp h
  set X := mvPolynomialX (Fin (n + 2)) (Fin (n + 2)) ℤ
  let K := FractionRing (MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ)
  let ι : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ →+* K := algebraMap _ K
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have hX : desnanotJacobiDefect X = 0 := by
    apply hι
    rw [map_zero, desnanotJacobiDefect_map]
    unfold desnanotJacobiDefect
    rw [sub_eq_zero]
    apply desnanotJacobi_field
    intro hzero
    have hcore : (X.submatrix (interior n) (interior n)).det ≠ 0 := by
      intro hone
      have := congrArg (MvPolynomial.eval fun p : Fin (n + 2) × Fin (n + 2) =>
        (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ) p.1 p.2) hone
      rw [RingHom.map_det, map_zero] at this
      have heval :
          (MvPolynomial.eval fun p : Fin (n + 2) × Fin (n + 2) =>
            (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ) p.1 p.2).mapMatrix
              (X.submatrix (interior n) (interior n)) = 1 := by
        ext i j
        simp [X, interior, Matrix.one_apply, Fin.ext_iff]
      rw [heval, det_one] at this
      exact one_ne_zero this
    apply hcore
    apply hι
    rw [map_zero, RingHom.map_det]
    exact hzero
  have hmap := desnanotJacobiDefect_map
    (MvPolynomial.aeval fun p : Fin (n + 2) × Fin (n + 2) => M p.1 p.2 :
      MvPolynomial _ ℤ →ₐ[ℤ] R).toRingHom X
  rw [hX, map_zero] at hmap
  rw [hmap]
  congr 1
  exact (mvPolynomialX_mapMatrix_aeval ℤ M).symm

end

end Matrix
