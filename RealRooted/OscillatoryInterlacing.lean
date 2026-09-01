import RealRooted.CauchyInterlacing.Polynomial
import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Core

/-!
# Strict principal-section interlacing for oscillatory matrices

This module is the RealRooted endpoint of the Whitney-reduction and
oscillatory-matrix core. It combines that matrix theory with polynomial Cauchy
interlacing to obtain strict interlacing, simple roots, root-disjointness, and
positive spectrum for consecutive principal sections.
-/

namespace Matrix

/-- Strict trailing-principal interlacing for the classical oscillatory
criterion. The `Interlaces` component supplies weak interlacing and splitness;
the two root-multiplicity conclusions together with root-disjointness make
every interlacing inequality strict. All roots of the ambient characteristic
polynomial are positive. -/
theorem IsTotallyNonneg.trailing_charpoly_strictInterlaces {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin N, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < A i.succ i.castSucc) :
    RealRooted.Interlaces
        (A.submatrix Fin.succ Fin.succ).charpoly A.charpoly ∧
      (∀ x : ℝ, A.charpoly.IsRoot x →
        A.charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x →
        (A.submatrix Fin.succ Fin.succ).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬(A.charpoly.IsRoot x ∧
        (A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x)) ∧
      ∀ x ∈ A.charpoly.roots, 0 < x := by
  obtain ⟨T, hT, hTdet, hTchar, hTtrailing, hTlower, hTupper,
      hTsuper, hTsub⟩ :=
    exists_whitneyTridiagonal_adjacent_pos A hA hdet hsuper hsub
  obtain ⟨S, hS, hSchar, hStrailing, hNoCommonT⟩ :=
    exists_hermitianModel_of_tridiagonal T hTlower hTupper hTsuper hTsub
  have hInterS : RealRooted.Interlaces
      (S.submatrix Fin.succ Fin.succ).charpoly S.charpoly := by
    simpa only [Fin.succAbove_zero] using
      RealRooted.principalSubmatrix_charpoly_interlaces S hS 0
  have hInter : RealRooted.Interlaces
      (A.submatrix Fin.succ Fin.succ).charpoly A.charpoly := by
    rw [← hTchar, ← hTtrailing, ← hSchar, ← hStrailing]
    exact hInterS
  have hNoCommon : ∀ x : ℝ, ¬(A.charpoly.IsRoot x ∧
      (A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x) := by
    intro x hroots
    apply hNoCommonT x
    constructor
    · rw [hTchar]
      exact hroots.1
    · rw [hTtrailing]
      exact hroots.2
  have hPrec : RealRooted.Prec
      (A.submatrix Fin.succ Fin.succ).charpoly A.charpoly :=
    hInter.toPrec
  have hFullSimple : ∀ x : ℝ, A.charpoly.IsRoot x →
      A.charpoly.rootMultiplicity x = 1 := by
    intro x hx
    have hTrailingNotRoot :
        ¬(A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x := by
      intro hxTrailing
      exact hNoCommon x ⟨hx, hxTrailing⟩
    have hTrailingMult :
        (A.submatrix Fin.succ Fin.succ).charpoly.rootMultiplicity x = 0 :=
      Polynomial.rootMultiplicity_eq_zero hTrailingNotRoot
    have hbound := (RealRooted.rootMultiplicity_bounds_of_prec hPrec x).2
    have hpos := (Polynomial.rootMultiplicity_pos A.charpoly_monic.ne_zero).2 hx
    lia
  have hTrailingSimple : ∀ x : ℝ,
      (A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x →
        (A.submatrix Fin.succ Fin.succ).charpoly.rootMultiplicity x = 1 := by
    intro x hx
    have hFullNotRoot : ¬A.charpoly.IsRoot x := by
      intro hxFull
      exact hNoCommon x ⟨hxFull, hx⟩
    have hFullMult : A.charpoly.rootMultiplicity x = 0 :=
      Polynomial.rootMultiplicity_eq_zero hFullNotRoot
    have hbound := (RealRooted.rootMultiplicity_bounds_of_prec hPrec x).1
    have hpos := (Polynomial.rootMultiplicity_pos
      (A.submatrix Fin.succ Fin.succ).charpoly_monic.ne_zero).2 hx
    lia
  refine ⟨hInter, hFullSimple, hTrailingSimple, hNoCommon, ?_⟩
  intro x hx
  have hxRoot : A.charpoly.IsRoot x :=
    (Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hx
  have hxNonneg : 0 ≤ x := hA.nonneg_of_isRoot_charpoly hxRoot
  have hxNe : x ≠ 0 := by
    intro hxZero
    subst x
    have hcoeff : A.charpoly.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hxRoot.eq_zero
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, hcoeff, mul_zero]
  exact lt_of_le_of_ne hxNonneg (Ne.symm hxNe)

/-- Strict leading-principal interlacing for the classical oscillatory
criterion. This is the leading-section orientation of
`IsTotallyNonneg.trailing_charpoly_strictInterlaces`. -/
theorem IsTotallyNonneg.leading_charpoly_strictInterlaces {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin N, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < A i.succ i.castSucc) :
    RealRooted.Interlaces
        (A.submatrix Fin.castSucc Fin.castSucc).charpoly A.charpoly ∧
      (∀ x : ℝ, A.charpoly.IsRoot x →
        A.charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (A.submatrix Fin.castSucc Fin.castSucc).charpoly.IsRoot x →
        (A.submatrix Fin.castSucc Fin.castSucc).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬(A.charpoly.IsRoot x ∧
        (A.submatrix Fin.castSucc Fin.castSucc).charpoly.IsRoot x)) ∧
      ∀ x ∈ A.charpoly.roots, 0 < x := by
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    Matrix.reindex Fin.revPerm Fin.revPerm A
  have hB : B.IsTotallyNonneg := by
    exact hA.finRev
  have hBdet : B.det ≠ 0 := by
    simpa [B] using hdet
  have hBsuper : ∀ i : Fin N, 0 < B i.castSucc i.succ := by
    intro i
    simpa [B, Matrix.submatrix, Fin.rev_castSucc, Fin.rev_succ] using hsub i.rev
  have hBsub : ∀ i : Fin N, 0 < B i.succ i.castSucc := by
    intro i
    simpa [B, Matrix.submatrix, Fin.rev_castSucc, Fin.rev_succ] using hsuper i.rev
  have hstrict := hB.trailing_charpoly_strictInterlaces hBdet hBsuper hBsub
  have hBchar : B.charpoly = A.charpoly := by
    simpa [B] using Matrix.charpoly_reindex Fin.revPerm A
  have hBtail : (B.submatrix Fin.succ Fin.succ).charpoly =
      (A.submatrix Fin.castSucc Fin.castSucc).charpoly := by
    rw [← Matrix.charpoly_reindex Fin.revPerm
      (A.submatrix Fin.castSucc Fin.castSucc)]
    congr 1
    ext i j
    simp [B, Matrix.submatrix, Matrix.reindex_apply,
      Fin.rev_succ]
  simpa only [hBchar, hBtail] using hstrict

end Matrix
