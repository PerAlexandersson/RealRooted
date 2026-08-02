import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Cauchy-Binet determinant expansions

This file develops the rectangular Cauchy-Binet formula. It expands a selected
minor into a sum over intermediate maps, proves that noninjective maps vanish,
and factors each injective map through the increasing enumeration of its image.
The remaining step transports permutation signs and groups by image subset.
-/

open scoped BigOperators

namespace Matrix

/-- Leibniz expansion of a selected minor of a rectangular matrix product. -/
theorem det_submatrix_mul_eq_sum_perm_fun
    {R : Type*} [CommRing R] {l n m q : ℕ}
    (L : Matrix (Fin l) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R)
    (rows : Fin q → Fin l) (cols : Fin q → Fin m) :
    ((L * A).submatrix rows cols).det =
      ∑ σ : Equiv.Perm (Fin q), Equiv.Perm.sign σ •
        ∑ f : Fin q → Fin n,
          ∏ i, L (rows (σ i)) (f i) * A (f i) (cols i) := by
  rw [Matrix.det_apply]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Finset.prod_univ_sum]
  simp

/-- Reassemble the permutation sum for each intermediate-index map. -/
theorem det_submatrix_mul_eq_sum_fun_det
    {R : Type*} [CommRing R] {l n m q : ℕ}
    (L : Matrix (Fin l) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R)
    (rows : Fin q → Fin l) (cols : Fin q → Fin m) :
    ((L * A).submatrix rows cols).det =
      ∑ f : Fin q → Fin n,
        (L.submatrix rows f).det * ∏ i, A (f i) (cols i) := by
  rw [det_submatrix_mul_eq_sum_perm_fun]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro f
  rw [Matrix.det_apply]
  simp only [Matrix.submatrix_apply, Finset.prod_mul_distrib]
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc]

end Matrix

private theorem coe_ofFinEmb_eq_range {q : ℕ} {I : Type*} (f : Fin q ↪ I) :
    (Set.powersetCard.ofFinEmb q I f : Set I) = Set.range f := by
  ext x
  simp [Set.powersetCard.ofFinEmb, Set.powersetCard.map]

/-- An injective finite map into a linear order factors through the increasing
enumeration of its image and a permutation of its domain. -/
theorem Set.powersetCard.exists_orderEmb_comp_perm_eq_of_injective
    {q : ℕ} {I : Type*} [LinearOrder I]
    (f : Fin q → I) (hf : Function.Injective f) :
    ∃ s : Set.powersetCard I q, ∃ p : Equiv.Perm (Fin q),
      ∀ i, Set.powersetCard.ofFinEmbEquiv.symm s (p i) = f i := by
  let emb : Fin q ↪ I := ⟨f, hf⟩
  let s : Set.powersetCard I q := Set.powersetCard.ofFinEmb q I emb
  let e : Fin q ↪o I := Set.powersetCard.ofFinEmbEquiv.symm s
  have hfRange : Set.range f = (s : Set I) :=
    (coe_ofFinEmb_eq_range emb).symm
  have heRange : Set.range e = (s : Set I) := by
    calc
      Set.range e = (Set.powersetCard.ofFinEmb q I e.toEmbedding : Set I) :=
        (coe_ofFinEmb_eq_range e.toEmbedding).symm
      _ = (s : Set I) := congrArg
        (fun t : Set.powersetCard I q => (t : Set I))
        (Set.powersetCard.ofFinEmbEquiv.apply_symm_apply s)
  have hRange : Set.range f = Set.range e := hfRange.trans heRange.symm
  let ee : Fin q ≃ Set.range e := Equiv.ofInjective e e.injective
  let p : Equiv.Perm (Fin q) :=
    (Equiv.ofInjective f hf).trans
      ((Equiv.setCongr hRange).trans ee.symm)
  refine ⟨s, p, ?_⟩
  intro i
  have hfi : f i ∈ Set.range e := hRange ▸ ⟨i, rfl⟩
  change e (ee.symm ⟨f i, hfi⟩) = f i
  exact congrArg Subtype.val (ee.apply_symm_apply ⟨f i, hfi⟩)
