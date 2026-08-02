import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

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


private theorem range_orderEmbOfPowersetCard {q : ℕ} {I : Type*}
    [LinearOrder I] (s : Set.powersetCard I q) :
    Set.range (Set.powersetCard.ofFinEmbEquiv.symm s) = (s : Set I) := by
  let e : Fin q ↪o I := Set.powersetCard.ofFinEmbEquiv.symm s
  calc
    Set.range e = (Set.powersetCard.ofFinEmb q I e.toEmbedding : Set I) :=
      (coe_ofFinEmb_eq_range e.toEmbedding).symm
    _ = (s : Set I) := congrArg
      (fun t : Set.powersetCard I q => (t : Set I))
      (Set.powersetCard.ofFinEmbEquiv.apply_symm_apply s)

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
  have hRange : Set.range f = Set.range e :=
    hfRange.trans (range_orderEmbOfPowersetCard s).symm
  let ee : Fin q ≃ Set.range e := Equiv.ofInjective e e.injective
  let p : Equiv.Perm (Fin q) :=
    (Equiv.ofInjective f hf).trans
      ((Equiv.setCongr hRange).trans ee.symm)
  refine ⟨s, p, ?_⟩
  intro i
  have hfi : f i ∈ Set.range e := hRange ▸ ⟨i, rfl⟩
  change e (ee.symm ⟨f i, hfi⟩) = f i
  exact congrArg Subtype.val (ee.apply_symm_apply ⟨f i, hfi⟩)

private theorem range_comp_perm {q : ℕ} {I : Type*}
    (e : Fin q → I) (p : Equiv.Perm (Fin q)) :
    Set.range (fun i => e (p i)) = Set.range e := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨p i, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨p.symm j, by simp⟩

/-- The ordered-image/permutation representation of an injective finite map is
unique. -/
theorem Set.powersetCard.orderEmb_comp_perm_injective
    {q : ℕ} {I : Type*} [LinearOrder I] :
    Function.Injective
      (fun z : Set.powersetCard I q × Equiv.Perm (Fin q) =>
        fun i => Set.powersetCard.ofFinEmbEquiv.symm z.1 (z.2 i)) := by
  rintro ⟨s, p⟩ ⟨t, r⟩ h
  let es : Fin q ↪o I := Set.powersetCard.ofFinEmbEquiv.symm s
  let et : Fin q ↪o I := Set.powersetCard.ofFinEmbEquiv.symm t
  have hst : s = t := by
    apply Subtype.ext
    apply Finset.coe_injective
    calc
      (s : Set I) = Set.range es := (range_orderEmbOfPowersetCard s).symm
      _ = Set.range (fun i => es (p i)) := (range_comp_perm es p).symm
      _ = Set.range (fun i => et (r i)) := congrArg Set.range h
      _ = Set.range et := range_comp_perm et r
      _ = (t : Set I) := range_orderEmbOfPowersetCard t
  subst t
  have hpr : p = r := by
    apply Equiv.ext
    intro i
    exact es.injective (congrFun h i)
  exact Prod.ext rfl hpr

/-- Ordered image and a domain permutation parameterize all finite embeddings. -/
noncomputable def Set.powersetCard.orderEmbPermEquivEmbedding
    {q : ℕ} {I : Type*} [LinearOrder I] :
    Set.powersetCard I q × Equiv.Perm (Fin q) ≃ (Fin q ↪ I) :=
  Equiv.ofBijective
    (fun z =>
      ⟨fun i => Set.powersetCard.ofFinEmbEquiv.symm z.1 (z.2 i),
        (Set.powersetCard.ofFinEmbEquiv.symm z.1).injective.comp
          z.2.injective⟩)
    ⟨by
      intro z w h
      apply Set.powersetCard.orderEmb_comp_perm_injective
      funext i
      exact congrArg (fun g : Fin q ↪ I => g i) h,
    by
      intro f
      obtain ⟨s, p, h⟩ :=
        Set.powersetCard.exists_orderEmb_comp_perm_eq_of_injective f f.injective
      refine ⟨(s, p), ?_⟩
      ext i
      exact h i⟩

/-- Reindex a sum over finite embeddings by ordered image and permutation. -/
theorem Set.powersetCard.sum_embedding_eq_sum_orderEmb_perm
    {q : ℕ} {I M : Type*} [LinearOrder I] [Fintype I] [AddCommMonoid M]
    (g : (Fin q ↪ I) → M) :
    ∑ f : Fin q ↪ I, g f =
      ∑ s : Set.powersetCard I q, ∑ p : Equiv.Perm (Fin q),
        g ⟨fun i => Set.powersetCard.ofFinEmbEquiv.symm s (p i),
          (Set.powersetCard.ofFinEmbEquiv.symm s).injective.comp p.injective⟩ := by
  calc
    ∑ f : Fin q ↪ I, g f =
        ∑ z, g (Set.powersetCard.orderEmbPermEquivEmbedding z) :=
      (Set.powersetCard.orderEmbPermEquivEmbedding.sum_comp g).symm
    _ = ∑ s : Set.powersetCard I q, ∑ p : Equiv.Perm (Fin q),
        g (Set.powersetCard.orderEmbPermEquivEmbedding (s, p)) :=
      Fintype.sum_prod_type _
    _ = _ := by
      simp [Set.powersetCard.orderEmbPermEquivEmbedding]

private theorem sum_function_eq_sum_embedding_of_zero_noninjective
    {q : ℕ} {I M : Type*} [Fintype I] [AddCommMonoid M]
    (g : (Fin q → I) → M)
    (hzero : ∀ f, ¬ Function.Injective f → g f = 0) :
    ∑ f : Fin q → I, g f = ∑ e : Fin q ↪ I, g e := by
  classical
  calc
    ∑ f : Fin q → I, g f =
        (∑ f : {f : Fin q → I // Function.Injective f}, g f) +
          ∑ f : {f : Fin q → I // ¬ Function.Injective f}, g f :=
      (Fintype.sum_subtype_add_sum_subtype Function.Injective g).symm
    _ = ∑ f : {f : Fin q → I // Function.Injective f}, g f := by
      rw [show (∑ f : {f : Fin q → I // ¬ Function.Injective f}, g f) = 0 by
        apply Finset.sum_eq_zero
        intro f _
        exact hzero f f.property, add_zero]
    _ = ∑ f : Fin q ↪ I, g f := by
      exact Fintype.sum_equiv
        (Equiv.subtypeInjectiveEquivEmbedding (Fin q) I) _ _ fun _ => rfl

private theorem sum_perm_det_submatrix_comp_mul_prod_eq
    {R : Type*} [CommRing R] {l n m q : ℕ}
    (L : Matrix (Fin l) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R)
    (rows : Fin q → Fin l) (cols : Fin q → Fin m)
    (e : Fin q → Fin n) :
    (∑ p : Equiv.Perm (Fin q),
        (L.submatrix rows (fun i => e (p i))).det *
          ∏ i, A (e (p i)) (cols i)) =
      (L.submatrix rows e).det * (A.submatrix e cols).det := by
  calc
    _ = (L.submatrix rows e).det *
          ∑ p : Equiv.Perm (Fin q),
            Equiv.Perm.sign p • ∏ i, A (e (p i)) (cols i) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro p
      rw [show L.submatrix rows (fun i => e (p i)) =
          (L.submatrix rows e).submatrix id p by rfl]
      rw [Matrix.det_permute', Units.smul_def,
        ← Int.cast_smul_eq_zsmul R]
      simp [mul_comm, mul_assoc]
    _ = (L.submatrix rows e).det * (A.submatrix e cols).det := by
      congr 1
      rw [Matrix.det_apply]
      rfl

/-- Rectangular Cauchy--Binet for selected square minors. -/
theorem Matrix.det_submatrix_mul_eq_sum_powersetCard
    {R : Type*} [CommRing R] {l n m q : ℕ}
    (L : Matrix (Fin l) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R)
    (rows : Fin q → Fin l) (cols : Fin q → Fin m) :
    ((L * A).submatrix rows cols).det =
      ∑ s : Set.powersetCard (Fin n) q,
        (L.submatrix rows
          (Set.powersetCard.ofFinEmbEquiv.symm s)).det *
        (A.submatrix
          (Set.powersetCard.ofFinEmbEquiv.symm s) cols).det := by
  classical
  rw [Matrix.det_submatrix_mul_eq_sum_fun_det]
  rw [sum_function_eq_sum_embedding_of_zero_noninjective]
  · rw [Set.powersetCard.sum_embedding_eq_sum_orderEmb_perm]
    apply Fintype.sum_congr
    intro s
    simpa using sum_perm_det_submatrix_comp_mul_prod_eq L A rows cols
      (Set.powersetCard.ofFinEmbEquiv.symm s)
  · intro f hf
    rw [Matrix.det_submatrix_eq_zero_of_not_injective_right L rows f hf,
      zero_mul]

private theorem selected_mulVec_injective
    {R : Type*} [Field R] {n m q : ℕ}
    (A : Matrix (Fin n) (Fin m) R)
    (hA : Function.Injective A.mulVec)
    (cols : Fin q → Fin m) (hcols : StrictMono cols) :
    Function.Injective (A.submatrix id cols).mulVec := by
  rw [Matrix.mulVec_injective_iff]
  have h := (Matrix.mulVec_injective_iff.mp hA).comp cols hcols.injective
  simpa [Matrix.col, Function.comp_def] using h

private theorem exists_left_inverse_matrix
    {R : Type*} [Field R] {n q : ℕ}
    (B : Matrix (Fin n) (Fin q) R)
    (hB : Function.Injective B.mulVec) :
    ∃ C : Matrix (Fin q) (Fin n) R, C * B = 1 := by
  let f := Matrix.toLin' B
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    apply hB
    simpa only [f, Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hf
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg,
    ← Matrix.toLin'_one, LinearMap.toMatrix'_toLin']

/-- Full column rank gives a nonzero maximal minor on strictly increasing rows.

The proof restricts the independent columns, takes a linear left inverse, and
applies rectangular Cauchy--Binet to the resulting identity matrix. -/
theorem Matrix.exists_ordered_minor_ne_zero_of_mulVec_injective
    {R : Type*} [Field R] {n m q : ℕ}
    (A : Matrix (Fin n) (Fin m) R)
    (hA : Function.Injective A.mulVec)
    (cols : Fin q → Fin m) (hcols : StrictMono cols) :
    ∃ rows : Fin q → Fin n, StrictMono rows ∧
      (A.submatrix rows cols).det ≠ 0 := by
  classical
  let B := A.submatrix id cols
  have hB : Function.Injective B.mulVec := by
    exact selected_mulVec_injective A hA cols hcols
  obtain ⟨C, hCB⟩ := exists_left_inverse_matrix B hB
  have hsum :
      (∑ s : Set.powersetCard (Fin n) q,
        (C.submatrix id
          (Set.powersetCard.ofFinEmbEquiv.symm s)).det *
        (B.submatrix
          (Set.powersetCard.ofFinEmbEquiv.symm s) id).det) ≠ 0 := by
    rw [← Matrix.det_submatrix_mul_eq_sum_powersetCard C B id id, hCB]
    simp
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (by simpa using hsum)
  refine ⟨Set.powersetCard.ofFinEmbEquiv.symm s,
    (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono, ?_⟩
  have hminor := (mul_ne_zero_iff.mp hs).2
  simpa [B] using hminor
