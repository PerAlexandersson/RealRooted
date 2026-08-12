import RealRooted.BorceaBranden.Applications.DegreeBoxPolarization
import RealRooted.BorceaBranden.FiniteSymbolPreserver
import RealRooted.Polarization

/-!
# Source diagonalization for a general degree box

This file begins the arbitrary degree-vector polarization layer in the proof of
Borcea--Brändén Theorem 1.1. A coordinate of degree `κ i` is replaced by the
multiaffine block `Fin (κ i)`, and diagonal projection renames every variable
in that block back to coordinate `i`.
-/

open scoped BigOperators

namespace RealRooted.BorceaBranden

noncomputable section

/-- The multiaffine source obtained by replacing coordinate `i` with
`κ i` copies. -/
abbrev PolarizedSource {σ : Type*} (κ : σ → ℕ) := Σ i, Fin (κ i)

/-- Variables after polarizing exactly the coordinates in `S`. -/
def SourcePolarizationStageVars {σ : Type*} [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ) :=
  (Σ i : {i // i ∈ S}, Fin (κ i)) ⊕ {i : σ // i ∉ S}

/-- Stage variables other than a selected unpolarized coordinate. -/
def SourcePolarizationStageRest {σ : Type*} [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ) (i : σ) :=
  (Σ j : {j // j ∈ S}, Fin (κ j)) ⊕
    {j : σ // j ∉ S ∧ j ≠ i}

/-- Isolate one unpolarized stage coordinate as a `Fin 1` block. -/
def sourcePolarizationStageIsolateEquiv
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S) :
    SourcePolarizationStageVars κ S ≃
      SourcePolarizationStageRest κ S i ⊕ Fin 1 where
  toFun x := by
    rcases x with x | j
    · exact Sum.inl (Sum.inl x)
    · by_cases hji : j.1 = i
      · exact Sum.inr 0
      · exact Sum.inl (Sum.inr ⟨j.1, j.2, hji⟩)
  invFun x := by
    rcases x with x | _k
    · rcases x with x | j
      · exact Sum.inl x
      · exact Sum.inr ⟨j.1, j.2.1⟩
    · exact Sum.inr ⟨i, hi⟩
  left_inv x := by
    rcases x with x | j
    · rfl
    · dsimp
      by_cases hji : j.1 = i
      · simp only [dif_pos hji]
        change (Sum.inr ⟨i, hi⟩ :
          SourcePolarizationStageVars κ S) = Sum.inr j
        congr 1
        exact Subtype.ext hji.symm
      · simp [hji]
  right_inv x := by
    rcases x with x | k
    · rcases x with x | j
      · rfl
      · dsimp
        simp [j.2.2]
    · fin_cases k
      dsimp
      simp

/-- Replace the isolated singleton by its polarized block. -/
def sourcePolarizationStageInstallEquiv
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S) :
    SourcePolarizationStageVars κ (insert i S) ≃
      SourcePolarizationStageRest κ S i ⊕ Fin (κ i) where
  toFun x := by
    rcases x with x | j
    · rcases x with ⟨j, k⟩
      by_cases hji : j.1 = i
      · exact Sum.inr (Fin.cast (congrArg κ hji) k)
      · exact Sum.inl (Sum.inl
          ⟨⟨j.1, (Finset.mem_insert.mp j.2).resolve_left hji⟩, k⟩)
    · have hj : j.1 ≠ i ∧ j.1 ∉ S := by
        simpa [Finset.mem_insert] using j.2
      exact Sum.inl (Sum.inr ⟨j.1, hj.2, hj.1⟩)
  invFun x := by
    rcases x with x | k
    · rcases x with x | j
      · exact Sum.inl ⟨⟨x.1.1, Finset.mem_insert_of_mem x.1.2⟩, x.2⟩
      · exact Sum.inr
          ⟨j.1, by simp [Finset.mem_insert, j.2.1, j.2.2]⟩
    · exact Sum.inl ⟨⟨i, Finset.mem_insert_self i S⟩, k⟩
  left_inv x := by
    rcases x with x | j
    · rcases x with ⟨j, k⟩
      dsimp
      by_cases hji : j.1 = i
      · rcases j with ⟨j, hj⟩
        dsimp at hji ⊢
        subst i
        simp
      · simp [hji]
    · rfl
  right_inv x := by
    rcases x with x | k
    · rcases x with x | j
      · have hne : x.1.1 ≠ i := fun h => hi (h ▸ x.1.2)
        dsimp
        simp [hne]
      · rfl
    · dsimp
      simp

/-- At the empty stage, the variables are the original source variables. -/
def sourcePolarizationStageEmptyEquiv
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) :
    SourcePolarizationStageVars κ ∅ ≃ σ where
  toFun x := by
    rcases x with x | i
    · have hx : x.1.1 ∈ (∅ : Finset σ) := x.1.2
      exact False.elim (Finset.notMem_empty _ hx)
    · exact i.1
  invFun i := Sum.inr ⟨i, by simp⟩
  left_inv x := by
    rcases x with x | i
    · have hx : x.1.1 ∈ (∅ : Finset σ) := x.1.2
      exact False.elim (Finset.notMem_empty _ hx)
    · rfl
  right_inv i := rfl

/-- At the final stage, all variables belong to their polarized blocks. -/
def sourcePolarizationStageUnivEquiv
    {σ : Type*} [Fintype σ] [DecidableEq σ] (κ : σ → ℕ) :
    SourcePolarizationStageVars κ Finset.univ ≃ PolarizedSource κ where
  toFun x := by
    rcases x with x | i
    · exact ⟨x.1.1, x.2⟩
    · exact False.elim (i.2 (Finset.mem_univ i.1))
  invFun x := Sum.inl ⟨⟨x.1, Finset.mem_univ x.1⟩, x.2⟩
  left_inv x := by
    rcases x with x | i
    · rfl
    · exact False.elim (i.2 (Finset.mem_univ i.1))
  right_inv x := by
    rcases x with ⟨i, k⟩
    rfl

/-- Polarize one raw coordinate of a source-polarization stage. -/
noncomputable def sourcePolarizationStageStep
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S)
    (P : MvPolynomial (SourcePolarizationStageVars κ S) ℂ) :
    MvPolynomial (SourcePolarizationStageVars κ (insert i S)) ℂ :=
  MvPolynomial.rename (sourcePolarizationStageInstallEquiv κ S i hi).symm
    (MvPolynomial.sourceBlockPolarization (κ i)
      (MvPolynomial.rename (sourcePolarizationStageIsolateEquiv κ S i hi) P))

private theorem degreeOf_rename_stageIsolate_selected
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S)
    (P : MvPolynomial (SourcePolarizationStageVars κ S) ℂ) :
    (MvPolynomial.rename (sourcePolarizationStageIsolateEquiv κ S i hi) P).degreeOf
        (Sum.inr default) = P.degreeOf (Sum.inr ⟨i, hi⟩) := by
  have h := MvPolynomial.degreeOf_rename_of_injective
    (sourcePolarizationStageIsolateEquiv κ S i hi).injective
    (Sum.inr ⟨i, hi⟩) (p := P)
  convert h using 1
  · simp [sourcePolarizationStageIsolateEquiv]
  · rfl

/-- One staged source-polarization step preserves upper-half-plane
stability. -/
theorem mvUpperHalfPlaneStable_sourcePolarizationStageStep
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S)
    (P : MvPolynomial (SourcePolarizationStageVars κ S) ℂ)
    (hdeg : P.degreeOf (Sum.inr ⟨i, hi⟩) ≤ κ i)
    (hstable : MvUpperHalfPlaneStable P) :
    MvUpperHalfPlaneStable (sourcePolarizationStageStep κ S i hi P) := by
  unfold sourcePolarizationStageStep
  apply MvUpperHalfPlaneStable.rename
  apply MvPolynomial.mvUpperHalfPlaneStable_sourceBlockPolarization
  · rwa [degreeOf_rename_stageIsolate_selected]
  · exact hstable.rename

/-- A staged polarization step does not increase the degree of any raw
coordinate that remains unprocessed. -/
theorem degreeOf_sourcePolarizationStageStep_raw_le
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S)
    (P : MvPolynomial (SourcePolarizationStageVars κ S) ℂ)
    (j : σ) (hj : j ∉ insert i S) :
    (sourcePolarizationStageStep κ S i hi P).degreeOf
        (Sum.inr ⟨j, hj⟩) ≤
      P.degreeOf (Sum.inr ⟨j, fun hjS => hj (Finset.mem_insert_of_mem hjS)⟩) := by
  have hji : j ≠ i := by
    intro h
    apply hj
    subst j
    exact Finset.mem_insert_self i S
  have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
  let rj : {j : σ // j ∉ S ∧ j ≠ i} := ⟨j, hjS, hji⟩
  let oldj : {j : σ // j ∉ S} := ⟨j, hjS⟩
  let newj : {j : σ // j ∉ insert i S} := ⟨j, hj⟩
  let isolate := sourcePolarizationStageIsolateEquiv κ S i hi
  let install := sourcePolarizationStageInstallEquiv κ S i hi
  let Q := MvPolynomial.rename isolate P
  let R := MvPolynomial.sourceBlockPolarization (κ i) Q
  have hinstallMap : install.symm (Sum.inl (Sum.inr rj)) = Sum.inr newj := by
    dsimp [install, sourcePolarizationStageInstallEquiv]
  have hinstall :
      (MvPolynomial.rename install.symm R).degreeOf (Sum.inr newj) =
        R.degreeOf (Sum.inl (Sum.inr rj)) := by
    rw [← hinstallMap]
    exact MvPolynomial.degreeOf_rename_of_injective install.symm.injective
      (Sum.inl (Sum.inr rj))
  have hisolateMap : isolate (Sum.inr oldj) = Sum.inl (Sum.inr rj) := by
    dsimp [isolate, sourcePolarizationStageIsolateEquiv]
    rw [dif_neg hji]
    apply congrArg (fun x => Sum.inl (Sum.inr x))
    exact Subtype.ext rfl
  have hisolate :
      Q.degreeOf (Sum.inl (Sum.inr rj)) = P.degreeOf (Sum.inr oldj) := by
    rw [← hisolateMap]
    exact MvPolynomial.degreeOf_rename_of_injective isolate.injective
      (Sum.inr oldj)
  change (MvPolynomial.rename install.symm R).degreeOf (Sum.inr newj) ≤
    P.degreeOf (Sum.inr oldj)
  rw [hinstall]
  exact (MvPolynomial.degreeOf_sourceBlockPolarization_inl_le
    (κ i) Q (Sum.inr rj)).trans_eq hisolate

/-- The coefficient of a general source monomial, retaining all output
variables. -/
noncomputable def sourceCoefficientGeneral
    {σ τ : Type*} (P : MvPolynomial (τ ⊕ σ) ℂ) (r : σ →₀ ℕ) :
    MvPolynomial τ ℂ :=
  (MvPolynomial.sumAlgEquiv ℂ σ τ
    (MvPolynomial.rename (Equiv.sumComm τ σ) P)).coeff r

/-- Coefficients of `sourceCoefficientGeneral` are the corresponding combined
output/source coefficients of the original polynomial. -/
theorem coeff_sourceCoefficientGeneral
    {σ τ : Type*} (P : MvPolynomial (τ ⊕ σ) ℂ)
    (u : τ →₀ ℕ) (r : σ →₀ ℕ) :
    MvPolynomial.coeff u (sourceCoefficientGeneral P r) =
      MvPolynomial.coeff (u.sumElim r) P := by
  classical
  unfold sourceCoefficientGeneral
  rw [MvPolynomial.coeff_coeff_sumAlgEquiv]
  have hmap :
      (u.sumElim r).mapDomain (Equiv.sumComm τ σ) = r.sumElim u := by
    ext x
    rcases x with i | i
    · simp
    · simp
  rw [← hmap, MvPolynomial.coeff_rename_mapDomain
    (Equiv.sumComm τ σ) (Equiv.sumComm τ σ).injective]

/-- Extracting a source coefficient does not increase the degree in any
output coordinate. -/
theorem degreeOf_sourceCoefficientGeneral_le
    {σ τ : Type*} (P : MvPolynomial (τ ⊕ σ) ℂ)
    (r : σ →₀ ℕ) (j : τ) :
    (sourceCoefficientGeneral P r).degreeOf j ≤
      P.degreeOf (Sum.inl j) := by
  rw [MvPolynomial.degreeOf_eq_sup, Finset.sup_le_iff]
  intro u hu
  change (u.sumElim r) (Sum.inl j) ≤ P.degreeOf (Sum.inl j)
  apply MvPolynomial.monomial_le_degreeOf
  rw [MvPolynomial.mem_support_iff, ← coeff_sourceCoefficientGeneral]
  exact MvPolynomial.mem_support_iff.mp hu

/-- Source-coefficient extraction on a separated output/source monomial. -/
theorem sourceCoefficientGeneral_monomial_sumElim
    {σ τ : Type*} [DecidableEq σ]
    (u : τ →₀ ℕ) (a r : σ →₀ ℕ) (c : ℂ) :
    sourceCoefficientGeneral (MvPolynomial.monomial (u.sumElim a) c) r =
      if r = a then MvPolynomial.monomial u c else 0 := by
  classical
  ext d
  rw [coeff_sourceCoefficientGeneral]
  by_cases hra : r = a
  · subst r
    have hleft : u.sumElim a = d.sumElim a ↔ u = d := by
      constructor
      · intro h
        ext i
        exact DFunLike.congr_fun h (Sum.inl i)
      · rintro rfl
        rfl
    simp [MvPolynomial.coeff_monomial, hleft]
  · have hne : d.sumElim r ≠ u.sumElim a := by
      intro h
      apply hra
      ext i
      exact DFunLike.congr_fun h (Sum.inr i)
    have hne' : u.sumElim a ≠ d.sumElim r := Ne.symm hne
    simp [MvPolynomial.coeff_monomial, hra, hne']

@[simp] theorem sourceCoefficientGeneral_add
    {σ τ : Type*} (P Q : MvPolynomial (τ ⊕ σ) ℂ) (r : σ →₀ ℕ) :
    sourceCoefficientGeneral (P + Q) r =
      sourceCoefficientGeneral P r + sourceCoefficientGeneral Q r := by
  simp [sourceCoefficientGeneral]

@[simp] theorem sourceCoefficientGeneral_smul
    {σ τ : Type*} (c : ℂ) (P : MvPolynomial (τ ⊕ σ) ℂ)
    (r : σ →₀ ℕ) :
    sourceCoefficientGeneral (c • P) r =
      c • sourceCoefficientGeneral P r := by
  simp [sourceCoefficientGeneral]

/-- The product of elementary symmetric polynomials in all polarized source
blocks. -/
noncomputable def blockElementarySymmetric
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (r : σ →₀ ℕ) :
    MvPolynomial (PolarizedSource κ) ℂ :=
  ∏ i, MvPolynomial.rename (fun j : Fin (κ i) => ⟨i, j⟩)
    (MvPolynomial.esymm (Fin (κ i)) ℂ (r i))

/-- Polarize every variable in the source block of a polynomial while leaving
the output block unchanged. Terms outside the degree box are discarded. -/
noncomputable def sourceBlockwisePolarizationGeneral
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (P : MvPolynomial (τ ⊕ σ) ℂ) :
    MvPolynomial (τ ⊕ PolarizedSource κ) ℂ :=
  ∑ r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i},
    MvPolynomial.C ((MvPolynomial.boxChoose κ r.1 : ℂ)⁻¹) *
      MvPolynomial.rename Sum.inl (sourceCoefficientGeneral P r.1) *
        MvPolynomial.rename Sum.inr (blockElementarySymmetric κ r.1)

/-- General source-block polarization on a separated output/source
monomial. -/
theorem sourceBlockwisePolarizationGeneral_monomial_sumElim
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (u : τ →₀ ℕ) (a : σ →₀ ℕ) (ha : ∀ i, a i ≤ κ i) (c : ℂ) :
    sourceBlockwisePolarizationGeneral κ
        (MvPolynomial.monomial (u.sumElim a) c) =
      MvPolynomial.C ((MvPolynomial.boxChoose κ a : ℂ)⁻¹) *
        MvPolynomial.rename Sum.inl (MvPolynomial.monomial u c) *
          MvPolynomial.rename Sum.inr (blockElementarySymmetric κ a) := by
  classical
  unfold sourceBlockwisePolarizationGeneral
  rw [Fintype.sum_eq_single ⟨a, ha⟩]
  · rw [sourceCoefficientGeneral_monomial_sumElim]
    simp
  · intro r hra
    have hr_ne : r.1 ≠ a := fun h => hra (Subtype.ext h)
    rw [sourceCoefficientGeneral_monomial_sumElim]
    simp [hr_ne]

/-- General source-block polarization as a complex-linear map. -/
noncomputable def sourceBlockwisePolarizationGeneralLinearMap
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ) :
    MvPolynomial (τ ⊕ σ) ℂ →ₗ[ℂ]
      MvPolynomial (τ ⊕ PolarizedSource κ) ℂ where
  toFun := sourceBlockwisePolarizationGeneral κ
  map_add' P Q := by
    unfold sourceBlockwisePolarizationGeneral
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [sourceCoefficientGeneral_add, map_add]
    ring
  map_smul' c P := by
    unfold sourceBlockwisePolarizationGeneral
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [sourceCoefficientGeneral_smul, map_smul]
    simp only [MvPolynomial.smul_eq_C_mul, RingHom.id_apply]
    ring

@[simp] theorem sourceBlockwisePolarizationGeneralLinearMap_apply
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (P : MvPolynomial (τ ⊕ σ) ℂ) :
    sourceBlockwisePolarizationGeneralLinearMap κ P =
      sourceBlockwisePolarizationGeneral κ P := rfl

private theorem mapDomain_sigma_fst_le {σ : Type*} [Finite σ]
    (κ : σ → ℕ) (m : PolarizedSource κ →₀ ℕ)
    (hm : ∀ a, m a ≤ 1) (i : σ) :
    (m.mapDomain Sigma.fst) i ≤ κ i := by
  classical
  letI := Fintype.ofFinite σ
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  change (∑ x ∈ m.support, if x.fst = i then m x else 0) ≤ κ i
  calc
    (∑ x ∈ m.support, if x.fst = i then m x else 0) ≤
        ∑ x ∈ m.support, if x.fst = i then 1 else 0 := by
      exact Finset.sum_le_sum fun x _ => by split_ifs <;> simp_all
    _ ≤ ∑ x : PolarizedSource κ, if x.fst = i then 1 else 0 := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = κ i := by
      rw [Fintype.sum_sigma, Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [hji]
      · simp

/-- Aggregate a multiaffine exponent vector across each polarized block. -/
noncomputable def diagonalDegreeBoxIndexGeneral
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : PolarizedSource κ →₀ ℕ // ∀ i, m i ≤ 1}) :
    {m : σ →₀ ℕ // ∀ i, m i ≤ κ i} :=
  ⟨m.1.mapDomain Sigma.fst, mapDomain_sigma_fst_le κ m.1 m.2⟩

/-- Diagonal projection from the multiaffine polarized source back to the
original coordinate-wise degree box. -/
noncomputable def diagonalProjectionDegreeBoxGeneral
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE (PolarizedSource κ) ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial.degreeOfLE σ ℂ κ where
  toFun p := ⟨MvPolynomial.rename Sigma.fst p.1, by
    rw [MvPolynomial.mem_degreeOfLE]
    intro d hd i
    obtain ⟨u, hu, hcoeff⟩ := MvPolynomial.coeff_rename_ne_zero
      Sigma.fst p.1 d (MvPolynomial.mem_support_iff.mp hd)
    rw [← hu]
    apply mapDomain_sigma_fst_le κ u
    intro a
    exact (MvPolynomial.mem_degreeOfLE p.1).mp p.2 u
      (MvPolynomial.mem_support_iff.mpr hcoeff) a⟩
  map_add' p q := by
    apply Subtype.ext
    simp
  map_smul' c p := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_diagonalProjectionDegreeBoxGeneral
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (p : MvPolynomial.degreeOfLE (PolarizedSource κ) ℂ (fun _ => 1)) :
    (diagonalProjectionDegreeBoxGeneral κ p : MvPolynomial σ ℂ) =
      MvPolynomial.rename Sigma.fst p.1 := rfl

@[simp]
theorem diagonalProjectionDegreeBoxGeneral_basis
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : PolarizedSource κ →₀ ℕ // ∀ i, m i ≤ 1}) :
    (diagonalProjectionDegreeBoxGeneral κ
      (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ => 1) m) :
        MvPolynomial σ ℂ) =
    MvPolynomial.monomial (m.1.mapDomain Sigma.fst) 1 := by
  rw [coe_diagonalProjectionDegreeBoxGeneral,
    MvPolynomial.coe_basisDegreeOfLE, MvPolynomial.rename_monomial]

/-- Diagonal projection sends a multiaffine basis monomial to the original
degree-box basis monomial obtained by aggregating each source block. -/
theorem diagonalProjectionDegreeBoxGeneral_basis_eq_basis
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : PolarizedSource κ →₀ ℕ // ∀ i, m i ≤ 1}) :
    diagonalProjectionDegreeBoxGeneral κ
        (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ => 1) m) =
      MvPolynomial.basisDegreeOfLE κ
        (diagonalDegreeBoxIndexGeneral κ m) := by
  apply Subtype.ext
  rw [diagonalProjectionDegreeBoxGeneral_basis,
    MvPolynomial.coe_basisDegreeOfLE]
  congr 1

private def blockEmbedding {σ : Type*} (κ : σ → ℕ) (i : σ) :
    Fin (κ i) → PolarizedSource κ := fun j => ⟨i, j⟩

private theorem blockEmbedding_injective {σ : Type*} (κ : σ → ℕ) (i : σ) :
    Function.Injective (blockEmbedding κ i) := by
  intro j k h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

/-- The blockwise polarization of a degree-box basis monomial. -/
noncomputable def blockwisePolarizationBasis
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    MvPolynomial (PolarizedSource κ) ℂ :=
  ∏ i, MvPolynomial.rename (blockEmbedding κ i)
    (_root_.RealRooted.polarization (κ i) (Polynomial.X ^ m.1 i))

private def stageBlockEmbedding
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : {i // i ∈ S}) :
    Fin (κ i) → SourcePolarizationStageVars κ S :=
  fun j => Sum.inl ⟨i, j⟩

private def stageRawEmbedding
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ) :
    {i : σ // i ∉ S} → SourcePolarizationStageVars κ S := Sum.inr

/-- Direct partial polarization of a degree-box basis monomial after exactly
the coordinates in `S` have been processed. -/
noncomputable def partialBlockwisePolarizationBasis
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    MvPolynomial (SourcePolarizationStageVars κ S) ℂ :=
  ∏ i, if hi : i ∈ S then
      MvPolynomial.rename (stageBlockEmbedding κ S ⟨i, hi⟩)
        (_root_.RealRooted.polarization (κ i) (Polynomial.X ^ m.1 i))
    else MvPolynomial.X (stageRawEmbedding κ S ⟨i, hi⟩) ^ m.1 i

/-- Direct partial source polarization as a linear map into the ambient
polynomial ring on the stage variables. -/
noncomputable def partialBlockwisePolarizationDegreeBox
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ) :
    MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ]
      MvPolynomial (SourcePolarizationStageVars κ S) ℂ :=
  (MvPolynomial.basisDegreeOfLE (R := ℂ) κ).constr ℂ fun m =>
    partialBlockwisePolarizationBasis κ S m

@[simp] theorem partialBlockwisePolarizationDegreeBox_basis
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    partialBlockwisePolarizationDegreeBox κ S
        (MvPolynomial.basisDegreeOfLE (R := ℂ) κ m) =
      partialBlockwisePolarizationBasis κ S m := by
  simp [partialBlockwisePolarizationDegreeBox]

/-- The empty partial stage is the original basis monomial, up to its
canonical variable equivalence. -/
theorem rename_partialBlockwisePolarizationBasis_empty
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    MvPolynomial.rename (sourcePolarizationStageEmptyEquiv κ)
        (partialBlockwisePolarizationBasis κ ∅ m) =
      MvPolynomial.monomial m.1 1 := by
  classical
  simp only [partialBlockwisePolarizationBasis, Finset.notMem_empty,
    ↓reduceDIte, map_prod]
  simp only [map_pow, MvPolynomial.rename_X]
  simp only [stageRawEmbedding, sourcePolarizationStageEmptyEquiv,
    Equiv.coe_fn_mk]
  change (∏ i, MvPolynomial.X i ^ m.1 i) = MvPolynomial.monomial m.1 1
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  symm
  apply Finset.prod_subset (Finset.subset_univ m.1.support)
  intro i _hi hiSupport
  simp [Finsupp.notMem_support_iff.mp hiSupport]

/-- The final partial stage is the direct full blockwise polarization, up to
its canonical variable equivalence. -/
theorem rename_partialBlockwisePolarizationBasis_univ
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    MvPolynomial.rename (sourcePolarizationStageUnivEquiv κ)
        (partialBlockwisePolarizationBasis κ Finset.univ m) =
      blockwisePolarizationBasis κ m := by
  classical
  unfold partialBlockwisePolarizationBasis blockwisePolarizationBasis
  simp only [Finset.mem_univ, ↓reduceDIte, map_prod, MvPolynomial.rename_rename]
  apply Finset.prod_congr rfl
  intro i _hi
  congr 1

private theorem fst_eq_of_mem_vars_blockwisePolarizationFactor
    {σ : Type*} (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) (i : σ)
    {a : PolarizedSource κ}
    (ha : a ∈ (MvPolynomial.rename (blockEmbedding κ i)
      (_root_.RealRooted.polarization (κ i) (Polynomial.X ^ m.1 i))).vars) :
    a.1 = i := by
  obtain ⟨j, _hj, hja⟩ := MvPolynomial.mem_vars_rename (blockEmbedding κ i)
    (_root_.RealRooted.polarization (κ i) (Polynomial.X ^ m.1 i)) ha
  rw [← hja]
  rfl

private theorem isMultiaffine_blockwisePolarizationBasis
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    MvPolynomial.IsMultiaffine (blockwisePolarizationBasis κ m) := by
  classical
  unfold blockwisePolarizationBasis
  induction (Finset.univ : Finset σ) using Finset.induction_on with
  | empty =>
      intro a
      simp [MvPolynomial.degreeOf_one]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      apply MvPolynomial.IsMultiaffine.mul_of_disjoint_vars
      · exact (_root_.RealRooted.isMultiaffine_polarization
          (κ i) (Polynomial.X ^ m.1 i)).rename (blockEmbedding_injective κ i)
      · exact ih
      · rw [Finset.disjoint_left]
        intro a ha_i ha_s
        have hai := fst_eq_of_mem_vars_blockwisePolarizationFactor κ m i ha_i
        have ha_union := MvPolynomial.vars_prod
          (fun j => MvPolynomial.rename (blockEmbedding κ j)
            (_root_.RealRooted.polarization (κ j) (Polynomial.X ^ m.1 j))) ha_s
        simp only [Finset.mem_biUnion] at ha_union
        obtain ⟨j, hjs, haj⟩ := ha_union
        have haj' := fst_eq_of_mem_vars_blockwisePolarizationFactor κ m j haj
        have hji : j = i := haj'.symm.trans hai
        exact hi (hji ▸ hjs)

/-- General source polarization from degree box `κ` to the all-ones box on
the blocks `Σ i, Fin (κ i)`. -/
noncomputable def blockwisePolarizationDegreeBoxGeneral
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ]
      MvPolynomial.degreeOfLE (PolarizedSource κ) ℂ (fun _ => 1) :=
  (MvPolynomial.basisDegreeOfLE (R := ℂ) κ).constr ℂ fun m =>
    ⟨blockwisePolarizationBasis κ m,
      (MvPolynomial.mem_degreeOfLE_iff_degreeOf _).2
        (isMultiaffine_blockwisePolarizationBasis κ m)⟩

@[simp] theorem blockwisePolarizationDegreeBoxGeneral_basis
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    blockwisePolarizationDegreeBoxGeneral κ
        (MvPolynomial.basisDegreeOfLE (R := ℂ) κ m) =
      ⟨blockwisePolarizationBasis κ m,
        (MvPolynomial.mem_degreeOfLE_iff_degreeOf _).2
          (isMultiaffine_blockwisePolarizationBasis κ m)⟩ := by
  simp [blockwisePolarizationDegreeBoxGeneral]

private theorem rename_blockwisePolarizationFactor
    {σ : Type*} (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) (i : σ) :
    MvPolynomial.rename Sigma.fst
        (MvPolynomial.rename (blockEmbedding κ i)
          (_root_.RealRooted.polarization (κ i) (Polynomial.X ^ m.1 i))) =
      MvPolynomial.X i ^ m.1 i := by
  rw [MvPolynomial.rename_rename]
  have hcomp : Sigma.fst ∘ blockEmbedding κ i = fun _ : Fin (κ i) => i := by
    funext j
    rfl
  rw [hcomp]
  have hdegree :
      (Polynomial.X ^ m.1 i : Polynomial ℂ).natDegree ≤ κ i := by
    simpa using m.2 i
  calc
    MvPolynomial.rename (fun _ : Fin (κ i) => i)
        (_root_.RealRooted.polarization (κ i) (Polynomial.X ^ m.1 i)) =
        MvPolynomial.rename (fun _ : Fin 1 => i)
          (MvPolynomial.rename (fun _ : Fin (κ i) => (0 : Fin 1))
            (_root_.RealRooted.polarization (κ i) (Polynomial.X ^ m.1 i))) := by
      rw [MvPolynomial.rename_rename]
      rfl
    _ = MvPolynomial.rename (fun _ : Fin 1 => i)
        ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
          (Polynomial.X ^ m.1 i)) := by
      rw [_root_.RealRooted.rename_polarization_const hdegree]
    _ = MvPolynomial.X i ^ m.1 i := by simp

theorem diagonalProjectionDegreeBoxGeneral_blockwisePolarization_basis
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    diagonalProjectionDegreeBoxGeneral κ
        (blockwisePolarizationDegreeBoxGeneral κ
          (MvPolynomial.basisDegreeOfLE (R := ℂ) κ m)) =
      MvPolynomial.basisDegreeOfLE κ m := by
  classical
  apply Subtype.ext
  rw [blockwisePolarizationDegreeBoxGeneral_basis,
    coe_diagonalProjectionDegreeBoxGeneral,
    MvPolynomial.coe_basisDegreeOfLE]
  simp only [blockwisePolarizationBasis, map_prod,
    rename_blockwisePolarizationFactor]
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  symm
  apply Finset.prod_subset (Finset.subset_univ m.1.support)
  intro i _hi hiSupport
  simp [Finsupp.notMem_support_iff.mp hiSupport]

/-- Blockwise polarization is a section of diagonal projection. -/
theorem diagonalProjectionDegreeBoxGeneral_blockwisePolarization
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (p : MvPolynomial.degreeOfLE σ ℂ κ) :
    diagonalProjectionDegreeBoxGeneral κ
        (blockwisePolarizationDegreeBoxGeneral κ p) = p := by
  have hmaps :
      (diagonalProjectionDegreeBoxGeneral κ).comp
          (blockwisePolarizationDegreeBoxGeneral κ) = LinearMap.id := by
    apply (MvPolynomial.basisDegreeOfLE (R := ℂ) κ).ext
    intro m
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    exact diagonalProjectionDegreeBoxGeneral_blockwisePolarization_basis κ m
  exact LinearMap.congr_fun hmaps p

/-- Lift an operator on degree box `κ` to its multiaffine polarized source by
precomposing with diagonal projection. -/
noncomputable def sourcePolarizedOperatorGeneral
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ) :
    MvPolynomial.degreeOfLE (PolarizedSource κ) ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial τ ℂ :=
  T.comp (diagonalProjectionDegreeBoxGeneral κ)

/-- Basis action of the general source-polarized operator. -/
theorem sourcePolarizedOperatorGeneral_basis
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ)
    (m : {m : PolarizedSource κ →₀ ℕ // ∀ i, m i ≤ 1}) :
    sourcePolarizedOperatorGeneral κ T
        (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ => 1) m) =
      T (MvPolynomial.basisDegreeOfLE κ
        (diagonalDegreeBoxIndexGeneral κ m)) := by
  unfold sourcePolarizedOperatorGeneral
  simp only [LinearMap.comp_apply]
  rw [diagonalProjectionDegreeBoxGeneral_basis_eq_basis]

/-- The source-polarized operator agrees with the original operator after
blockwise polarization. -/
theorem sourcePolarizedOperatorGeneral_blockwisePolarization
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ)
    (p : MvPolynomial.degreeOfLE σ ℂ κ) :
    sourcePolarizedOperatorGeneral κ T
        (blockwisePolarizationDegreeBoxGeneral κ p) = T p := by
  unfold sourcePolarizedOperatorGeneral
  rw [LinearMap.comp_apply,
    diagonalProjectionDegreeBoxGeneral_blockwisePolarization]

end


end RealRooted.BorceaBranden
