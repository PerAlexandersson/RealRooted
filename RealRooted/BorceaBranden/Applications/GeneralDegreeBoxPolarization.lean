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
    · have hj : j.1 ≠ i ∧ j.1 ∉ S := by simpa [Finset.mem_insert] using j.2
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

@[simp] theorem sourcePolarizationStageIsolateEquiv_processed
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S) (j : σ) (hj : j ∈ S) (k : Fin (κ j)) :
    sourcePolarizationStageIsolateEquiv κ S i hi
        (Sum.inl ⟨⟨j, hj⟩, k⟩) =
      Sum.inl (Sum.inl ⟨⟨j, hj⟩, k⟩) := rfl

@[simp] theorem sourcePolarizationStageIsolateEquiv_selected
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S) :
    sourcePolarizationStageIsolateEquiv κ S i hi (Sum.inr ⟨i, hi⟩) =
      Sum.inr default := by
  simp [sourcePolarizationStageIsolateEquiv]

@[simp] theorem sourcePolarizationStageIsolateEquiv_raw
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i j : σ) (hi : i ∉ S) (hj : j ∉ S) (hji : j ≠ i) :
    sourcePolarizationStageIsolateEquiv κ S i hi (Sum.inr ⟨j, hj⟩) =
      Sum.inl (Sum.inr ⟨j, hj, hji⟩) := by
  simp only [sourcePolarizationStageIsolateEquiv, Equiv.coe_fn_mk,
    dif_neg hji]
  congr 3

@[simp] theorem sourcePolarizationStageInstallEquiv_symm_processed
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S) (j : σ) (hj : j ∈ S) (k : Fin (κ j)) :
    (sourcePolarizationStageInstallEquiv κ S i hi).symm
        (Sum.inl (Sum.inl ⟨⟨j, hj⟩, k⟩)) =
      Sum.inl ⟨⟨j, Finset.mem_insert_of_mem hj⟩, k⟩ := rfl

@[simp] theorem sourcePolarizationStageInstallEquiv_symm_raw
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i j : σ) (hi : i ∉ S) (hj : j ∉ S) (hji : j ≠ i) :
    (sourcePolarizationStageInstallEquiv κ S i hi).symm
        (Sum.inl (Sum.inr ⟨j, hj, hji⟩)) =
      Sum.inr ⟨j, by simp [Finset.mem_insert, hj, hji]⟩ := rfl

@[simp] theorem sourcePolarizationStageInstallEquiv_symm_new
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S) (k : Fin (κ i)) :
    (sourcePolarizationStageInstallEquiv κ S i hi).symm (Sum.inr k) =
      Sum.inl ⟨⟨i, Finset.mem_insert_self i S⟩, k⟩ := rfl

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

/-- One source-polarization stage step as a complex-linear map. -/
noncomputable def sourcePolarizationStageStepLinearMap
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S) :
    MvPolynomial (SourcePolarizationStageVars κ S) ℂ →ₗ[ℂ]
      MvPolynomial (SourcePolarizationStageVars κ (insert i S)) ℂ :=
  (MvPolynomial.renameEquiv ℂ
      (sourcePolarizationStageInstallEquiv κ S i hi).symm).toLinearMap.comp
    ((MvPolynomial.sourceBlockPolarizationLinearMap (κ i)).comp
      (MvPolynomial.renameEquiv ℂ
        (sourcePolarizationStageIsolateEquiv κ S i hi)).toLinearMap)

@[simp] theorem sourcePolarizationStageStepLinearMap_apply
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (hi : i ∉ S)
    (P : MvPolynomial (SourcePolarizationStageVars κ S) ℂ) :
    sourcePolarizationStageStepLinearMap κ S i hi P =
      sourcePolarizationStageStep κ S i hi P := rfl

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

/-- Coordinatewise complementation in a finite degree box. -/
def boxComplementIndex {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i}) :
    {m : σ →₀ ℕ // ∀ i, m i ≤ κ i} :=
  (MvPolynomial.degreeOfLEIndexEquiv κ).symm fun i =>
    ⟨κ i - r.1 i, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

@[simp] theorem boxComplementIndex_apply {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i}) (i : σ) :
    (boxComplementIndex κ r).1 i = κ i - r.1 i := by
  simp [boxComplementIndex, MvPolynomial.degreeOfLEIndexEquiv]

/-- Coordinatewise complementation is an involution on bounded exponents. -/
def boxComplementEquiv {σ : Type*} [Fintype σ] (κ : σ → ℕ) :
    {r : σ →₀ ℕ // ∀ i, r i ≤ κ i} ≃
      {m : σ →₀ ℕ // ∀ i, m i ≤ κ i} where
  toFun := boxComplementIndex κ
  invFun := boxComplementIndex κ
  left_inv r := by
    apply Subtype.ext
    ext i
    simp [Nat.sub_sub_self (r.2 i)]
  right_inv r := by
    apply Subtype.ext
    ext i
    simp [Nat.sub_sub_self (r.2 i)]

@[simp] theorem boxComplementIndex_involution {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i}) :
    boxComplementIndex κ (boxComplementIndex κ r) = r := by
  exact (boxComplementEquiv κ).left_inv r

/-- Complementing a bounded exponent preserves its degree-box binomial
coefficient. -/
theorem boxChoose_boxComplementIndex {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i}) :
    MvPolynomial.boxChoose κ (boxComplementIndex κ r).1 =
      MvPolynomial.boxChoose κ r.1 := by
  classical
  unfold MvPolynomial.boxChoose
  apply Finset.prod_congr rfl
  intro i _hi
  rw [boxComplementIndex_apply, Nat.choose_symm (r.2 i)]

private theorem rightComplementMonomial_eq_rename_boxComplement
    {σ τ R : Type*} [CommSemiring R] [Fintype σ]
    (κ : σ → ℕ) (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    MvPolynomial.rightComplementMonomial (R := R) (τ := τ) κ m.1 =
      MvPolynomial.rename Sum.inr
        (MvPolynomial.monomial (boxComplementIndex κ m).1 1) := by
  rw [MvPolynomial.rightComplementMonomial_eq_prod]
  calc
    (∏ i, MvPolynomial.X (R := R) (Sum.inr i) ^ (κ i - m.1 i)) =
        MvPolynomial.rename Sum.inr
          (∏ i, MvPolynomial.X (R := R) i ^ (κ i - m.1 i)) := by simp
    _ = MvPolynomial.rename Sum.inr
          (MvPolynomial.monomial (boxComplementIndex κ m).1 1) := by
      congr 1
      calc
        (∏ i, MvPolynomial.X (R := R) i ^ (κ i - m.1 i)) =
            MvPolynomial.monomial
              (Finsupp.indicator Finset.univ
                (fun i _ => κ i - m.1 i)) 1 := by
          simpa using MvPolynomial.prod_X_pow (R := R)
            (fun i => κ i - m.1 i) Finset.univ
        _ = MvPolynomial.monomial (boxComplementIndex κ m).1 1 := by
          apply congrArg (fun d => MvPolynomial.monomial d (1 : R))
          ext i
          simp [Finsupp.indicator]

private theorem rename_inl_monomial_mul_rename_inr_monomial
    {σ τ R : Type*} [CommSemiring R]
    (u : τ →₀ ℕ) (a : σ →₀ ℕ) (c : R) :
    MvPolynomial.rename Sum.inl (MvPolynomial.monomial u c) *
        MvPolynomial.rename Sum.inr (MvPolynomial.monomial a 1) =
      MvPolynomial.monomial (u.sumElim a) c := by
  classical
  rw [MvPolynomial.rename_monomial, MvPolynomial.rename_monomial,
    MvPolynomial.monomial_mul]
  have hsum :
      Finsupp.mapDomain (Sum.inl : τ → τ ⊕ σ) u +
          Finsupp.mapDomain (Sum.inr : σ → τ ⊕ σ) a =
        u.sumElim a :=
    (Finsupp.sumElim_eq_add u a).symm
  rw [hsum, mul_one]

private theorem sourceCoefficientGeneral_rename_mul_monomial
    {σ τ : Type*} [DecidableEq σ]
    (q : MvPolynomial τ ℂ) (a r : σ →₀ ℕ) :
    sourceCoefficientGeneral
        (MvPolynomial.rename Sum.inl q *
          MvPolynomial.rename Sum.inr (MvPolynomial.monomial a 1)) r =
      if r = a then q else 0 := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, add_mul, sourceCoefficientGeneral_add, hp, hq]
      split <;> simp_all
  | monomial u c =>
      rw [rename_inl_monomial_mul_rename_inr_monomial,
        sourceCoefficientGeneral_monomial_sumElim]

private theorem sourceCoefficientGeneral_symbolTerm
    {σ τ : Type*} [Fintype σ]
    (κ : σ → ℕ) (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i})
    (q : MvPolynomial τ ℂ) (c : ℂ) (r : σ →₀ ℕ) :
    sourceCoefficientGeneral
        (MvPolynomial.C c * MvPolynomial.rename Sum.inl q *
          MvPolynomial.rightComplementMonomial κ m.1) r =
      if r = (boxComplementIndex κ m).1 then MvPolynomial.C c * q else 0 := by
  classical
  rw [rightComplementMonomial_eq_rename_boxComplement]
  have hleft :
      (MvPolynomial.C c : MvPolynomial (τ ⊕ σ) ℂ) *
          MvPolynomial.rename (Sum.inl : τ → τ ⊕ σ) q =
        MvPolynomial.rename (Sum.inl : τ → τ ⊕ σ)
          ((MvPolynomial.C c : MvPolynomial τ ℂ) * q) := by
    rw [map_mul, MvPolynomial.rename_C]
  rw [hleft, sourceCoefficientGeneral_rename_mul_monomial]
  by_cases h : r = (boxComplementIndex κ m).1 <;> simp [h]

/-- Extracting a source coefficient commutes with a finite sum. -/
theorem sourceCoefficientGeneral_sum {σ τ ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (τ ⊕ σ) ℂ) (r : σ →₀ ℕ) :
    sourceCoefficientGeneral (∑ i ∈ s, f i) r =
      ∑ i ∈ s, sourceCoefficientGeneral (f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sourceCoefficientGeneral]
  | @insert a s ha ih => simp [ha, ih]

/-- The unpolarized source coefficient of a finite algebraic symbol is the operator
image at the complementary exponent, with the expected binomial factor. -/
theorem sourceCoefficientGeneral_algebraicSymbol
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ)
    (r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i}) :
    sourceCoefficientGeneral (MvPolynomial.algebraicSymbol κ T) r.1 =
      MvPolynomial.C (MvPolynomial.boxChoose κ r.1 : ℂ) *
        T (MvPolynomial.basisDegreeOfLE κ (boxComplementIndex κ r)) := by
  classical
  rw [MvPolynomial.algebraicSymbol_eq_sum,
    show (∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
        MvPolynomial.C (MvPolynomial.boxChoose κ m.1 : ℂ) *
          MvPolynomial.rename Sum.inl
              (T (MvPolynomial.basisDegreeOfLE κ m)) *
            MvPolynomial.rightComplementMonomial κ m.1) =
      ∑ m ∈ Finset.univ,
        MvPolynomial.C (MvPolynomial.boxChoose κ m.1 : ℂ) *
          MvPolynomial.rename Sum.inl
              (T (MvPolynomial.basisDegreeOfLE κ m)) *
            MvPolynomial.rightComplementMonomial κ m.1 by rfl,
    sourceCoefficientGeneral_sum]
  rw [Finset.sum_eq_single (boxComplementIndex κ r)]
  · rw [sourceCoefficientGeneral_symbolTerm]
    simp only [boxComplementIndex_involution, if_pos]
    rw [boxChoose_boxComplementIndex]
  · intro m _hm hm
    rw [sourceCoefficientGeneral_symbolTerm]
    have hne : r.1 ≠ (boxComplementIndex κ m).1 := by
      intro h
      apply hm
      have hr : r = boxComplementIndex κ m := Subtype.ext h
      simpa using (congrArg (boxComplementIndex κ) hr).symm
    simp [hne]
  · simp

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

/-- Source polarization of a finite algebraic symbol cancels its binomial
factor and replaces each complementary source monomial by the corresponding
block elementary-symmetric polynomial. -/
theorem sourceBlockwisePolarizationGeneral_algebraicSymbol_eq_sum
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ) :
    sourceBlockwisePolarizationGeneral κ
        (MvPolynomial.algebraicSymbol κ T) =
      ∑ r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i},
        MvPolynomial.rename Sum.inl
            (T (MvPolynomial.basisDegreeOfLE κ
              (boxComplementIndex κ r))) *
          MvPolynomial.rename Sum.inr
            (blockElementarySymmetric κ r.1) := by
  classical
  unfold sourceBlockwisePolarizationGeneral
  apply Fintype.sum_congr
  intro r
  rw [sourceCoefficientGeneral_algebraicSymbol]
  have hchoose : MvPolynomial.boxChoose κ r.1 ≠ 0 := by
    unfold MvPolynomial.boxChoose
    exact Finset.prod_ne_zero_iff.mpr fun i _hi =>
      (Nat.choose_pos (r.2 i)).ne'
  rw [map_mul]
  simp only [MvPolynomial.rename_C]
  rw [← mul_assoc, ← MvPolynomial.C_mul]
  simp [hchoose]

/-- The source-polarized unpolarized symbol in the common normal form indexed
by the original source exponent. -/
theorem sourceBlockwisePolarizationGeneral_algebraicSymbol_normalForm
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ) :
    sourceBlockwisePolarizationGeneral κ
        (MvPolynomial.algebraicSymbol κ T) =
      ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
        MvPolynomial.rename Sum.inl
            (T (MvPolynomial.basisDegreeOfLE κ m)) *
          MvPolynomial.rename Sum.inr
            (blockElementarySymmetric κ (boxComplementIndex κ m).1) := by
  rw [sourceBlockwisePolarizationGeneral_algebraicSymbol_eq_sum]
  apply Fintype.sum_equiv (boxComplementEquiv κ)
  intro r
  change
    MvPolynomial.rename Sum.inl
          (T (MvPolynomial.basisDegreeOfLE κ (boxComplementIndex κ r))) *
        MvPolynomial.rename Sum.inr (blockElementarySymmetric κ r.1) =
      MvPolynomial.rename Sum.inl
          (T (MvPolynomial.basisDegreeOfLE κ (boxComplementIndex κ r))) *
        MvPolynomial.rename Sum.inr
          (blockElementarySymmetric κ
            (boxComplementIndex κ (boxComplementIndex κ r)).1)
  rw [boxComplementIndex_involution]

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

private theorem coeff_specializeLeft_eq_eval_sourceCoefficientGeneral
    {σ τ : Type*} (P : MvPolynomial (τ ⊕ σ) ℂ)
    (x : τ → ℂ) (r : σ →₀ ℕ) :
    MvPolynomial.coeff r (_root_.RealRooted.specializeLeft x P) =
      MvPolynomial.eval x (sourceCoefficientGeneral P r) := by
  have hspecial :
      _root_.RealRooted.specializeLeft x P =
        MvPolynomial.map (MvPolynomial.eval x)
          (MvPolynomial.sumAlgEquiv ℂ σ τ
            (MvPolynomial.rename (Equiv.sumComm τ σ) P)) := by
    unfold _root_.RealRooted.specializeLeft
    change
      (MvPolynomial.aeval
          (Sum.elim (MvPolynomial.C ∘ x) MvPolynomial.X)) P =
        ((MvPolynomial.mapAlgHom (MvPolynomial.aeval x)).comp
          ((MvPolynomial.sumAlgEquiv ℂ σ τ).toAlgHom.comp
            (MvPolynomial.rename (Equiv.sumComm τ σ)))) P
    congr 1
    apply MvPolynomial.algHom_ext
    rintro (i | i) <;>
      simp [Function.comp_def, Equiv.sumComm_apply]
  rw [hspecial, MvPolynomial.coeff_map]
  rfl

private theorem specializeLeft_mem_sourceDegreeBox
    {σ τ : Type*} (κ : σ → ℕ)
    (P : MvPolynomial (τ ⊕ σ) ℂ)
    (hdeg : ∀ i, P.degreeOf (Sum.inr i) ≤ κ i)
    (x : τ → ℂ) :
    _root_.RealRooted.specializeLeft x P ∈
      MvPolynomial.degreeOfLE σ ℂ κ := by
  rw [MvPolynomial.mem_degreeOfLE]
  intro r hr i
  have hcoeff : MvPolynomial.eval x (sourceCoefficientGeneral P r) ≠ 0 := by
    rw [← coeff_specializeLeft_eq_eval_sourceCoefficientGeneral]
    exact MvPolynomial.mem_support_iff.mp hr
  have hsource : sourceCoefficientGeneral P r ≠ 0 := by
    intro hzero
    simp [hzero] at hcoeff
  obtain ⟨u, hu⟩ := MvPolynomial.exists_coeff_ne_zero hsource
  have horig : MvPolynomial.coeff (u.sumElim r) P ≠ 0 := by
    rw [← coeff_sourceCoefficientGeneral]
    exact hu
  have hmonomial : (u.sumElim r) (Sum.inr i) ≤ P.degreeOf (Sum.inr i) :=
    MvPolynomial.monomial_le_degreeOf (Sum.inr i)
      (MvPolynomial.mem_support_iff.mpr horig)
  exact hmonomial.trans (hdeg i)

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

/-- Multiaffine exponent vectors on the fully polarized source. -/
abbrev ZeroOneExponent {σ : Type*} [Fintype σ] (κ : σ → ℕ) :=
  {b : PolarizedSource κ →₀ ℕ // ∀ x, b x ≤ 1}

/-- A choice of one finite support inside each polarized source block. -/
abbrev BlockSupports {σ : Type*} [Fintype σ] (κ : σ → ℕ) :=
  ∀ i, Finset (Fin (κ i))

/-- Read a zero-one exponent as its support in each source block. -/
def exponentBlockSupports {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (b : ZeroOneExponent κ) : BlockSupports κ :=
  fun i => Finset.univ.filter fun j => b.1 ⟨i, j⟩ = 1

/-- Install a family of block supports as a zero-one exponent. -/
noncomputable def exponentOfBlockSupports {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (s : BlockSupports κ) : ZeroOneExponent κ :=
  ⟨Finsupp.equivFunOnFinite.symm fun x => if x.2 ∈ s x.1 then 1 else 0,
    fun x => by
      change (if x.2 ∈ s x.1 then 1 else 0) ≤ 1
      split_ifs <;> simp⟩

@[simp] theorem exponentBlockSupports_exponentOfBlockSupports
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (s : BlockSupports κ) :
    exponentBlockSupports κ (exponentOfBlockSupports κ s) = s := by
  funext i
  ext j
  simp [exponentBlockSupports, exponentOfBlockSupports]

@[simp] theorem exponentOfBlockSupports_exponentBlockSupports
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (b : ZeroOneExponent κ) :
    exponentOfBlockSupports κ (exponentBlockSupports κ b) = b := by
  apply Subtype.ext
  apply Finsupp.ext
  intro x
  simp only [exponentOfBlockSupports, exponentBlockSupports,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hx : b.1 x = 1
  · simp [hx]
  · have hle := b.2 x
    have hx0 : b.1 x = 0 := by lia
    simp [hx0]

/-- Zero-one exponents are equivalently independent choices of a support in
each source block. -/
noncomputable def zeroOneExponentEquivBlockSupports
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) :
    ZeroOneExponent κ ≃ BlockSupports κ where
  toFun := exponentBlockSupports κ
  invFun := exponentOfBlockSupports κ
  left_inv := exponentOfBlockSupports_exponentBlockSupports κ
  right_inv := exponentBlockSupports_exponentOfBlockSupports κ

/-- Aggregating a zero-one exponent across a block counts its block support. -/
theorem diagonalDegreeBoxIndexGeneral_apply_eq_card_blockSupport
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (b : ZeroOneExponent κ) (i : σ) :
    (diagonalDegreeBoxIndexGeneral κ b).1 i =
      (exponentBlockSupports κ b i).card := by
  change (b.1.mapDomain Sigma.fst) i = _
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  rw [Finsupp.sum_fintype _ _ (by intro x; simp)]
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [Finsupp.single_eq_same]
    change (∑ j : Fin (κ i), b.1 ⟨i, j⟩) =
      (Finset.univ.filter fun j => b.1 ⟨i, j⟩ = 1).card
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hbj : b.1 ⟨i, j⟩ = 1
    · simp [hbj]
    · have hle := b.2 ⟨i, j⟩
      have hb0 : b.1 ⟨i, j⟩ = 0 := by lia
      simp [hb0]
  · intro j _hj hji
    simp [hji]
  · simp

/-- The fiber of diagonal aggregation over a bounded source exponent. -/
abbrev DiagonalAggregateFiber {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :=
  {b : ZeroOneExponent κ // diagonalDegreeBoxIndexGeneral κ b = m}

/-- Independent block supports whose cardinalities are prescribed by `m`. -/
abbrev BlockSupportsOfCard {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :=
  ∀ i, {s : Finset (Fin (κ i)) // s.card = m.1 i}

noncomputable instance instFintypeBlockSupportsOfCard
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    Fintype (BlockSupportsOfCard κ m) :=
  @Pi.instFintype σ
    (fun i => {s : Finset (Fin (κ i)) // s.card = m.1 i})
    (Classical.decEq σ) _ (fun _ => inferInstance)

/-- A multiaffine aggregation fiber is the dependent product of the
fixed-cardinality support choices in each block. -/
noncomputable def diagonalAggregateFiberEquivBlockSupportsOfCard
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    DiagonalAggregateFiber κ m ≃ BlockSupportsOfCard κ m where
  toFun b i :=
    ⟨exponentBlockSupports κ b.1 i, by
      rw [← diagonalDegreeBoxIndexGeneral_apply_eq_card_blockSupport]
      exact congrArg (fun r => r.1 i) b.2⟩
  invFun s :=
    ⟨exponentOfBlockSupports κ fun i => (s i).1, by
      apply Subtype.ext
      ext i
      rw [diagonalDegreeBoxIndexGeneral_apply_eq_card_blockSupport,
        exponentBlockSupports_exponentOfBlockSupports]
      exact (s i).2⟩
  left_inv b := by
    apply Subtype.ext
    exact exponentOfBlockSupports_exponentBlockSupports κ b.1
  right_inv s := by
    funext i
    apply Subtype.ext
    exact congrFun
      (exponentBlockSupports_exponentOfBlockSupports κ fun i => (s i).1) i

noncomputable instance instFintypeDiagonalAggregateFiber
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    Fintype (DiagonalAggregateFiber κ m) :=
  Fintype.ofEquiv (BlockSupportsOfCard κ m)
    (diagonalAggregateFiberEquivBlockSupportsOfCard κ m).symm

/-- Complement each fixed-cardinality support inside its polarized block. -/
noncomputable def blockSupportsOfCardComplementEquiv
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    BlockSupportsOfCard κ m ≃
      BlockSupportsOfCard κ (boxComplementIndex κ m) where
  toFun s i :=
    ⟨(s i).1ᶜ, by
      rw [Finset.card_compl, (s i).2, boxComplementIndex_apply]
      simp⟩
  invFun s i :=
    ⟨(s i).1ᶜ, by
      rw [Finset.card_compl, (s i).2, boxComplementIndex_apply,
        Fintype.card_fin, Nat.sub_sub_self (m.2 i)]⟩
  left_inv s := by
    funext i
    apply Subtype.ext
    simp
  right_inv s := by
    funext i
    apply Subtype.ext
    simp

/-- Aggregation fibers can equivalently be indexed by complementary supports,
whose block cardinalities are `κ - m`. -/
noncomputable def diagonalAggregateFiberEquivComplementBlockSupports
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    DiagonalAggregateFiber κ m ≃
      BlockSupportsOfCard κ (boxComplementIndex κ m) :=
  (diagonalAggregateFiberEquivBlockSupportsOfCard κ m).trans
    (blockSupportsOfCardComplementEquiv κ m)

/-- The monomial supported on the complement of a multiaffine exponent. -/
noncomputable def complementSupportMonomial
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (b : ZeroOneExponent κ) : MvPolynomial (PolarizedSource κ) ℂ :=
  ∏ i, ∏ j ∈ (exponentBlockSupports κ b i)ᶜ, MvPolynomial.X ⟨i, j⟩

private theorem prod_blockSupport_compl_eq
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (b : ZeroOneExponent κ) (i : σ) :
    (∏ j ∈ (exponentBlockSupports κ b i)ᶜ,
        MvPolynomial.X (R := ℂ) (⟨i, j⟩ : PolarizedSource κ)) =
      ∏ j : Fin (κ i),
        if b.1 ⟨i, j⟩ = 0 then
          MvPolynomial.X (R := ℂ) (⟨i, j⟩ : PolarizedSource κ) else 1 := by
  classical
  rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_eq_filter,
    Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _hj
  by_cases hbj : b.1 ⟨i, j⟩ = 1
  · simp [exponentBlockSupports, hbj]
  · have hle := b.2 ⟨i, j⟩
    have hb0 : b.1 ⟨i, j⟩ = 0 := by lia
    simp only [exponentBlockSupports, Finset.mem_filter, Finset.mem_univ,
      true_and, hb0, zero_ne_one, not_false_eq_true, if_true]

/-- The blockwise complement monomial is the product of a variable exactly at
the zero entries of the exponent. -/
theorem complementSupportMonomial_eq_fintype_prod_ite
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (b : ZeroOneExponent κ) :
    complementSupportMonomial κ b =
      ∏ x : PolarizedSource κ,
        if b.1 x = 0 then MvPolynomial.X x else 1 := by
  classical
  unfold complementSupportMonomial
  simp_rw [prod_blockSupport_compl_eq]
  exact (Fintype.prod_sigma fun x : PolarizedSource κ =>
    if b.1 x = 0 then MvPolynomial.X x else 1).symm

/-- Expand the product of block elementary-symmetric polynomials as the sum
over independent fixed-cardinality supports. -/
theorem blockElementarySymmetric_eq_sum_blockSupportsOfCard
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i}) :
    blockElementarySymmetric κ r.1 =
      ∑ s : BlockSupportsOfCard κ r,
        ∏ i, ∏ j ∈ (s i).1, MvPolynomial.X ⟨i, j⟩ := by
  classical
  unfold blockElementarySymmetric
  simp_rw [MvPolynomial.esymm_eq_sum_subtype, map_sum, map_prod,
    MvPolynomial.rename_X]
  rw [Fintype.prod_sum]

/-- The complement-support fiber sum is the product of the corresponding
block elementary-symmetric polynomials. -/
theorem sum_complementSupportMonomial_diagonalAggregateFiber
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    (∑ b : DiagonalAggregateFiber κ m,
        complementSupportMonomial κ b.1) =
      blockElementarySymmetric κ (boxComplementIndex κ m).1 := by
  rw [blockElementarySymmetric_eq_sum_blockSupportsOfCard]
  apply Fintype.sum_equiv
    (diagonalAggregateFiberEquivComplementBlockSupports κ m)
  intro b
  rfl

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

private def stageRestBlockEmbedding
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) (j : {j // j ∈ S}) :
    Fin (κ j) → SourcePolarizationStageRest κ S i :=
  fun k => Sum.inl ⟨j, k⟩

private def stageRestRawEmbedding
    {σ : Type*} [DecidableEq σ] (κ : σ → ℕ) (S : Finset σ)
    (i : σ) : {j : σ // j ∉ S ∧ j ≠ i} →
      SourcePolarizationStageRest κ S i := Sum.inr

/-- The factors of a partial basis other than one selected raw coordinate,
expressed on the isolated stage-rest variables. -/
private noncomputable def sourcePolarizationStageRestBasis
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ) (i : σ)
    (m : {m : σ →₀ ℕ // ∀ j, m j ≤ κ j}) :
    MvPolynomial (SourcePolarizationStageRest κ S i) ℂ :=
  ∏ j, if hji : j = i then 1 else if hj : j ∈ S then
      MvPolynomial.rename (stageRestBlockEmbedding κ S i ⟨j, hj⟩)
        (_root_.RealRooted.polarization (κ j) (Polynomial.X ^ m.1 j))
    else MvPolynomial.X (stageRestRawEmbedding κ S i ⟨j, hj, hji⟩) ^ m.1 j

private theorem rename_stageIsolate_partialBlockwisePolarizationBasis
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ) (i : σ) (hi : i ∉ S)
    (m : {m : σ →₀ ℕ // ∀ j, m j ≤ κ j}) :
    MvPolynomial.rename (sourcePolarizationStageIsolateEquiv κ S i hi)
        (partialBlockwisePolarizationBasis κ S m) =
      MvPolynomial.rename Sum.inl
          (sourcePolarizationStageRestBasis κ S i m) *
        MvPolynomial.X (Sum.inr default) ^ m.1 i := by
  classical
  unfold partialBlockwisePolarizationBasis sourcePolarizationStageRestBasis
  simp only [map_prod]
  rw [Fintype.prod_eq_prod_compl_mul i]
  congr 1
  · rw [Fintype.prod_eq_prod_compl_mul i]
    simp only [ne_eq, ↓reduceDIte, map_one, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp only [hji, ↓reduceDIte]
    by_cases hjS : j ∈ S
    · simp only [hjS, ↓reduceDIte, MvPolynomial.rename_rename]
      congr 1
    · simp only [hjS, ↓reduceDIte, map_pow, MvPolynomial.rename_X]
      simp [stageRawEmbedding, stageRestRawEmbedding,
        sourcePolarizationStageIsolateEquiv, hji]
  · simp only [hi, ↓reduceDIte, map_pow, MvPolynomial.rename_X]
    simp [stageRawEmbedding, sourcePolarizationStageIsolateEquiv]

private theorem rename_stageInstall_sourcePolarizationStageRestBasis
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ) (i : σ) (hi : i ∉ S)
    (m : {m : σ →₀ ℕ // ∀ j, m j ≤ κ j}) :
    MvPolynomial.rename (sourcePolarizationStageInstallEquiv κ S i hi).symm
        (MvPolynomial.rename Sum.inl
            (sourcePolarizationStageRestBasis κ S i m) *
          MvPolynomial.rename Sum.inr
            (_root_.RealRooted.polarization (κ i) (Polynomial.X ^ m.1 i))) =
      partialBlockwisePolarizationBasis κ (insert i S) m := by
  classical
  unfold sourcePolarizationStageRestBasis partialBlockwisePolarizationBasis
  simp only [map_mul, MvPolynomial.rename_rename, map_prod]
  rw [Fintype.prod_eq_prod_compl_mul i]
  simp only [↓reduceDIte, map_one, mul_one]
  rw [Fintype.prod_eq_prod_compl_mul i]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp only [hji, ↓reduceDIte]
    by_cases hjS : j ∈ S
    · simp only [hjS, Finset.mem_insert, or_true, ↓reduceDIte,
        MvPolynomial.rename_rename]
      congr 1
    · have hjInsert : j ∉ insert i S := by simp [Finset.mem_insert, hji, hjS]
      simp only [hjS, hjInsert, ↓reduceDIte, map_pow, MvPolynomial.rename_X]
      simp [stageRestRawEmbedding, stageRawEmbedding,
        sourcePolarizationStageInstallEquiv]
  · simp only [Finset.mem_insert_self, ↓reduceDIte]
    congr 1

/-- One staged step sends the direct partial basis at `S` to the direct
partial basis at `insert i S`. -/
theorem sourcePolarizationStageStep_partialBlockwisePolarizationBasis
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ) (i : σ) (hi : i ∉ S)
    (m : {m : σ →₀ ℕ // ∀ j, m j ≤ κ j}) :
    sourcePolarizationStageStep κ S i hi
        (partialBlockwisePolarizationBasis κ S m) =
      partialBlockwisePolarizationBasis κ (insert i S) m := by
  unfold sourcePolarizationStageStep
  rw [rename_stageIsolate_partialBlockwisePolarizationBasis]
  rw [MvPolynomial.sourceBlockPolarization_rename_mul_X_pow
    (κ i) (m.1 i) (sourcePolarizationStageRestBasis κ S i m) (m.2 i)]
  exact rename_stageInstall_sourcePolarizationStageRestBasis κ S i hi m

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

/-- The direct partial polarization maps satisfy the same insert recurrence
as the staged one-coordinate construction. -/
theorem sourcePolarizationStageStep_partialBlockwisePolarizationDegreeBox
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (S : Finset σ) (i : σ) (hi : i ∉ S) :
    (sourcePolarizationStageStepLinearMap κ S i hi).comp
        (partialBlockwisePolarizationDegreeBox κ S) =
      partialBlockwisePolarizationDegreeBox κ (insert i S) := by
  apply (MvPolynomial.basisDegreeOfLE (R := ℂ) κ).ext
  intro m
  simp only [LinearMap.comp_apply,
    partialBlockwisePolarizationDegreeBox_basis,
    sourcePolarizationStageStepLinearMap_apply]
  exact sourcePolarizationStageStep_partialBlockwisePolarizationBasis
    κ S i hi m

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

/-- The empty partial stage reconstructs the original degree-box
polynomial. -/
theorem rename_partialBlockwisePolarizationDegreeBox_empty
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (p : MvPolynomial.degreeOfLE σ ℂ κ) :
    MvPolynomial.rename (sourcePolarizationStageEmptyEquiv κ)
        (partialBlockwisePolarizationDegreeBox κ ∅ p) = p.1 := by
  have hmaps :
      (MvPolynomial.renameEquiv ℂ
          (sourcePolarizationStageEmptyEquiv κ)).toLinearMap.comp
          (partialBlockwisePolarizationDegreeBox κ ∅) =
        Submodule.subtype (MvPolynomial.degreeOfLE σ ℂ κ) := by
    apply (MvPolynomial.basisDegreeOfLE (R := ℂ) κ).ext
    intro m
    simp only [LinearMap.comp_apply,
      partialBlockwisePolarizationDegreeBox_basis]
    simpa using rename_partialBlockwisePolarizationBasis_empty κ m
  exact LinearMap.congr_fun hmaps p

/-- Every unprocessed coordinate of a direct partial polarization retains its
original degree cap. -/
theorem degreeOf_partialBlockwisePolarizationDegreeBox_raw_le
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (p : MvPolynomial.degreeOfLE σ ℂ κ)
    (S : Finset σ) (j : σ) (hj : j ∉ S) :
    (partialBlockwisePolarizationDegreeBox κ S p).degreeOf
        (Sum.inr ⟨j, hj⟩) ≤ κ j := by
  induction S using Finset.induction_on with
  | empty =>
      have hrename := MvPolynomial.degreeOf_rename_of_injective
        (sourcePolarizationStageEmptyEquiv κ).injective
        (Sum.inr ⟨j, hj⟩)
        (p := partialBlockwisePolarizationDegreeBox κ ∅ p)
      have hmap : sourcePolarizationStageEmptyEquiv κ (Sum.inr ⟨j, hj⟩) = j := rfl
      rw [hmap, rename_partialBlockwisePolarizationDegreeBox_empty] at hrename
      exact hrename.symm.trans_le
        ((MvPolynomial.mem_degreeOfLE_iff_degreeOf p.1).mp p.2 j)
  | @insert i S hi ih =>
      have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
      have hstep := LinearMap.congr_fun
        (sourcePolarizationStageStep_partialBlockwisePolarizationDegreeBox
          κ S i hi) p
      rw [LinearMap.comp_apply] at hstep
      rw [← hstep]
      exact (degreeOf_sourcePolarizationStageStep_raw_le κ S i hi
        (partialBlockwisePolarizationDegreeBox κ S p) j hj).trans
          (ih hjS)

/-- Every direct partial source polarization of a stable degree-box
polynomial is stable. -/
theorem mvUpperHalfPlaneStable_partialBlockwisePolarizationDegreeBox
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (p : MvPolynomial.degreeOfLE σ ℂ κ)
    (hp : MvUpperHalfPlaneStable p.1) (S : Finset σ) :
    MvUpperHalfPlaneStable (partialBlockwisePolarizationDegreeBox κ S p) := by
  induction S using Finset.induction_on with
  | empty =>
      have hrename := rename_partialBlockwisePolarizationDegreeBox_empty κ p
      have heq :
          MvPolynomial.rename (sourcePolarizationStageEmptyEquiv κ).symm p.1 =
            partialBlockwisePolarizationDegreeBox κ ∅ p := by
        rw [← hrename, MvPolynomial.rename_rename,
          (sourcePolarizationStageEmptyEquiv κ).symm_comp_self,
          MvPolynomial.rename_id_apply]
      rw [← heq]
      exact hp.rename
  | @insert i S hi ih =>
      have hstep := LinearMap.congr_fun
        (sourcePolarizationStageStep_partialBlockwisePolarizationDegreeBox
          κ S i hi) p
      rw [LinearMap.comp_apply] at hstep
      rw [← hstep]
      exact mvUpperHalfPlaneStable_sourcePolarizationStageStep κ S i hi
        (partialBlockwisePolarizationDegreeBox κ S p)
        (degreeOf_partialBlockwisePolarizationDegreeBox_raw_le κ p S i hi) ih

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

/-- The final partial stage is the direct full blockwise polarization. -/
theorem rename_partialBlockwisePolarizationDegreeBox_univ
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (κ : σ → ℕ) (p : MvPolynomial.degreeOfLE σ ℂ κ) :
    MvPolynomial.rename (sourcePolarizationStageUnivEquiv κ)
        (partialBlockwisePolarizationDegreeBox κ Finset.univ p) =
      (blockwisePolarizationDegreeBoxGeneral κ p).1 := by
  have hmaps :
      (MvPolynomial.renameEquiv ℂ
          (sourcePolarizationStageUnivEquiv κ)).toLinearMap.comp
          (partialBlockwisePolarizationDegreeBox κ Finset.univ) =
        (Submodule.subtype
          (MvPolynomial.degreeOfLE (PolarizedSource κ) ℂ (fun _ => 1))).comp
            (blockwisePolarizationDegreeBoxGeneral κ) := by
    apply (MvPolynomial.basisDegreeOfLE (R := ℂ) κ).ext
    intro m
    simp only [LinearMap.comp_apply,
      partialBlockwisePolarizationDegreeBox_basis,
      blockwisePolarizationDegreeBoxGeneral_basis]
    exact rename_partialBlockwisePolarizationBasis_univ κ m
  exact LinearMap.congr_fun hmaps p

/-- General blockwise polarization preserves upper-half-plane stability. -/
theorem mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (p : MvPolynomial.degreeOfLE σ ℂ κ)
    (hp : MvUpperHalfPlaneStable p.1) :
    MvUpperHalfPlaneStable (blockwisePolarizationDegreeBoxGeneral κ p).1 := by
  classical
  have hpartial :=
    mvUpperHalfPlaneStable_partialBlockwisePolarizationDegreeBox
      κ p hp Finset.univ
  have hrename := hpartial.rename
    (f := sourcePolarizationStageUnivEquiv κ)
  rw [rename_partialBlockwisePolarizationDegreeBox_univ] at hrename
  exact hrename

private theorem blockwisePolarizationBasis_eq_normalized
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i}) :
    blockwisePolarizationBasis κ r =
      MvPolynomial.C ((MvPolynomial.boxChoose κ r.1 : ℂ)⁻¹) *
        blockElementarySymmetric κ r.1 := by
  classical
  unfold blockwisePolarizationBasis blockElementarySymmetric
  simp_rw [_root_.RealRooted.polarization_X_pow (r.2 _), map_mul,
    MvPolynomial.rename_C]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← map_prod]
  simp [MvPolynomial.boxChoose]

private theorem coe_blockwisePolarizationDegreeBoxGeneral_eq_sum
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (p : MvPolynomial.degreeOfLE σ ℂ κ) :
    (blockwisePolarizationDegreeBoxGeneral κ p).1 =
      ∑ r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i},
        MvPolynomial.C (MvPolynomial.coeff r.1 p.1) *
          blockwisePolarizationBasis κ r := by
  classical
  unfold blockwisePolarizationDegreeBoxGeneral
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply,
    MvPolynomial.basisDegreeOfLE_repr_apply,
    MvPolynomial.smul_eq_C_mul, Submodule.coe_sum,
    Submodule.coe_smul]

private theorem coe_blockwisePolarizationDegreeBoxGeneral_eq_normalized_sum
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (p : MvPolynomial.degreeOfLE σ ℂ κ) :
    (blockwisePolarizationDegreeBoxGeneral κ p).1 =
      ∑ r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i},
        MvPolynomial.C ((MvPolynomial.boxChoose κ r.1 : ℂ)⁻¹) *
          MvPolynomial.C (MvPolynomial.coeff r.1 p.1) *
            blockElementarySymmetric κ r.1 := by
  rw [coe_blockwisePolarizationDegreeBoxGeneral_eq_sum]
  apply Fintype.sum_congr
  intro r
  rw [blockwisePolarizationBasis_eq_normalized]
  ring

/-- Specializing the untouched output variables commutes with blockwise
polarization of the source variables. -/
theorem specializeLeft_sourceBlockwisePolarizationGeneral
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (P : MvPolynomial (τ ⊕ σ) ℂ)
    (hdeg : ∀ i, P.degreeOf (Sum.inr i) ≤ κ i)
    (x : τ → ℂ) :
    let q : MvPolynomial.degreeOfLE σ ℂ κ :=
      ⟨_root_.RealRooted.specializeLeft x P,
        specializeLeft_mem_sourceDegreeBox κ P hdeg x⟩
    _root_.RealRooted.specializeLeft x
        (sourceBlockwisePolarizationGeneral κ P) =
      (blockwisePolarizationDegreeBoxGeneral κ q).1 := by
  classical
  dsimp only
  rw [coe_blockwisePolarizationDegreeBoxGeneral_eq_normalized_sum]
  unfold sourceBlockwisePolarizationGeneral
  change
    MvPolynomial.aeval
        (Sum.elim (MvPolynomial.C ∘ x) MvPolynomial.X)
        (∑ r : {r : σ →₀ ℕ // ∀ i, r i ≤ κ i},
          MvPolynomial.C ((MvPolynomial.boxChoose κ r.1 : ℂ)⁻¹) *
            MvPolynomial.rename Sum.inl (sourceCoefficientGeneral P r.1) *
              MvPolynomial.rename Sum.inr
                (blockElementarySymmetric κ r.1)) = _
  rw [map_sum]
  apply Fintype.sum_congr
  intro r
  rw [map_mul, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq]
  have houtput (Q : MvPolynomial τ ℂ) :
      MvPolynomial.aeval
          (Sum.elim (MvPolynomial.C ∘ x) MvPolynomial.X)
          (MvPolynomial.rename (Sum.inl : τ → τ ⊕ PolarizedSource κ) Q) =
        MvPolynomial.C (MvPolynomial.eval x Q) := by
    rw [MvPolynomial.aeval_rename]
    change MvPolynomial.aeval (MvPolynomial.C ∘ x) Q =
      MvPolynomial.C (MvPolynomial.eval x Q)
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add Q R hQ hR =>
        rw [map_add, hQ, hR, map_add]
        exact (map_add MvPolynomial.C _ _).symm
    | mul_X Q i hQ =>
        rw [map_mul, MvPolynomial.aeval_X, hQ, map_mul,
          MvPolynomial.eval_X]
        simpa only [Function.comp_apply] using
          (map_mul MvPolynomial.C (MvPolynomial.eval x Q) (x i)).symm
  have hsource (Q : MvPolynomial (PolarizedSource κ) ℂ) :
      MvPolynomial.aeval
          (Sum.elim (MvPolynomial.C ∘ x) MvPolynomial.X)
          (MvPolynomial.rename
            (Sum.inr : PolarizedSource κ → τ ⊕ PolarizedSource κ) Q) = Q := by
    rw [MvPolynomial.aeval_rename]
    change MvPolynomial.aeval MvPolynomial.X Q = Q
    exact MvPolynomial.aeval_X_left_apply Q
  rw [houtput, hsource,
    coeff_specializeLeft_eq_eval_sourceCoefficientGeneral]

/-- Blockwise polarization of the source variables preserves stability while
leaving an arbitrary output-variable block untouched. -/
theorem mvUpperHalfPlaneStable_sourceBlockwisePolarizationGeneral
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (P : MvPolynomial (τ ⊕ σ) ℂ)
    (hdeg : ∀ i, P.degreeOf (Sum.inr i) ≤ κ i)
    (hstable : _root_.RealRooted.MvUpperHalfPlaneStable P) :
    _root_.RealRooted.MvUpperHalfPlaneStable
      (sourceBlockwisePolarizationGeneral κ P) := by
  intro z hz
  let x : τ → ℂ := fun i => z (Sum.inl i)
  let y : PolarizedSource κ → ℂ := fun i => z (Sum.inr i)
  let q : MvPolynomial.degreeOfLE σ ℂ κ :=
    ⟨_root_.RealRooted.specializeLeft x P,
      specializeLeft_mem_sourceDegreeBox κ P hdeg x⟩
  have hx : ∀ i, 0 < (x i).im := fun i => hz (Sum.inl i)
  have hy : ∀ i, 0 < (y i).im := fun i => hz (Sum.inr i)
  have hqstable : _root_.RealRooted.MvUpperHalfPlaneStable q.1 :=
    hstable.specializeLeft hx
  have hpolar :
      _root_.RealRooted.MvUpperHalfPlaneStable
        (blockwisePolarizationDegreeBoxGeneral κ q).1 :=
    mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral κ q hqstable
  have hfiber :
      _root_.RealRooted.MvUpperHalfPlaneStable
        (_root_.RealRooted.specializeLeft x
          (sourceBlockwisePolarizationGeneral κ P)) := by
    rw [specializeLeft_sourceBlockwisePolarizationGeneral κ P hdeg x]
    exact hpolar
  have hnonzero := hfiber y hy
  rw [_root_.RealRooted.eval_specializeLeft] at hnonzero
  have hxy : Sum.elim x y = z := by
    funext i
    cases i <;> rfl
  simpa only [hxy] using hnonzero

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

/-- Expand the multiaffine symbol of the general source-polarized operator.
All degree-box binomial factors are one. -/
theorem algebraicSymbol_sourcePolarizedOperatorGeneral_eq_sum
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ) :
    MvPolynomial.algebraicSymbol
        (fun _ : PolarizedSource κ => 1)
        (sourcePolarizedOperatorGeneral κ T) =
      ∑ m : {m : PolarizedSource κ →₀ ℕ // ∀ i, m i ≤ 1},
        MvPolynomial.rename Sum.inl
            (T (MvPolynomial.basisDegreeOfLE κ
              (diagonalDegreeBoxIndexGeneral κ m))) *
          MvPolynomial.rightComplementMonomial
            (fun _ : PolarizedSource κ => 1) m.1 := by
  rw [MvPolynomial.algebraicSymbol_eq_sum]
  apply Fintype.sum_congr
  intro m
  rw [MvPolynomial.boxChoose_one_of_le_one m.1 m.2,
    sourcePolarizedOperatorGeneral_basis]
  simp

private theorem
    rightComplementMonomial_one_eq_rename_complementSupportMonomial
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (b : ZeroOneExponent κ) :
    MvPolynomial.rightComplementMonomial (R := ℂ) (τ := τ)
        (fun _ : PolarizedSource κ => 1) b.1 =
      MvPolynomial.rename Sum.inr (complementSupportMonomial κ b) := by
  classical
  rw [MvPolynomial.rightComplementMonomial_eq_prod,
    complementSupportMonomial_eq_fintype_prod_ite]
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro x _hx
  by_cases hbx : b.1 x = 1
  · simp [hbx]
  · have hle := b.2 x
    have hb0 : b.1 x = 0 := by lia
    simp [hb0]

/-- The lifted multiaffine symbol in the common normal form indexed by the
aggregated original source exponent. -/
theorem algebraicSymbol_sourcePolarizedOperatorGeneral_normalForm
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ) :
    MvPolynomial.algebraicSymbol
        (fun _ : PolarizedSource κ => 1)
        (sourcePolarizedOperatorGeneral κ T) =
      ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
        MvPolynomial.rename Sum.inl
            (T (MvPolynomial.basisDegreeOfLE κ m)) *
          MvPolynomial.rename Sum.inr
            (blockElementarySymmetric κ (boxComplementIndex κ m).1) := by
  rw [algebraicSymbol_sourcePolarizedOperatorGeneral_eq_sum]
  simp_rw [rightComplementMonomial_one_eq_rename_complementSupportMonomial]
  calc
    (∑ b : ZeroOneExponent κ,
        MvPolynomial.rename Sum.inl
            (T (MvPolynomial.basisDegreeOfLE κ
              (diagonalDegreeBoxIndexGeneral κ b))) *
          MvPolynomial.rename Sum.inr (complementSupportMonomial κ b)) =
        ∑ bm : Σ m, DiagonalAggregateFiber κ m,
          MvPolynomial.rename Sum.inl
              (T (MvPolynomial.basisDegreeOfLE κ bm.1)) *
            MvPolynomial.rename Sum.inr
              (complementSupportMonomial κ bm.2.1) := by
      apply Fintype.sum_equiv
        (Equiv.sigmaFiberEquiv (diagonalDegreeBoxIndexGeneral κ)).symm
      intro b
      rfl
    _ = ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
          ∑ b : DiagonalAggregateFiber κ m,
            MvPolynomial.rename Sum.inl
                (T (MvPolynomial.basisDegreeOfLE κ m)) *
              MvPolynomial.rename Sum.inr
                (complementSupportMonomial κ b.1) := by
      rw [Fintype.sum_sigma]
    _ = ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
          MvPolynomial.rename Sum.inl
              (T (MvPolynomial.basisDegreeOfLE κ m)) *
            MvPolynomial.rename Sum.inr
              (∑ b : DiagonalAggregateFiber κ m,
                complementSupportMonomial κ b.1) := by
      apply Fintype.sum_congr
      intro m
      rw [map_sum, Finset.mul_sum]
    _ = _ := by
      apply Fintype.sum_congr
      intro m
      rw [sum_complementSupportMonomial_diagonalAggregateFiber]

/-- Borcea--Brändén Lemma 2.5 for an arbitrary finite degree box: the
multiaffine symbol of the source-polarized operator is the source-block
polarization of the original finite algebraic symbol. -/
theorem algebraicSymbol_sourcePolarizedOperatorGeneral
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ) :
    MvPolynomial.algebraicSymbol
        (fun _ : PolarizedSource κ => 1)
        (sourcePolarizedOperatorGeneral κ T) =
      sourceBlockwisePolarizationGeneral κ
        (MvPolynomial.algebraicSymbol κ T) := by
  rw [algebraicSymbol_sourcePolarizedOperatorGeneral_normalForm,
    sourceBlockwisePolarizationGeneral_algebraicSymbol_normalForm]

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

/-- Stable-symbol sufficiency for an arbitrary finite source degree box and
an unrestricted target-variable type. -/
theorem finiteSymbol_preserves_stability_general
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ)
    (hSymbol : MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol κ T))
    (p : MvPolynomial.degreeOfLE σ ℂ κ)
    (hp : MvUpperHalfPlaneStable p.1) :
    MvUpperHalfPlaneStableOrZero (T p) := by
  let Tpolar := sourcePolarizedOperatorGeneral κ T
  have hSymbolDegree (i : σ) :
      (MvPolynomial.algebraicSymbol κ T).degreeOf (Sum.inr i) ≤ κ i :=
    MvPolynomial.degreeOf_algebraicSymbol_inr_le κ T i
  have hPolarSymbol : MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol
        (fun _ : PolarizedSource κ => 1) Tpolar) := by
    rw [algebraicSymbol_sourcePolarizedOperatorGeneral]
    exact mvUpperHalfPlaneStable_sourceBlockwisePolarizationGeneral
      κ (MvPolynomial.algebraicSymbol κ T) hSymbolDegree hSymbol
  have hPolarInput : MvUpperHalfPlaneStable
      (blockwisePolarizationDegreeBoxGeneral κ p).1 :=
    mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral κ p hp
  have hresult := finiteSymbol_preserves_stability Tpolar hPolarSymbol
    (blockwisePolarizationDegreeBoxGeneral κ p) hPolarInput
  rw [sourcePolarizedOperatorGeneral_blockwisePolarization] at hresult
  exact hresult

end


end RealRooted.BorceaBranden
