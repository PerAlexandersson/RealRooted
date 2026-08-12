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
