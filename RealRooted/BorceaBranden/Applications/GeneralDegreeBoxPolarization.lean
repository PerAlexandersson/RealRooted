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

end


end RealRooted.BorceaBranden
