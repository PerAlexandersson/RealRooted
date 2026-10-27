module

public import RealRooted.BorceaBranden.RealFiniteNecessity
public import RealRooted.BorceaBranden.FiniteSymbolClassification
public import RealRooted.BorceaBranden.RealFiniteClassification
import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization
public import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol

@[expose] public section

noncomputable section

namespace RealRooted
namespace BorceaBranden

private def complexifyMvLinear (σ : Type*) :
    MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℂ where
  toFun := complexifyMv
  map_add' p q := by simp [complexifyMv]
  map_smul' c p := by
    simp [complexifyMv, Algebra.smul_def]

/-- Complexify a real polynomial while retaining its coordinate-wise degree-box
membership. -/
def complexifyDegreeBox
    {σ : Type*} (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ]
      MvPolynomial.degreeOfLE σ ℂ κ where
  toFun p := ⟨complexifyMv p.1, by
    rw [MvPolynomial.mem_degreeOfLE]
    intro m hm i
    exact (MvPolynomial.mem_degreeOfLE p.1).mp p.2 m
      (MvPolynomial.support_map_subset _ _ hm) i⟩
  map_add' p q := by
    apply Subtype.ext
    simp [complexifyMv]
  map_smul' c p := by
    apply Subtype.ext
    simp [complexifyMv, Algebra.smul_def]

/-- The underlying polynomial of `complexifyDegreeBox` is `complexifyMv`. -/
@[simp]
theorem coe_complexifyDegreeBox
    {σ : Type*} (κ : σ → ℕ)
    (p : MvPolynomial.degreeOfLE σ ℝ κ) :
    (complexifyDegreeBox κ p).1 = complexifyMv p.1 :=
  rfl

/-- Complexifying a real bounded monomial-basis vector gives the corresponding
complex bounded monomial-basis vector. -/
@[simp]
theorem complexifyDegreeBox_basis
    {σ : Type*} {κ : σ → ℕ}
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    complexifyDegreeBox κ (MvPolynomial.basisDegreeOfLE (R := ℝ) κ m) =
      MvPolynomial.basisDegreeOfLE (R := ℂ) κ m := by
  apply Subtype.ext
  simp [complexifyDegreeBox, complexifyMv]

/-- The coefficientwise complex-linear extension of a real operator on a
coordinate-wise degree box. -/
def complexificationDegreeBoxLinearMap
    {σ : Type*} (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ) :
    MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ :=
  (MvPolynomial.basisDegreeOfLE (R := ℂ) κ).constr ℂ fun m =>
    complexifyMv (T (MvPolynomial.basisDegreeOfLE (R := ℝ) κ m))

/-- The complex extension sends a complex monomial-basis vector to the
complexification of its real-operator image. -/
@[simp]
theorem complexificationDegreeBoxLinearMap_basis
    {σ : Type*} (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    complexificationDegreeBoxLinearMap κ T
        (MvPolynomial.basisDegreeOfLE (R := ℂ) κ m) =
      complexifyMv (T (MvPolynomial.basisDegreeOfLE (R := ℝ) κ m)) := by
  simp [complexificationDegreeBoxLinearMap]

/-- Complex-linear extension agrees with the original operator on complexified
real inputs. -/
@[simp]
theorem complexificationDegreeBoxLinearMap_complexify
    {σ : Type*} (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ)
    (p : MvPolynomial.degreeOfLE σ ℝ κ) :
    complexificationDegreeBoxLinearMap κ T (complexifyDegreeBox κ p) =
      complexifyMv (T p) := by
  let lhs : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℂ :=
    (complexificationDegreeBoxLinearMap κ T).restrictScalars ℝ |>.comp
      (complexifyDegreeBox κ)
  let rhs : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℂ :=
    (complexifyMvLinear σ).comp T
  have hmaps : lhs = rhs := by
    apply (MvPolynomial.basisDegreeOfLE (R := ℝ) κ).ext
    intro m
    simp only [lhs, rhs, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      complexifyDegreeBox_basis, complexificationDegreeBoxLinearMap_basis]
    rfl
  exact LinearMap.congr_fun hmaps p

/-- The algebraic symbol of the complex-linear extension is the
coefficientwise complexification of the real algebraic symbol. -/
theorem algebraicSymbol_complexificationDegreeBoxLinearMap
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ) :
    MvPolynomial.algebraicSymbol κ (complexificationDegreeBoxLinearMap κ T) =
      complexifyMv (MvPolynomial.algebraicSymbol κ T) := by
  classical
  simp only [MvPolynomial.algebraicSymbol_eq_sum]
  change (∑ m, MvPolynomial.C (MvPolynomial.boxChoose κ m.1 : ℂ) *
      MvPolynomial.rename Sum.inl
        (complexificationDegreeBoxLinearMap κ T
          (MvPolynomial.basisDegreeOfLE κ m)) *
        MvPolynomial.rightComplementMonomial κ m.1) =
    MvPolynomial.map Complex.ofRealHom
      (∑ m, MvPolynomial.C (MvPolynomial.boxChoose κ m.1 : ℝ) *
        MvPolynomial.rename Sum.inl
          (T (MvPolynomial.basisDegreeOfLE κ m)) *
          MvPolynomial.rightComplementMonomial κ m.1)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  have hright :
      MvPolynomial.map Complex.ofRealHom
          (MvPolynomial.rightComplementMonomial (R := ℝ) (τ := σ) κ m.1) =
        MvPolynomial.rightComplementMonomial (R := ℂ) (τ := σ) κ m.1 := by
    simp [MvPolynomial.rightComplementMonomial]
  rw [complexificationDegreeBoxLinearMap_basis]
  simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_rename,
    hright, complexifyMv]
  norm_cast

/-- The positive algebraic-symbol branch of Borcea--Brändén,
arXiv:0809.0401, Theorem 1.2 preserves real stability on a degree box. -/
theorem preservesRealStabilityOnDegreeBox_of_algebraicSymbol_realStable
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hSymbol : MvRealStable (MvPolynomial.algebraicSymbol κ T)) :
    PreservesRealStabilityOnDegreeBox κ T := by
  intro p hp
  let pℂ := complexifyDegreeBox κ p
  have hpℂ : MvUpperHalfPlaneStable pℂ.1 := hp
  have hsymbolℂ : MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol κ
        (complexificationDegreeBoxLinearMap κ T)) := by
    rw [algebraicSymbol_complexificationDegreeBoxLinearMap]
    exact hSymbol
  have hout := finiteSymbol_preserves_stability_general κ
    (complexificationDegreeBoxLinearMap κ T) hsymbolℂ pℂ hpℂ
  rw [complexificationDegreeBoxLinearMap_complexify] at hout
  exact mvRealStableOrZero_iff_complexifyMv.mpr hout

end BorceaBranden
end RealRooted
