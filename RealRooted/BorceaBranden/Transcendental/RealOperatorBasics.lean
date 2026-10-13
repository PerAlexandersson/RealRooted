import RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne
import RealRooted.BorceaBranden.Transcendental.ComplexClassification

noncomputable section

namespace RealRooted.BorceaBranden

variable {σ : Type} [Fintype σ]

/-- A real linear operator on the full polynomial ring preserves real
stability, allowing zero output. -/
def PreservesRealStability
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) : Prop :=
  ∀ p, MvRealStable p → MvRealStableOrZero (T p)

/-- The global stable rank-at-most-two alternative in real Theorem 1.4. -/
def HasGlobalStableRankTwoRepresentation
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) : Prop :=
  HasStableRankTwoRangeRepresentation T

omit [Fintype σ] in
/-- A global stable rank-at-most-two representation preserves real
stability. -/
theorem HasGlobalStableRankTwoRepresentation.preservesRealStability
    {T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hT : HasGlobalStableRankTwoRepresentation T) :
    PreservesRealStability T := by
  intro p _hp
  obtain ⟨α, β, P, Q, hall, hrepr⟩ := hT
  rw [hrepr, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  exact hall (α p) (β p)

/-- The coefficientwise complex-linear extension of a real operator on the
full multivariate polynomial ring. -/
def complexificationMvLinearMap
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) :
    MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
  (MvPolynomial.basisMonomials σ ℂ).constr ℂ fun m =>
    complexifyMv (T (MvPolynomial.monomial m 1))

omit [Fintype σ] in
/-- The full complex extension agrees with the real operator on a monomial. -/
@[simp]
theorem complexificationMvLinearMap_monomial_one
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    complexificationMvLinearMap T (MvPolynomial.monomial m 1) =
      complexifyMv (T (MvPolynomial.monomial m 1)) := by
  exact (MvPolynomial.basisMonomials σ ℂ).constr_basis ℂ
    (fun e => complexifyMv (T (MvPolynomial.monomial e 1))) m

private def complexifyMvLinearFull (σ : Type) :
    MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℂ where
  toFun := complexifyMv
  map_add' p q := by simp [complexifyMv]
  map_smul' c p := by simp [complexifyMv, Algebra.smul_def]

omit [Fintype σ] in
/-- The full complex extension agrees with the original operator on
complexified real inputs. -/
@[simp]
theorem complexificationMvLinearMap_complexify
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (p : MvPolynomial σ ℝ) :
    complexificationMvLinearMap T (complexifyMv p) = complexifyMv (T p) := by
  let lhs : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℂ :=
    (complexificationMvLinearMap T).restrictScalars ℝ |>.comp
      (complexifyMvLinearFull σ)
  let rhs : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℂ :=
    (complexifyMvLinearFull σ).comp T
  have hmaps : lhs = rhs := by
    apply (MvPolynomial.basisMonomials σ ℝ).ext
    intro m
    change complexificationMvLinearMap T
        (complexifyMv (MvPolynomial.monomial m 1)) =
      complexifyMv (T (MvPolynomial.monomial m 1))
    rw [show complexifyMv (MvPolynomial.monomial m 1) =
        MvPolynomial.monomial m 1 by simp [complexifyMv]]
    exact complexificationMvLinearMap_monomial_one T m
  exact LinearMap.congr_fun hmaps p

private theorem signedInvFactorial_eq_realSignedInvFactorial
    (α : σ →₀ ℕ) :
    signedInvFactorial α = (realSignedInvFactorial α : ℂ) := by
  unfold signedInvFactorial realSignedInvFactorial
  push_cast
  rfl

/-- The transcendental-symbol family of the complex extension is the
complexification of the real transcendental-symbol family. -/
theorem transcendentalSymbolPolynomial_complexificationMvLinearMap
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) :
    transcendentalSymbolPolynomial (complexificationMvLinearMap T) =
      complexifyFamily (realTranscendentalSymbolPolynomial T) := by
  classical
  funext α
  unfold transcendentalSymbolPolynomial realTranscendentalSymbolPolynomial
    complexifyFamily
  rw [complexificationMvLinearMap_monomial_one,
    signedInvFactorial_eq_realSignedInvFactorial]
  simp [complexifyMv]

/-- Restriction to a real degree box commutes with complex-linear extension. -/
theorem degreeBoxRestriction_complexificationMvLinearMap
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) (κ : σ → ℕ) :
    degreeBoxRestriction κ (complexificationMvLinearMap T) =
      complexificationDegreeBoxLinearMap κ
        (T.comp (MvPolynomial.degreeOfLE σ ℝ κ).subtype) := by
  classical
  apply (MvPolynomial.basisDegreeOfLE (R := ℂ) κ).ext
  intro m
  simp only [degreeBoxRestriction, LinearMap.comp_apply, Submodule.coe_subtype]
  rw [show ((MvPolynomial.basisDegreeOfLE (R := ℂ) κ m :
      MvPolynomial.degreeOfLE σ ℂ κ) : MvPolynomial σ ℂ) =
        MvPolynomial.monomial m.1 1 by
      ext e
      simp [MvPolynomial.coe_basisDegreeOfLE]]
  rw [complexificationMvLinearMap_monomial_one]
  simp

/-- The positive transcendental-symbol branch of real Theorem 1.4 preserves
real stability. -/
theorem preservesRealStability_of_realTranscendentalSymbol_stableLimit
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (hT : IsRealStableLimit (realTranscendentalSymbolPolynomial T)) :
    PreservesRealStability T := by
  classical
  intro p hp
  have hcomplex : IsComplexStableLimit
      (transcendentalSymbolPolynomial (complexificationMvLinearMap T)) := by
    rw [transcendentalSymbolPolynomial_complexificationMvLinearMap]
    exact hT.isComplexStableLimit
  have hout := preservesComplexStability_of_transcendentalSymbol_stableLimit
    (complexificationMvLinearMap T) hcomplex (complexifyMv p) hp
  rw [complexificationMvLinearMap_complexify] at hout
  exact mvRealStableOrZero_iff_complexifyMv.mpr hout

end RealRooted.BorceaBranden
