import RealRooted.BorceaBranden.Transcendental.SymbolBridge

open Filter Topology

noncomputable section

namespace RealRooted.BorceaBranden

variable {σ : Type} [Fintype σ]

/-- A linear operator on the full multivariate polynomial ring preserves complex
upper-half-plane stability, allowing zero output. -/
def PreservesComplexStability
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) : Prop :=
  ∀ p, MvUpperHalfPlaneStable p → MvUpperHalfPlaneStableOrZero (T p)

/-- The global stable rank-at-most-one alternative in the complex classification. -/
def HasGlobalStableRankOneRepresentation
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) : Prop :=
  ∃ (α : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (P : MvPolynomial σ ℂ),
    MvUpperHalfPlaneStable P ∧ ∀ p, T p = (α p) • P

private theorem HasGlobalStableRankOneRepresentation.onDegreeBox
    {T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ}
    (hT : HasGlobalStableRankOneRepresentation T) (κ : σ → ℕ) :
    HasStableRankOneRepresentation κ (degreeBoxRestriction κ T) := by
  obtain ⟨α, P, hP, hrepr⟩ := hT
  refine ⟨α.comp (MvPolynomial.degreeOfLE σ ℂ κ).subtype, P, hP, ?_⟩
  intro p
  exact hrepr p.1

omit [Fintype σ] in
/-- A global stable rank-at-most-one representation preserves complex stability. -/
theorem HasGlobalStableRankOneRepresentation.preservesComplexStability
    [Finite σ]
    {T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ}
    (hT : HasGlobalStableRankOneRepresentation T) :
    PreservesComplexStability T := by
  classical
  let _ := Fintype.ofFinite σ
  intro p hp
  let κ := fun i => p.degreeOf i
  let q : MvPolynomial.degreeOfLE σ ℂ κ :=
    ⟨p, (MvPolynomial.mem_degreeOfLE_iff_degreeOf p).2 fun _ => le_rfl⟩
  have hpreserves :=
    (hT.onDegreeBox κ).preservesComplexStabilityOnDegreeBox
  exact hpreserves q hp

omit [Fintype σ] in
private theorem hasGlobalStableRankOneRepresentation_of_range_stableOrZero
    {T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ}
    (hT : ∀ p, MvUpperHalfPlaneStableOrZero (T p)) :
    HasGlobalStableRankOneRepresentation T := by
  by_cases hzero : T = 0
  · refine ⟨0, 1, MvUpperHalfPlaneStable.one, ?_⟩
    intro p
    simp [hzero]
  · obtain ⟨p₀, hp₀⟩ : ∃ p, T p ≠ 0 := by
      by_contra h
      push Not at h
      apply hzero
      apply LinearMap.ext
      intro p
      exact h p
    let P := T p₀
    have hP : MvUpperHalfPlaneStable P := (hT p₀).resolve_left hp₀
    let z : σ → ℂ := fun _ => Complex.I
    have hz : ∀ i, 0 < (z i).im := by simp [z]
    have hPz : MvPolynomial.eval z P ≠ 0 := hP z hz
    let α : MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun p => MvPolynomial.eval z (T p) / MvPolynomial.eval z P
        map_add' := by
          intro p q
          simp [map_add, add_div]
        map_smul' := by
          intro c p
          simp [map_smul, mul_div_assoc] }
    refine ⟨α, P, hP, ?_⟩
    intro p
    let q := T (p - (α p) • p₀)
    have hq : q = T p - (α p) • P := by simp [q, P]
    have hqeval : MvPolynomial.eval z q = 0 := by
      rw [hq]
      simp [α]
      field_simp
      ring
    have hqzero : q = 0 := by
      rcases hT (p - (α p) • p₀) with hqzero | hqstable
      · exact hqzero
      · exact (hqstable z hz hqeval).elim
    rw [hq] at hqzero
    exact sub_eq_zero.mp hqzero

/-- The coordinate degree box naturally containing a polynomial. -/
def polynomialDegreeBox (p : MvPolynomial σ ℂ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => p.degreeOf i

@[simp]
theorem polynomialDegreeBox_apply (p : MvPolynomial σ ℂ) (i : σ) :
    polynomialDegreeBox p i = p.degreeOf i := rfl

private theorem preservesComplexStabilityOnDegreeBox_of_preservesComplexStability
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
    (hT : PreservesComplexStability T) (β : σ →₀ ℕ) :
    PreservesComplexStabilityOnDegreeBox (fun i => β i)
      (degreeBoxRestriction (fun i => β i) T) := by
  intro p hp
  exact hT p.1 hp

private theorem signedInvFactorial_ne_zero' (α : σ →₀ ℕ) :
    signedInvFactorial α ≠ 0 := by
  unfold signedInvFactorial multiFactorial
  apply div_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · exact_mod_cast Finset.prod_ne_zero_iff.mpr
      (fun i _hi => Nat.factorial_ne_zero (α i))

private theorem fall_ne_zero_of_le {α β : σ →₀ ℕ} (hαβ : α ≤ β) :
    (fall α β : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  unfold fall
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  rw [Nat.cast_ne_zero, ne_eq, Nat.descFactorial_eq_zero_iff_lt]
  exact not_lt.mpr (hαβ i)

private theorem degreeBoxRestriction_eq_zero_of_jensenTruncation_eq_zero
    (β : σ →₀ ℕ) (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
    (hzero : jensenTruncation β T = 0) :
    degreeBoxRestriction (fun i => β i) T = 0 := by
  apply (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun i => β i)).ext
  intro α
  apply MvPolynomial.ext
  intro γ
  have hz := congrArg (fun p : MvPolynomial (σ ⊕ σ) ℂ =>
    p.coeff (γ.sumElim α.1)) hzero
  rw [coeff_jensenTruncation] at hz
  have hpair :
      Finsupp.sumFinsuppEquivProdFinsupp (γ.sumElim α.1) = (γ, α.1) := by
    change Finsupp.sumFinsuppEquivProdFinsupp
      (Finsupp.sumFinsuppEquivProdFinsupp.symm (γ, α.1)) = _
    exact Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply _
  rw [hpair] at hz
  have hle : (α.1 : σ →₀ ℕ) ≤ β := fun i => α.2 i
  rw [ite_eq_left hle] at hz
  unfold transcendentalSymbolCoeff seriesCoeff at hz
  rw [hpair, coeff_transcendentalSymbolPolynomial] at hz
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hz
  have hscalar : (fall α.1 β : ℂ) * signedInvFactorial α.1 ≠ 0 :=
    mul_ne_zero (fall_ne_zero_of_le α.2) (signedInvFactorial_ne_zero' α.1)
  simp only [degreeBoxRestriction, LinearMap.comp_apply, Submodule.coe_subtype,
    MvPolynomial.coe_basisDegreeOfLE, LinearMap.zero_apply]
  rw [AddMonoidAlgebra.coeff_zero]
  have hproduct :
      ((fall α.1 β : ℂ) * signedInvFactorial α.1) *
        (T (MvPolynomial.monomial α.1 1)).coeff γ = 0 := by
    simpa [mul_assoc] using hz
  exact (mul_eq_zero.mp hproduct).resolve_left hscalar

/-- The transcendental-symbol branch of Borcea--Brändén, arXiv:0809.0401,
Theorem 1.3 preserves complex upper-half-plane stability. -/
theorem preservesComplexStability_of_transcendentalSymbol_stableLimit
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
    (hT : IsComplexStableLimit (transcendentalSymbolPolynomial T)) :
    PreservesComplexStability T := by
  classical
  intro p hp
  let β := polynomialDegreeBox p
  let q : MvPolynomial.degreeOfLE σ ℂ (fun i => β i) :=
    ⟨p, (MvPolynomial.mem_degreeOfLE_iff_degreeOf p).2 fun i => le_rfl⟩
  have hj : MvUpperHalfPlaneStableOrZero (jensenTruncation β T) := by
    exact fallingFactorial_glue_stableOrZero_of_isComplexStableLimit
      (transcendentalSymbolPolynomial T) hT β
  rcases hj with hjzero | hjstable
  · left
    have hrestriction :=
      degreeBoxRestriction_eq_zero_of_jensenTruncation_eq_zero β T hjzero
    have hvalue := LinearMap.congr_fun hrestriction q
    simpa only [degreeBoxRestriction, LinearMap.comp_apply, Submodule.coe_subtype,
      LinearMap.zero_apply, q] using hvalue
  · have halgebraic : MvUpperHalfPlaneStable
        (MvPolynomial.algebraicSymbol (fun i => β i)
          (degreeBoxRestriction (fun i => β i) T)) :=
      (algebraicSymbol_stable_iff_jensenTruncation_stable β T).2 hjstable
    have hpreserves := (finiteComplexSymbolClassification σ (fun i => β i)
      (degreeBoxRestriction (fun i => β i) T)).2 (Or.inr halgebraic)
    exact hpreserves q hp

private theorem not_hasStableRankOneRepresentation_of_bad_polynomial
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
    (p : MvPolynomial σ ℂ) (hp : ¬MvUpperHalfPlaneStableOrZero (T p))
    (κ : σ → ℕ) (hpκ : ∀ i, p.degreeOf i ≤ κ i) :
    ¬HasStableRankOneRepresentation κ (degreeBoxRestriction κ T) := by
  intro hrank
  let q : MvPolynomial.degreeOfLE σ ℂ κ :=
    ⟨p, (MvPolynomial.mem_degreeOfLE_iff_degreeOf p).2 hpκ⟩
  obtain ⟨α, P, hP, hrepr⟩ := hrank
  apply hp
  have hq := hrepr q
  change T p = (α q) • P at hq
  rw [hq, MvPolynomial.smul_eq_C_mul]
  exact hP.orZero.C_mul (α q)

/-- Necessity in complex Borcea--Brändén Theorem 1.3
(arXiv:0809.0401): a global stability preserver has either the stable
rank-at-most-one form or a transcendental symbol in the complex stable-limit class. -/
theorem rankOne_or_transcendentalSymbol_stableLimit_of_preservesComplexStability
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
    (hT : PreservesComplexStability T) :
    HasGlobalStableRankOneRepresentation T ∨
      IsComplexStableLimit (transcendentalSymbolPolynomial T) := by
  classical
  by_cases hrange : ∀ p, MvUpperHalfPlaneStableOrZero (T p)
  · exact Or.inl
      (hasGlobalStableRankOneRepresentation_of_range_stableOrZero hrange)
  · right
    push Not at hrange
    obtain ⟨p, hp⟩ := hrange
    obtain ⟨F, hF, hsum, hconv⟩ :=
      exists_stableOrZero_tendstoLocallyUniformly_of_eventually_constExp_glue
        (transcendentalSymbolPolynomial T) p.totalDegree (by
          intro m hm
          left
          let β := constExp σ (m + 1)
          have hpreserves :=
            preservesComplexStabilityOnDegreeBox_of_preservesComplexStability T hT β
          have hpβ : ∀ i, p.degreeOf i ≤ β i := by
            intro i
            change p.degreeOf i ≤ m + 1
            exact (MvPolynomial.degreeOf_le_totalDegree p i).trans
              (hm.trans (Nat.le_succ m))
          have hnrank : ¬HasStableRankOneRepresentation (fun i => β i)
              (degreeBoxRestriction (fun i => β i) T) :=
            not_hasStableRankOneRepresentation_of_bad_polynomial
              T p hp (fun i => β i) hpβ
          have halgebraic : MvUpperHalfPlaneStable
              (MvPolynomial.algebraicSymbol (fun i => β i)
                (degreeBoxRestriction (fun i => β i) T)) :=
            ((finiteComplexSymbolClassification σ (fun i => β i)
              (degreeBoxRestriction (fun i => β i) T)).1 hpreserves).resolve_left hnrank
          exact (algebraicSymbol_stable_iff_jensenTruncation_stable β T).1
            halgebraic)
    exact ⟨F, fun k => (hF k).symm, hsum, hconv⟩

/-- **Complex Borcea--Brändén Theorem 1.3** (arXiv:0809.0401).
A complex linear operator on a multivariate polynomial ring preserves
upper-half-plane stability exactly when it has the stable rank-at-most-one form,
or its transcendental symbol belongs to the complex stable-limit class. -/
theorem preservesComplexStability_iff_rankOne_or_transcendentalSymbol_stableLimit
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) :
    PreservesComplexStability T ↔
      HasGlobalStableRankOneRepresentation T ∨
        IsComplexStableLimit (transcendentalSymbolPolynomial T) := by
  constructor
  · exact rankOne_or_transcendentalSymbol_stableLimit_of_preservesComplexStability T
  · rintro (hrank | hsymbol)
    · exact hrank.preservesComplexStability
    · exact preservesComplexStability_of_transcendentalSymbol_stableLimit T hsymbol

end RealRooted.BorceaBranden
