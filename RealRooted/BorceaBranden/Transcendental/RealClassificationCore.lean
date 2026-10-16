module

public import RealRooted.BorceaBranden.Transcendental.RealOperatorBasics

@[expose] public noncomputable section

open Filter Topology
open scoped BigOperators

namespace RealRooted.BorceaBranden

variable {σ : Type} [Fintype σ]

/-- Precompose a real operator with simultaneous source-variable negation. -/
def sourceNegatedRealOperator
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ :=
  T.comp sourceNegationLinear

private theorem prod_negOne_pow_eq (m : σ →₀ ℕ) :
    (∏ i, (-1 : ℝ) ^ m i) = (-1 : ℝ) ^ (∑ i, m i) := by
  rw [← Finset.prod_pow_eq_pow_sum]

/-- Negating the right formal variables of the transcendental symbol is the
symbol of the source-negated operator. -/
theorem realTranscendentalSymbolPolynomial_sourceNegatedRealOperator
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) :
    realTranscendentalSymbolPolynomial (sourceNegatedRealOperator T) =
      negRightFamily (realTranscendentalSymbolPolynomial T) := by
  classical
  funext α
  unfold realTranscendentalSymbolPolynomial sourceNegatedRealOperator
    negRightFamily
  change MvPolynomial.C (realSignedInvFactorial α) *
      T (sourceNegation (MvPolynomial.monomial α 1)) = _
  rw [sourceNegation_monomial_one, map_smul, prod_negOne_pow_eq]
  simp only [MvPolynomial.smul_eq_C_mul]
  ring

/-- A stable positive finite algebraic symbol gives the corresponding real
falling-factorial truncation as a real stable-or-zero polynomial. -/
theorem realGlue_stableOrZero_of_algebraicSymbol_realStable
    [DecidableEq σ]
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) (β : σ →₀ ℕ)
    (hSymbol : MvRealStable
      (MvPolynomial.algebraicSymbol (fun i => β i)
        (T.comp (MvPolynomial.degreeOfLE σ ℝ (fun i => β i)).subtype))) :
    MvRealStableOrZero
      (realGlue (realTranscendentalSymbolPolynomial T)
        (fun α => fall α β) β) := by
  classical
  have hComplex : MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol (fun i => β i)
        (degreeBoxRestriction (fun i => β i)
          (complexificationMvLinearMap T))) := by
    rw [degreeBoxRestriction_complexificationMvLinearMap,
      algebraicSymbol_complexificationDegreeBoxLinearMap]
    exact hSymbol
  have hj :=
    (algebraicSymbol_stable_iff_jensenTruncation_stable β
      (complexificationMvLinearMap T)).1 hComplex
  rw [mvRealStableOrZero_iff_complexifyMv, complexifyMv_realGlue]
  have heq :
      glue (complexifyFamily (realTranscendentalSymbolPolynomial T))
          (fun α => fall α β) β =
        jensenTruncation β (complexificationMvLinearMap T) := by
    apply MvPolynomial.ext
    intro e
    rw [coeff_glue, coeff_jensenTruncation]
    congr 1
    exact congrArg (fun P => seriesCoeff P e)
      (transcendentalSymbolPolynomial_complexificationMvLinearMap T).symm
  rw [heq]
  exact Or.inr hj

private theorem reflectedDegreeBox_eq_smul_sourceNegated
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) (κ : σ → ℕ) :
    sourceReflectedOperator κ
        (T.comp (MvPolynomial.degreeOfLE σ ℝ κ).subtype) =
      (∏ i, (-1 : ℝ) ^ κ i) •
        ((sourceNegatedRealOperator T).comp
          (MvPolynomial.degreeOfLE σ ℝ κ).subtype) := by
  apply (MvPolynomial.basisDegreeOfLE (R := ℝ) κ).ext
  intro m
  simp only [sourceReflectedOperator, LinearMap.comp_apply, Submodule.coe_subtype,
    sourceNegatedRealOperator, LinearMap.smul_apply]
  rw [sourceReflectionDegreeBox_basis_explicit]
  rw [Submodule.coe_smul, map_smul]
  rw [MvPolynomial.coe_basisDegreeOfLE]
  change ((∏ i, (-1 : ℝ) ^ κ i) * ∏ i, (-1 : ℝ) ^ m.1 i) •
      T (MvPolynomial.monomial m.1 1) =
    (∏ i, (-1 : ℝ) ^ κ i) •
      T (sourceNegation (MvPolynomial.monomial m.1 1))
  rw [sourceNegation_monomial_one, map_smul, smul_smul]

/-- A stable negative-right finite algebraic symbol gives the signed real
falling-factorial truncation as a real stable-or-zero polynomial. -/
theorem realGlue_negRight_stableOrZero_of_algebraicSymbolNegRight_realStable
    [DecidableEq σ]
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) (β : σ →₀ ℕ)
    (hSymbol : MvRealStable
      (MvPolynomial.algebraicSymbolNegRight (fun i => β i)
        (T.comp (MvPolynomial.degreeOfLE σ ℝ (fun i => β i)).subtype))) :
    MvRealStableOrZero
      (realGlue (negRightFamily (realTranscendentalSymbolPolynomial T))
        (fun α => fall α β) β) := by
  classical
  let R := T.comp (MvPolynomial.degreeOfLE σ ℝ (fun i => β i)).subtype
  let Tn := sourceNegatedRealOperator T
  let c : ℝ := ∏ i, (-1 : ℝ) ^ β i
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity
  have hReflected : MvRealStable
      (MvPolynomial.algebraicSymbol (fun i => β i)
        (sourceReflectedOperator (fun i => β i) R)) := by
    rw [algebraicSymbol_sourceReflectedOperator]
    exact hSymbol
  have hOperator : sourceReflectedOperator (fun i => β i) R =
      c • (Tn.comp (MvPolynomial.degreeOfLE σ ℝ (fun i => β i)).subtype) := by
    exact reflectedDegreeBox_eq_smul_sourceNegated T (fun i => β i)
  rw [hOperator, MvPolynomial.algebraicSymbol_smul] at hReflected
  have hNegatedSymbol : MvRealStable
      (MvPolynomial.algebraicSymbol (fun i => β i)
        (Tn.comp (MvPolynomial.degreeOfLE σ ℝ (fun i => β i)).subtype)) := by
    intro z hz
    have hv := hReflected z hz
    simp only [MvPolynomial.smul_eq_C_mul, complexifyMv, map_mul,
      MvPolynomial.map_C, MvPolynomial.eval_C] at hv
    exact (mul_ne_zero_iff.mp hv).2
  have hj := realGlue_stableOrZero_of_algebraicSymbol_realStable
    Tn β hNegatedSymbol
  rw [realTranscendentalSymbolPolynomial_sourceNegatedRealOperator] at hj
  exact hj

/-- The negative-right transcendental-symbol branch of real Theorem 1.4
preserves real stability. -/
theorem preservesRealStability_of_negRight_transcendentalSymbol_stableLimit
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (hT : IsRealStableLimit
      (negRightFamily (realTranscendentalSymbolPolynomial T))) :
    PreservesRealStability T := by
  have hreflected : IsRealStableLimit
      (realTranscendentalSymbolPolynomial (sourceNegatedRealOperator T)) := by
    rw [realTranscendentalSymbolPolynomial_sourceNegatedRealOperator]
    exact hT
  have hpreserves :=
    preservesRealStability_of_realTranscendentalSymbol_stableLimit
      (sourceNegatedRealOperator T) hreflected
  intro p hp
  have hout := hpreserves (sourceNegation p) (MvRealStable.sourceNegation hp)
  change MvRealStableOrZero (T (sourceNegation (sourceNegation p))) at hout
  rw [sourceNegation_involutive] at hout
  exact hout

end RealRooted.BorceaBranden
