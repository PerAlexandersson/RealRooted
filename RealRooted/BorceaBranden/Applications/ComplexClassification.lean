import RealRooted.BorceaBranden.FiniteSymbolPreserver
import RealRooted.BorceaBranden.FiniteSymbolClassification

/-!
# Checked pieces of the complex finite-symbol classification

This application-layer module connects the multiaffine finite-symbol theorem
to the classification interface without creating a cycle between the challenge
entry point and its univariate compatibility modules.
-/

namespace RealRooted.BorceaBranden

noncomputable section

/-- Stable-symbol sufficiency for a multiaffine source box. This is the checked
local form of Borcea--Brändén Lemma 2.2. -/
theorem preservesComplexStabilityOnDegreeBox_one_of_algebraicSymbol_stable
    {σ : Type*} [Fintype σ]
    {T : MvPolynomial.degreeOfLE σ ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial σ ℂ}
    (hSymbol : MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol (fun _ : σ => 1) T)) :
    PreservesComplexStabilityOnDegreeBox (fun _ : σ => 1) T := by
  intro f hf
  exact RealRooted.BorceaBranden.finiteSymbol_preserves_stability
    T hSymbol f hf

/-- The reverse implication in the multiaffine instance of the complex finite
classification: either source alternative gives a stability preserver. -/
theorem preservesComplexStabilityOnDegreeBox_one_of_rankOne_or_symbol
    {σ : Type*} [Fintype σ]
    {T : MvPolynomial.degreeOfLE σ ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial σ ℂ}
    (h : HasStableRankOneRepresentation (fun _ : σ => 1) T ∨
      MvUpperHalfPlaneStable
        (MvPolynomial.algebraicSymbol (fun _ : σ => 1) T)) :
    PreservesComplexStabilityOnDegreeBox (fun _ : σ => 1) T := by
  rcases h with hrank | hSymbol
  · exact hrank.preservesComplexStabilityOnDegreeBox
  · exact
      preservesComplexStabilityOnDegreeBox_one_of_algebraicSymbol_stable hSymbol

end


end RealRooted.BorceaBranden

namespace RealRooted.Challenges.BorceaBranden

export RealRooted.BorceaBranden
  (preservesComplexStabilityOnDegreeBox_one_of_algebraicSymbol_stable
    preservesComplexStabilityOnDegreeBox_one_of_rankOne_or_symbol)

end RealRooted.Challenges.BorceaBranden
