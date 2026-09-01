import RealRooted.BorceaBranden.FiniteSymbolClassification
import RealRooted.BorceaBranden.UnivariateFiniteSymbol

/-!
# Borcea--Branden finite-symbol classification challenge entry point

Human statement:
https://www.symmetricfunctions.com/stablePolynomials.htm#borceaBrandenFiniteSymbol

Original reference: J. Borcea and P. Branden, "The Lee-Yang and Polya-Schur
programs. I. Linear operators preserving stability", Invent. Math. 177 (2009),
541--569.

This module preserves the established challenge-facing names as explicit
exports from the reusable complex and real-univariate theorem modules.
-/

namespace RealRooted
namespace Challenges
namespace BorceaBranden

export RealRooted.BorceaBranden
  (PreservesComplexStabilityOnDegreeBox
    shiftedBoxPolynomial
    shiftedBoxPolynomial_eq_prod
    mvUpperHalfPlaneStable_shiftedBoxPolynomial
    HasShiftedBoxPerturbations
    IsUniformlyDominatedByShiftedBox
    hasShiftedBoxPerturbations_of_uniformlyDominated
    uniformlyDominatedByShiftedBox
    hasShiftedBoxPerturbations
    specializeRight_algebraicSymbol
    eval_algebraicSymbol_eq_eval_shiftedBoxPolynomial
    algebraicSymbol_stable_of_preserves_of_shiftedBox_ne_zero
    HasStableRankOneRepresentation
    hasStableRankOneRepresentation_of_range_stableOrZero
    hasStableRankOneRepresentation_of_preserves_of_shiftedBox_eq_zero
    rankOne_or_algebraicSymbol_stable_of_preserves_of_perturbations
    rankOne_or_algebraicSymbol_stable_of_preserves_of_robust_perturbations
    rankOne_or_algebraicSymbol_stable_of_preserves
    HasStableRankOneRepresentation.preservesComplexStabilityOnDegreeBox
    finiteComplexSymbolClassificationStatement
    finiteComplexSymbolClassification
    finiteComplexSymbolIffStatement
    finiteComplexSymbolIff
    polynomialInFirstMv
    finiteAlgebraicSymbol
    PreservesRealRootedUpTo
    finiteSymbolTheoremStatement
    preservesRealRootedUpTo_of_finiteSymbol)

end BorceaBranden
end Challenges
end RealRooted
