import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol
import RealRooted.BorceaBranden.FiniteSymbolClassification
import RealRooted.BorceaBranden.UnivariateFiniteSymbol

/-!
# Borcea--Branden finite-symbol classification challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "borcea-branden"

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesComplexStabilityOnDegreeBox"
module = "RealRooted.BorceaBranden.FiniteSymbolClassification"

[[definitions]]
name = "RealRooted.BorceaBranden.HasStableRankOneRepresentation"
module = "RealRooted.BorceaBranden.FiniteSymbolClassification"

[[definitions]]
name = "RealRooted.BorceaBranden.finiteAlgebraicSymbol"
module = "RealRooted.BorceaBranden.UnivariateFiniteSymbol"

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesRealRootedUpTo"
module = "RealRooted.BorceaBranden.UnivariateFiniteSymbol"

[[theorems]]
name = "RealRooted.BorceaBranden.finiteComplexSymbolClassification"
module = "RealRooted.BorceaBranden.FiniteSymbolClassification"

[[theorems]]
name = "RealRooted.BorceaBranden.finiteSymbolTheorem"
module = "RealRooted.BorceaBranden.Applications.RealUnivariateSymbol"

[[theorems]]
name = "RealRooted.BorceaBranden.finiteSymbol_preservesRealRootedUpTo"
module = "RealRooted.BorceaBranden.Applications.RealUnivariateSymbol"
-->

<!-- realrooted-catalog-content -->
# Borcea–Brändén finite-symbol theorems

For a linear operator restricted to a finite multidegree box, the complex
classification gives the two alternatives: a stable rank-one representation,
or stability of the algebraic symbol.  The real univariate application proves
the positive-symbol implication for operators on polynomials of bounded
degree.  These are checked theorem witnesses derived from the multivariate
stability and polarization development, not conditional statement wrappers.

## References

J. Borcea and P. Brändén, “The Lee–Yang and Pólya–Schur programs. I. Linear
operators preserving stability,” *Inventiones Mathematicae* 177 (2009),
541–569.  See the
[finite-symbol discussion on symmetricfunctions.com](https://www.symmetricfunctions.com/stablePolynomials.htm#borceaBrandenFiniteSymbol).
<!-- /realrooted-catalog-content -->

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
    finiteSymbolTheorem
    finiteSymbol_preservesRealRootedUpTo)

end BorceaBranden
end Challenges
end RealRooted
