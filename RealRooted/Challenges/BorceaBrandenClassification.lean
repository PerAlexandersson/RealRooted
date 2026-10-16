module

public import RealRooted.BorceaBranden.RealFiniteClassificationIff
public import RealRooted.BorceaBranden.Transcendental.ComplexClassification
public import RealRooted.BorceaBranden.Transcendental.PivotForward
public import RealRooted.BorceaBranden.Transcendental.RealClassification
public import RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne

/-!
# Borcea--Brändén classification of stability preservers

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "borcea-branden-classification"
formalized = "2026-10-13"
authors = ["Borcea", "Brändén"]
years = [2009]

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesRealStabilityOnDegreeBox"
module = "RealRooted.BorceaBranden.RealFiniteClassification"
label = "Real stability preserver on a degree box"

[[definitions]]
name = "RealRooted.BorceaBranden.HasStableRankTwoRepresentation"
module = "RealRooted.BorceaBranden.RealFiniteClassification"
label = "Stable rank-at-most-two degree-box representation"

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesComplexStability"
module = "RealRooted.BorceaBranden.Transcendental.ComplexClassification"
label = "Complex stability preserver"

[[definitions]]
name = "RealRooted.BorceaBranden.HasGlobalStableRankOneRepresentation"
module = "RealRooted.BorceaBranden.Transcendental.ComplexClassification"
label = "Stable rank-at-most-one representation"

[[definitions]]
name = "RealRooted.BorceaBranden.PreservesRealStability"
module = "RealRooted.BorceaBranden.Transcendental.RealOperatorBasics"
label = "Real stability preserver"

[[definitions]]
name = "RealRooted.BorceaBranden.HasGlobalStableRankTwoRepresentation"
module = "RealRooted.BorceaBranden.Transcendental.RealOperatorBasics"
label = "Stable rank-at-most-two representation"

[[definitions]]
name = "RealRooted.BorceaBranden.IsComplexStableLimit"
module = "RealRooted.BorceaBranden.Transcendental.TranscendentalSymbol"
label = "Complex stable-limit class"

[[definitions]]
name = "RealRooted.BorceaBranden.IsRealStableLimit"
module = "RealRooted.BorceaBranden.Transcendental.TranscendentalSymbol"
label = "Real stable-limit class"

[[definitions]]
name = "RealRooted.BorceaBranden.transcendentalSymbolPolynomial"
module = "RealRooted.BorceaBranden.Transcendental.TranscendentalSymbol"
label = "Complex transcendental-symbol coefficient family"

[[definitions]]
name = "RealRooted.BorceaBranden.realTranscendentalSymbolPolynomial"
module = "RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne"
label = "Real transcendental-symbol coefficient family"

[[definitions]]
name = "RealRooted.BorceaBranden.negRightFamily"
module = "RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne"
label = "Right-sign reversal of a coefficient family"

[[theorems]]
name = """RealRooted.BorceaBranden.\
preservesRealStabilityOnDegreeBox_iff_rankTwo_or_symbol_or_negRight"""
module = "RealRooted.BorceaBranden.RealFiniteClassificationIff"
label = "Real finite classification (Theorem 1.2)"
headline = true

[[theorems]]
name = """RealRooted.BorceaBranden.\
preservesComplexStability_iff_rankOne_or_transcendentalSymbol_stableLimit"""
module = "RealRooted.BorceaBranden.Transcendental.ComplexClassification"
label = "Complex classification (Theorem 1.3)"
headline = true

[[theorems]]
name = """RealRooted.BorceaBranden.\
preservesRealStability_iff_rankTwo_or_signedTranscendentalSymbol_stableLimit"""
module = "RealRooted.BorceaBranden.Transcendental.RealClassification"
label = "Real classification (Theorem 1.4)"
headline = true

[[theorems]]
name = "RealRooted.BorceaBranden.isComplexStableLimit_iff_forall_fallingFactorial_glue_stableOrZero"
module = "RealRooted.BorceaBranden.Transcendental.PivotForward"
label = "Complex stable-limit criterion (Theorem 5.1)"
headline = true

[[theorems]]
name = "RealRooted.BorceaBranden.isRealStableLimit_iff_forall_realGlue_stableOrZero"
module = "RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne"
label = "Real stable-limit criterion (Theorem 5.1)"
headline = true
-->

<!-- realrooted-catalog-content -->
# Borcea–Brändén classification of stability preservers

A multivariate polynomial is stable if it does not vanish when every variable
lies in the open upper half-plane.

`PreservesRealStabilityOnDegreeBox` means that a real-linear operator sends
each real stable polynomial in a fixed coordinatewise degree box to a real
stable polynomial or zero.

`HasStableRankTwoRepresentation` means that the image lies in the real span
of two polynomials whose every real linear combination is stable or zero.

`PreservesComplexStability` means that a complex-linear operator on the full
polynomial ring sends each stable polynomial to a stable polynomial or zero.

`HasGlobalStableRankOneRepresentation` means that the operator has the form
$T(f)=\alpha(f)P$ for a fixed stable polynomial $P$.

`PreservesRealStability` is the corresponding preservation property for a
real-linear operator on the full real polynomial ring.

`HasGlobalStableRankTwoRepresentation` is the full-ring version of the stable
rank-at-most-two range condition.

`transcendentalSymbolPolynomial` is the coefficient family
$(-1)^{|\alpha|}T(z^\alpha)/\alpha!$ of the complex transcendental symbol.

`realTranscendentalSymbolPolynomial` is the same coefficient family over the
reals.

`negRightFamily` multiplies the coefficient indexed by $\alpha$ by
$(-1)^{|\alpha|}$.

`IsComplexStableLimit` consists of entire series that are locally uniform
limits of complex stable-or-zero polynomials.

`IsRealStableLimit` consists of entire real-coefficient series that are
locally uniform limits of real stable polynomials.

Theorem 1.2 is
`preservesRealStabilityOnDegreeBox_iff_rankTwo_or_symbol_or_negRight`: a
real-linear operator on a coordinatewise degree box preserves real stability
if and only if it has the stable rank-at-most-two form, its algebraic symbol is
real stable, or its right-sign-reversed algebraic symbol is real stable.

Theorem 1.3 is
`preservesComplexStability_iff_rankOne_or_transcendentalSymbol_stableLimit`: a
complex-linear operator on the full polynomial ring preserves stability if and
only if it has the stable rank-at-most-one form or its transcendental symbol
belongs to `IsComplexStableLimit`.

Theorem 1.4 is
`preservesRealStability_iff_rankTwo_or_signedTranscendentalSymbol_stableLimit`:
a real-linear operator on the full polynomial ring preserves real stability if
and only if it has the stable rank-at-most-two form, its transcendental symbol
belongs to `IsRealStableLimit`, or its right-sign-reversed transcendental
symbol belongs to that class.

The complex part of Theorem 5.1 is
`isComplexStableLimit_iff_forall_fallingFactorial_glue_stableOrZero`: a complex
coefficient family belongs to `IsComplexStableLimit` if and only if every
falling-factorial truncation is stable or zero. The real part is
`isRealStableLimit_iff_forall_realGlue_stableOrZero`, with real stable limits
and real stable-or-zero truncations.

The proof of Theorem 5.6 in the paper uses an induction step claiming that
partial differentiation lowers by one the largest degree among the minimal
support exponents; this fails for a general support. We instead induct on the
number of variables occurring in the support and on its minimal total degree,
using specialization and partial differentiation.

## References

J. Borcea and P. Brändén,
[“The Lee–Yang and Pólya–Schur programs. I. Linear operators preserving
stability,”](https://arxiv.org/abs/0809.0401) *Invent. Math.* 177
(2009), 541–569,
[doi:10.1007/s00222-009-0189-3](https://doi.org/10.1007/s00222-009-0189-3),
[arXiv:0809.0401](https://arxiv.org/abs/0809.0401).
<!-- /realrooted-catalog-content -->
-/

public section

namespace RealRooted.Challenges.BorceaBrandenClassification

end RealRooted.Challenges.BorceaBrandenClassification
