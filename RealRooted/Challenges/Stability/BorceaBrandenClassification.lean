module

import RealRooted.BorceaBranden.RealFiniteClassificationIff
import RealRooted.BorceaBranden.Transcendental.ComplexClassification
import RealRooted.BorceaBranden.Transcendental.PivotForward
import RealRooted.BorceaBranden.Transcendental.RealClassification
import RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne

/-!
# Borcea--Brändén classification of stability preservers

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "borcea-branden-classification"
formalized = "2026-10-13"
tags = []
references = [
  "BorceaBranden2009I",
]
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
realStabilityOnDegreeBox_iff_rankTwo_or_stable_symbol"""
module = "RealRooted.BorceaBranden.RealFiniteClassificationIff"
label = "Real finite classification (Theorem 1.2)"
symcat = "borceaBrandenFiniteSymbol"

[[theorems]]
name = """RealRooted.BorceaBranden.\
complexStability_iff_rankOne_or_stableLimit_symbol"""
module = "RealRooted.BorceaBranden.Transcendental.ComplexClassification"
label = "Complex classification (Theorem 1.3)"

[[theorems]]
name = """RealRooted.BorceaBranden.\
realStability_iff_rankTwo_or_stableLimit_signedSymbol"""
module = "RealRooted.BorceaBranden.Transcendental.RealClassification"
label = "Real classification (Theorem 1.4)"
headline = true
symcat = "borceaBrandenTranscendentalSymbol"

[[theorems]]
name = "RealRooted.BorceaBranden.isComplexStableLimit_iff_fallingFactorial_glue_stable"
module = "RealRooted.BorceaBranden.Transcendental.PivotForward"
label = "Complex stable-limit criterion (Theorem 5.1)"

[[theorems]]
name = "RealRooted.BorceaBranden.isRealStableLimit_iff_forall_realGlue_stableOrZero"
module = "RealRooted.BorceaBranden.Transcendental.RealTheoremFiveOne"
label = "Real stable-limit criterion (Theorem 5.1)"
-->

<!-- realrooted-catalog-content -->
# Borcea–Brändén classification of stability preservers

A linear operator on polynomials in finitely many variables preserves stability if and only if
it has a stable rank-one or rank-two form, or its algebraic or transcendental symbol is stable
or a limit of stable polynomials.

## Results

A polynomial is *stable* if it has no zero with every variable in the open upper half-plane;
*real stable* means stable with real coefficients. Theorem numbers refer to
[@BorceaBranden2009I]. Throughout, the index set $\sigma$ of the variables is finite.

**Operator classes.**

- `PreservesRealStabilityOnDegreeBox`: a real-linear operator on the polynomials of degree at
  most $\kappa_i$ in each variable $x_i$ maps real stable polynomials to real stable polynomials
  or zero.
- `HasStableRankTwoRepresentation`: $Tf=\alpha(f)P+\beta(f)Q$ for linear functionals $\alpha,\beta$
  and real polynomials $P,Q$ such that every real linear combination of $P$ and $Q$ is real
  stable or zero.
- `PreservesComplexStability`: a complex-linear operator on the full polynomial ring maps stable
  polynomials to stable polynomials or zero.
- `HasGlobalStableRankOneRepresentation`: $T(f)=\alpha(f)P$ for a linear functional $\alpha$ and a
  stable polynomial $P$.
- `PreservesRealStability`: the real-linear analogue of `PreservesComplexStability`.
- `HasGlobalStableRankTwoRepresentation`: the full-ring version of the rank-two form.

**Symbols.**

- `transcendentalSymbolPolynomial`: the coefficient family $(-1)^{|\alpha|}T(z^\alpha)/\alpha!$ of
  the complex transcendental symbol, and `realTranscendentalSymbolPolynomial` the same family over
  the reals.
- `negRightFamily`: multiplies the coefficient indexed by $\alpha$ by $(-1)^{|\alpha|}$.
- `IsComplexStableLimit`: the family defines an entire series that is a locally uniform limit of
  stable-or-zero complex polynomials; `IsRealStableLimit` is the real version, with real stable
  polynomials.

**Theorem 1.2** (`realStabilityOnDegreeBox_iff_rankTwo_or_stable_symbol`). A
real-linear operator on a coordinatewise degree box preserves real stability if and only if it
has the stable rank-two form, its algebraic symbol is real stable, or its right-sign-reversed
algebraic symbol is real stable.

**Theorem 1.3** (`complexStability_iff_rankOne_or_stableLimit_symbol`). A
complex-linear operator on the full polynomial ring preserves stability if and only if it has the
stable rank-one form or its transcendental symbol belongs to `IsComplexStableLimit`.

**Theorem 1.4**
(`realStability_iff_rankTwo_or_stableLimit_signedSymbol`). A real-linear
operator on the full polynomial ring preserves real stability if and only if it has the stable
rank-two form, its transcendental symbol belongs to `IsRealStableLimit`, or its
right-sign-reversed transcendental symbol does.

**Theorem 5.1** (`isComplexStableLimit_iff_fallingFactorial_glue_stable`,
`isRealStableLimit_iff_forall_realGlue_stableOrZero`). A coefficient family $(P_\alpha)$ belongs to
`IsComplexStableLimit` if and only if every falling-factorial truncation
$\sum_{\alpha\le\beta}\prod_i\binom{\beta_i}{\alpha_i}\alpha_i!\,P_\alpha(z)\,w^\alpha$ is stable or
zero. The real statement holds with `IsRealStableLimit` and real stable-or-zero truncations.

**Erratum.** The proof of Theorem 5.6 in the paper uses an induction step claiming that partial
differentiation lowers by one the largest degree among the minimal support exponents; this fails
for a general support. We instead induct on the number of variables occurring in the support and
on its minimal total degree, using specialization and partial differentiation.

## References

[@BorceaBranden2009I].
<!-- /realrooted-catalog-content -->
-/
