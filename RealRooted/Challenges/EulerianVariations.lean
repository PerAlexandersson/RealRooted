import RealRooted.Applications.EulerianVariations.CyclicPathDescents
import RealRooted.Applications.EulerianVariations.TernaryRuns
import RealRooted.CombinatorialExamples.PeakValues.WeightedInterleaving
import RealRooted.CombinatorialExamples.SuperEulerian

/-!
# Eulerian variations challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "eulerian-variations"
formalized = "2026-09-09"
references = [
  "Alexandersson2026Eulerian",
]
authors = ["Alexandersson", "Shankar"]
years = [2026]

[[definitions]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"
label = "Cyclic path descent polynomial"

[[definitions]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns.Recurrence"
label = "Ternary run polynomial"

[[definitions]]
name = "RealRooted.peakValuePolynomial"
module = "RealRooted.CombinatorialExamples.PeakValues"
label = "Multivariate peak-value polynomial"

[[definitions]]
name = "RealRooted.SuperEulerian.superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "Super-Eulerian polynomial"

[[theorems]]
name = """RealRooted.Applications.EulerianVariations.\
cyclicPathDescentPolynomial_simple_root_description"""
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"
label = "Zeros of the cyclic path descent polynomial"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial_eq_derivative"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"
label = "Cyclic path descents via the Narayana derivative"

[[theorems]]
name = "RealRooted.peakValuePolynomial_mvRealStable"
module = "RealRooted.CombinatorialExamples.PeakValues.Stability"
label = "The peak-value polynomial is real stable"
headline = true

[[theorems]]
name = "RealRooted.peakValueWeightedDiagonal_consecutive_strictInterl"
module = "RealRooted.CombinatorialExamples.PeakValues.WeightedInterleaving"
label = "Weighted peak-value diagonals interlace"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_isPF"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"
label = "Ternary run polynomials are PF"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_strictInterl"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"
label = "Consecutive ternary run polynomials interlace"

[[theorems]]
name = "RealRooted.SuperEulerian.isRealRooted_superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "Super-Eulerian polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.SuperEulerian.strictInterl_superEulerian_succ"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "Consecutive super-Eulerian polynomials interlace"

[[theorems]]
name = "RealRooted.SuperEulerian.exists_gamma_superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "Super-Eulerian gamma-polynomials are real-rooted and nonnegative"
-->

<!-- realrooted-catalog-content -->
# Real-rooted Eulerian variations

Four Eulerian-type families, coming from permutations, words and paths, are
real-rooted.

- **Cyclic path descents:** the polynomial with coefficients
  $2\binom{n}{k}\binom{n-1}{k-1}$ equals $\tfrac{2}{n}\, x B_n'(x)$, where
  $B_n(x) = \sum_k \binom{n}{k}^2 x^k$ is the type-B Narayana polynomial
  (`narayanaPolynomial 0 n`). Its zeros are simple: $0$, together with $n - 1$
  negative zeros.
- **Peak values:** the multivariate peak-value polynomial is real stable.
  For every choice of positive weights, consecutive weighted diagonals
  interlace.
- **Ternary runs:** the ternary run polynomials are PF polynomials, and
  consecutive ones interlace.

- **Super-Eulerian polynomials:** consecutive rows interlace, and their
  gamma-polynomials are real-rooted with nonnegative coefficients.

This page states the polynomial results. `Challenges.EulerianCompendium`
collects the full paper statements, including the public proofs identifying
the cyclic and ternary models with their actual word enumerators.

## References

See [@Alexandersson2026Eulerian].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Applications.EulerianVariations`.
-/
