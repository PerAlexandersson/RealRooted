import RealRooted.Applications.EulerianVariations.CyclicPathDescents
import RealRooted.Applications.EulerianVariations.PeakValues
import RealRooted.Applications.EulerianVariations.TernaryRuns

/-!
# Eulerian variations challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "eulerian-variations"
authors = ["Alexandersson"]
years = [2026]

[[definitions]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"

[[definitions]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns.Recurrence"

[[definitions]]
name = "RealRooted.peakValuePolynomial"
module = "RealRooted.CombinatorialExamples.PeakValues"

[[theorems]]
name = """RealRooted.Applications.EulerianVariations.\
cyclicPathDescentPolynomial_simple_root_description"""
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial_eq_derivative"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.peakValuePolynomial_stable"
module = "RealRooted.Applications.EulerianVariations.PeakValues"

[[theorems]]
name = """RealRooted.Applications.EulerianVariations.\
peakValueWeightedDiagonal_consecutive_strictInterl"""
module = "RealRooted.Applications.EulerianVariations.PeakValues"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_isPF"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_strictInterl"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"
-->

<!-- realrooted-catalog-content -->
# Real-rooted Eulerian variations

Three Eulerian-type families from permutations, words and paths are
formalized as real-rooted.

- **Cyclic path descents:** the polynomial with coefficients
  `2 C(n,k) C(n-1,k-1)` equals `(2/n) x N_n'(x)`, where `N_n` is the
  Narayana polynomial. Its zeros are simple: `0`, together with `n - 1`
  negative zeros.
- **Peak values:** the multivariate peak-value polynomial is real stable.
  For every choice of positive weights, consecutive weighted diagonals
  strictly interlace.
- **Ternary runs:** the ternary run polynomials are PF polynomials, and
  consecutive ones strictly interlace.

The combinatorial interpretations are cited from the paper; the formalized
objects are the polynomial families.

## References

P. Alexandersson, [“Real-rooted Eulerian polynomials from permutations,
words, and paths,”](https://arxiv.org/abs/2609.07325) arXiv:2609.07325 (2026).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Applications.EulerianVariations`.
-/
