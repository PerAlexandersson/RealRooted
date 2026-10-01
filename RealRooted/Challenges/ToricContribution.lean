import RealRooted.ParkingFunctions.ToricContribution.CommonInterlacer
import RealRooted.ParkingFunctions.ToricContribution.ContributionReversal

/-!
# Toric g-contribution challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "toric-g-contributions"
authors = ["Xiao"]
years = [2026]

[[definitions]]
name = "RealRooted.ParkingFunctions.ToricContribution.toricContribution"
module = "RealRooted.ParkingFunctions.ToricContribution.ContributionReversal"
label = "Toric g-contribution polynomial"

[[definitions]]
name = "RealRooted.ParkingFunctions.ToricContribution.rPolynomial"
module = "RealRooted.ParkingFunctions.ToricContribution.Definitions"
label = "Hypergeometric polynomials R_d"

[[theorems]]
name = "RealRooted.ParkingFunctions.ToricContribution.toricContributionRow_isInterlacingSeq"
module = "RealRooted.ParkingFunctions.ToricContribution.ContributionReversal"
label = "Xiao's Conjecture 4.2"

[[theorems]]
name = """RealRooted.ParkingFunctions.ToricContribution.\
normalizedRPolynomialFamily_hasCommonLeftInterleaver"""
module = "RealRooted.ParkingFunctions.ToricContribution.CommonInterlacer"
label = "The R_d have a common interleaver"

[[theorems]]
name = """RealRooted.ParkingFunctions.ToricContribution.\
weightedNormalizedReversedContributionFamily_sum_splits"""
module = "RealRooted.ParkingFunctions.ToricContribution.ContributionReversal"
label = "Positive weighted sums are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Toric g-contribution polynomials

Xiao studies the toric $g$-contribution polynomials $g_{n,j}(x)$, whose
coefficients are built from binomial coefficients and Catalan numbers.
Xiao's Conjecture 4.2 states that, for each $n = 2m + \varepsilon$ with $\varepsilon \in \{0, 1\}$,
the row $(g_{n,0}, g_{n,1}, \dotsc, g_{n,\lfloor n/2\rfloor})$ is an interlacing sequence.

**Theorem (Xiao's Conjecture 4.2).** For all $m$ and $\varepsilon \leq 1$, the toric
contribution row is an interlacing sequence.

The proof finds a common left interleaver for the normalized family: the
terminating hypergeometric polynomials $R_d$ share a Jacobi-type interlacer.
It follows that every strictly positive weighted sum of the normalized
reversed contributions is real-rooted.

## References

Q. Xiao, [“The real-rootedness of the toric g-contribution
polynomials,”](https://arxiv.org/abs/2609.01086) arXiv:2609.01086 (2026).
Common interleavers are described on the
[common interleaver page](/RealRooted/concepts/common-interleavers/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.ParkingFunctions.ToricContribution`.
-/
