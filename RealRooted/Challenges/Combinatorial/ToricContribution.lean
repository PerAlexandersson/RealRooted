module

import RealRooted.ParkingFunctions.ToricContribution.CommonInterlacer
import RealRooted.ParkingFunctions.ToricContribution.ContributionReversal

/-!
# Toric g-contribution polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "toric-g-contributions"
formalized = "2026-09-02"
tags = []
references = [
  "Xiao2026x",
]
authors = ["Xiao"]
years = [2026]

[[definitions]]
name = "RealRooted.ParkingFunctions.ToricContribution.toricContribution"
module = "RealRooted.ParkingFunctions.ToricContribution.ContributionReversal"
label = "Toric g-contribution polynomial"

[[definitions]]
name = "RealRooted.ParkingFunctions.ToricContribution.toricContributionRow"
module = "RealRooted.ParkingFunctions.ToricContribution.ContributionReversal"
label = "A row of toric g-contribution polynomials"

[[definitions]]
name = "RealRooted.IsInterlacingSeq"
module = "RealRooted.InterlacingSequenceBasic"
label = "Interlacing sequence"

[[definitions]]
name = "RealRooted.ParkingFunctions.ToricContribution.rPolynomial"
module = "RealRooted.ParkingFunctions.ToricContribution.Definitions"
label = "Hypergeometric polynomials R_d"

[[definitions]]
name = "RealRooted.ParkingFunctions.ToricContribution.normalizedRPolynomialFamily"
module = "RealRooted.ParkingFunctions.ToricContribution.CommonInterlacer"
label = "The sign-normalized family of the R_d"

[[definitions]]
name = "RealRooted.HasCommonLeftInterleaver"
module = "RealRooted.CommonInterleaver.RootDesc"
label = "Common left interleaver"

[[definitions]]
name = "RealRooted.ParkingFunctions.ToricContribution.weightedNormalizedReversedContributionFamily"
module = "RealRooted.ParkingFunctions.ToricContribution.ContributionReversal"
label = "Weighted normalized reversed contributions"

[[theorems]]
name = "RealRooted.ParkingFunctions.ToricContribution.toricContributionRow_isInterlacingSeq"
module = "RealRooted.ParkingFunctions.ToricContribution.ContributionReversal"
label = "Xiao's conjecture: toric contribution rows are interlacing sequences"
headline = true

[[theorems]]
name = """RealRooted.ParkingFunctions.ToricContribution.normalizedRPolynomialFamily_\
hasCommonLeftInterleaver"""
module = "RealRooted.ParkingFunctions.ToricContribution.CommonInterlacer"
label = "The R_d have a common interleaver"

[[theorems]]
name = """RealRooted.ParkingFunctions.ToricContribution.\
weightedNormalizedReversedContributionFamily_sum_splits"""
module = "RealRooted.ParkingFunctions.ToricContribution.ContributionReversal"
label = "Positive weighted sums of normalized reversed contributions are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Toric g-contribution polynomials

Each row of the toric $g$-contribution polynomials is an interlacing sequence, as conjectured by
Xiao.

## Results

A list $(f_0,\dots,f_k)$ is an *interlacing sequence* if $f_i\ll f_j$ for all $i<j$, not only
for consecutive indices. For $n=2m+\varepsilon$ with $\varepsilon\in\{0,1\}$ and $0\le j\le m$, the
toric $g$-contribution polynomial is
$$
g_{n,j}(x)=\sum_{k=0}^{m}\binom{n-k}{k}\,C_{n-j-k}\,(x-1)^k,
$$
where $C_i$ is the Catalan number.

**Theorem (Xiao's conjecture).** [@Xiao2026x, Conj. 4.2] For all $m\ge0$ and
$\varepsilon\in\{0,1\}$, the row $(g_{n,0},g_{n,1},\dots,g_{n,m})$ is an interlacing sequence.

**Theorem (common interleaver).** Let $m\ge1$ and $\varepsilon\in\{0,1\}$, and let
$(a)_k=a(a+1)\dotsm(a+k-1)$. For $0\le d\le m$ let
$$
\rho_d(x)=\sum_{k=0}^{m}(-1)^k\binom{m+\varepsilon+k}{m-k}\,C_{d+\varepsilon+k}\,x^k
=\binom{m+\varepsilon}{m}C_{d+\varepsilon}\,R_d(x),
$$
where $R_d(x)=\sum_{k\le m}r_kx^k$ is the terminating ${}_3F_2$-type polynomial with
$$
r_k=\frac{(-m)_k\,(m+1+\varepsilon)_k\,(\varepsilon+\tfrac12+d)_k}
{(\varepsilon+\tfrac12)_k\,(\varepsilon+\tfrac52+d)_k\,k!}.
$$
The polynomials $(-1)^mR_d$, $0\le d\le m$, have a common left interleaver, a Jacobi-type
polynomial of degree $m-1$. For all weights $w_d>0$, $0\le d\le m$, the polynomial
$\sum_d w_d\,(-1)^m\rho_d$ is real-rooted.

## Proof

The reversal $y^m\,g_{n,m-d}(1+1/y)$ is $\rho_d(-y)$.
The polynomials $(-1)^mR_d$ interlace pairwise, larger $d$ first, and this interlacing is carried
to the $g_{n,j}$ by the reversal and the shift $x\mapsto x-1$. A common left interleaver makes
every positive combination real-rooted.

## References

[@Xiao2026x]. Common interleavers are described on the
[common interleaver page](rr:common-interleavers). See also the
[toric $g$-contribution polynomial](sf:toricGContributionPolynomial) on symmetricfunctions.com;
Xiao's cross-size interlacing theorem there is a different statement.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.ParkingFunctions.ToricContribution`.
-/
