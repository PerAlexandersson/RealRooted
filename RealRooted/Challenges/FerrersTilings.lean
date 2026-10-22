import RealRooted.FerrersTiling.AnchorRefined
import RealRooted.FerrersTiling.FaultFreeRectangle
import RealRooted.FerrersTiling.FaultLines
import RealRooted.FerrersTiling.LTiling
import RealRooted.FerrersTiling.RowRefined

/-!
# Algebraic Ferrers-tiling polynomial families

<!-- realrooted-catalog
version = 1
section = "families"
slug = "ferrers-tilings"
formalized = "2026-10-22"
references = [
  "AhlbergAlexandersson2026",
  "ChudnovskySeymour2007",
]
authors = ["Ahlberg", "Alexandersson"]
years = [2026]

[[definitions]]
name = "RealRooted.FerrersTiling.anchorRefinedPolynomial"
module = "RealRooted.FerrersTiling.AnchorRefined"
label = "Terminal-state-refined anchor polynomial"

[[definitions]]
name = "RealRooted.FerrersTiling.anchorRefinedTotal"
module = "RealRooted.FerrersTiling.AnchorRefined"
label = "Unrefined anchor polynomial"

[[definitions]]
name = "RealRooted.FerrersTiling.lTilingPolynomial"
module = "RealRooted.FerrersTiling.LTiling"
label = "L-tile polynomial"

[[definitions]]
name = "RealRooted.FerrersTiling.twoColumnPolynomial"
module = "RealRooted.FerrersTiling.TwoColumn"
label = "Two-column tiling polynomial"

[[definitions]]
name = "RealRooted.FerrersTiling.faultLinePolynomial"
module = "RealRooted.FerrersTiling.FaultLines"
label = "Two-column fault-line polynomial"

[[definitions]]
name = "RealRooted.FerrersTiling.rectangleFaultFreePolynomial"
module = "RealRooted.FerrersTiling.FaultFreeRectangle"
label = "Fault-free rectangle polynomial"

[[definitions]]
name = "RealRooted.FerrersTiling.rigidPolynomial"
module = "RealRooted.FerrersTiling.Rigid"
label = "Rigid-tile polynomial"

[[definitions]]
name = "RealRooted.FerrersTiling.rowRefinedSpecialization"
module = "RealRooted.FerrersTiling.RowRefined"
label = "Row-refined univariate specialization"

[[theorems]]
name = "RealRooted.FerrersTiling.anchorRefined_interlacing"
module = "RealRooted.FerrersTiling.AnchorRefined"
label = "Refined anchor-polynomial vectors are interlacing"
headline = true

[[theorems]]
name = "RealRooted.FerrersTiling.anchorRefinedTotal_splits"
module = "RealRooted.FerrersTiling.AnchorRefined"
label = "Unrefined anchor polynomials are real-rooted"

[[theorems]]
name = "RealRooted.FerrersTiling.lTilingPolynomial_splits"
module = "RealRooted.FerrersTiling.LTiling"
label = "L-tile polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.FerrersTiling.twoColumnPolynomial_interl_succ"
module = "RealRooted.FerrersTiling.TwoColumn"
label = "Consecutive two-column polynomials interlace"
headline = true

[[theorems]]
name = "RealRooted.FerrersTiling.faultLinePolynomial_splits"
module = "RealRooted.FerrersTiling.FaultLines"
label = "Fault-line polynomials are real-rooted"

[[theorems]]
name = "RealRooted.FerrersTiling.rectangleFaultFreePolynomial_interl"
module = "RealRooted.FerrersTiling.FaultFreeRectangle"
label = "Consecutive fault-free rectangle polynomials interlace"

[[theorems]]
name = "RealRooted.FerrersTiling.rigidPolynomial_isPFPolynomial"
module = "RealRooted.FerrersTiling.Rigid"
label = "Rigid-tile polynomials are Pólya-frequency"
headline = true

[[theorems]]
name = "RealRooted.FerrersTiling.rowRefinedSpecialization_splits"
module = "RealRooted.FerrersTiling.RowRefined"
label = "Row-refined specializations are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Polynomials from tilings of rectangles

Ahlberg and Alexandersson associate several polynomial families with tilings
of rectangles by Ferrers shapes.  At this algebraic layer we define the
families by the recurrences and coefficient formulas from the paper; the
tiling bijections are separate combinatorial statements.

The terminal-state-refined anchor polynomials obey the paper's transfer
matrix: the row for $\infty$ consists of ones, while row $j$ consists of $t$
in the columns before $j$ and zeroes thereafter.  The library's zero-aware
matrix-preserver theorem proves that every resulting vector is an interlacing
sequence [@AhlbergAlexandersson2026, Thm. 3.5].

For a two-column tile and parameter $d$, the polynomial of width $n$ is

$$
P_n(t)=\sum_j \binom{n-j}{j}d^j t^j.
$$

It satisfies $P_{n+2}=P_{n+1}+dtP_n$, is real-rooted, and satisfies
$P_n\preceq P_{n+1}$ [@AhlbergAlexandersson2026, Thm. 4.1].  Reversing its
coefficients gives the fault-line family
$R_{n+2}=tR_{n+1}+dtR_n$, which is also real-rooted.

For a rigid tile of width $\ell+1$, the polynomial is

$$
P_{d,\ell,n}(t)=\sum_j \binom{d(n-j\ell)}{j}t^j.
$$

This is the path-power polynomial
`pathPowerCliquePolynomial (d * ell + 1) (d * n)`.  Powers of paths are
claw-free, so the Chudnovsky--Seymour theorem makes the polynomial
Pólya-frequency; in particular all its zeros are real and nonpositive
[@AhlbergAlexandersson2026, Thm. 5.3].

The fault-free rectangle polynomial is another path-power polynomial.  Its
closed coefficients give the paper's bars-and-stars formula, its path
deletion recurrence is $B_d=B_{d-1}+tB_{d-k}$, and consecutive members
interlace [@AhlbergAlexandersson2026, Lem. 6.3].  Finally, the univariate
row-refined specialization

$$
\sum_j \binom{n-j}{j}(s+d-1)^j
$$

is a translate of a path-power polynomial and is therefore real-rooted
[@AhlbergAlexandersson2026, Thm. 7.1].

## Proof idea

All four families are identified with independence polynomials of powers of
paths, possibly after a positive scaling, translation, or coefficient
reversal.  The library's path-power theory supplies both real-rootedness and
interlacing; reflection preserves splitting.

## References

The families and formulas are from [@AhlbergAlexandersson2026].  The
real-rootedness engine for path-power independence polynomials is the
claw-free independence-polynomial theorem of [@ChudnovskySeymour2007].
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.FerrersTilings

end RealRooted.Challenges.FerrersTilings
