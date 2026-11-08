module

import RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily
import RealRooted.ThreeTermRecurrence.ShiftedChebyshevRootRegions

/-!
# Shifted Chebyshev families with a perturbed first row

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "shifted-chebyshev-families"
formalized = "2026-11-01"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.constantLagFamily"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily"
label = "The constant-lag family P_{n+2} = (X + d) P_{n+1} - b² P_n with first row X + d + c"

[[definitions]]
name = "RealRooted.shiftedChebyshevFamily"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily"
label = "The shifted Chebyshev family (b, d) = (1, 2)"

[[definitions]]
name = "RealRooted.reflectedShiftedChebyshevFamily"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily"
label = "The coefficient reflection of the shifted Chebyshev family"

[[theorems]]
name = "RealRooted.constantLagFamily_strictInterl"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily"
label = "Consecutive rows of the constant-lag family interlace"
headline = true

[[theorems]]
name = "RealRooted.constantLagFamily_hasSimpleRoots"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily"
label = "The rows have simple roots"

[[theorems]]
name = "RealRooted.shiftedChebyshevFamily_coeff"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevRootRegions"
label = "Explicit binomial coefficients of the shifted Chebyshev family"

[[theorems]]
name = "RealRooted.shiftedChebyshevFamily_isRoot_nonpos_iff"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevRootRegions"
label = "Row n has only nonpositive roots exactly when c ≥ -1 - 1/n"
headline = true

[[theorems]]
name = "RealRooted.shiftedChebyshevFamily_isRoot_mem_Icc_iff"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevRootRegions"
label = "Row n has all roots in [-4, 0] exactly when |c| ≤ 1 + 1/n"
headline = true

[[theorems]]
name = "RealRooted.shiftedChebyshevFamily_strictInterl_parameter"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevRootRegions"
label = "The rows interlace in the parameter c"

[[theorems]]
name = "RealRooted.reflectedShiftedChebyshevFamily_eq_reflect"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily"
label = "The reflected family satisfies a quadratic-lag recurrence"

[[theorems]]
name = "RealRooted.reflectedShiftedChebyshevFamily_isRoot_neg_iff"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevRootRegions"
label = "The reflected row has only negative roots exactly when c ≥ -1 - 1/n"

[[theorems]]
name = "RealRooted.reflectedShiftedChebyshevFamily_isRoot_le_neg_quarter_iff"
module = "RealRooted.ThreeTermRecurrence.ShiftedChebyshevRootRegions"
label = "The reflected row has all roots ≤ -1/4 exactly when |c| ≤ 1 + 1/n"
-->

<!-- realrooted-catalog-content -->
# Shifted Chebyshev families with a perturbed first row

For real $b,d,c$ let $P_0=1$, $P_1=x+d+c$ and
$$
P_{n+2}=(x+d)\,P_{n+1}-b^2P_n .
$$
This is a Favard-type three-term recurrence with a perturbed first row. Each
$P_n$ is monic of degree $n$, and for $b\ne0$ every $P_n$ has simple roots and
consecutive rows interlace.

## The shifted Chebyshev case

For $(b,d)=(1,2)$ we obtain the shifted Chebyshev family $S_n^{(c)}$, with
$S_n^{(c)}(0)=n+1+nc$ and coefficients
$$
[x^k]S_n^{(c)}=\binom{n+k}{2k}+(1+c)\binom{n+k}{2k+1}.
$$
For $n\ge1$ the exact root windows are
$$
\text{all roots }\le0\iff c\ge-1-\tfrac1n,\qquad
\text{all roots in }[-4,0]\iff|c|\le1+\tfrac1n .
$$
For $c<d$ the row $S_{n+1}^{(d)}$ interlaces $S_{n+1}^{(c)}$, so the rows are
ordered in the parameter.

## The reflected family

The coefficient reflection $x^nS_n^{(c)}(1/x)$ satisfies the quadratic-lag
recurrence $Q_0=1$, $Q_1=1+(2+c)x$,
$$
Q_{n+2}=(1+2x)\,Q_{n+1}-x^2Q_n,
$$
has constant term $1$, is real-rooted, and has degree $n$ unless $n+1+nc=0$, when it
has degree $n-1$. Its roots are all negative exactly when $c\ge-1-1/n$, and all
roots are $\le-\tfrac14$ exactly when $|c|\le1+1/n$. The coefficients of $Q_n$ in
degree $1\le k\le n$ are
$\binom{2n-k}{k}+(1+c)\binom{2n-k}{k-1}$.

## What is new

These families arose from RealRooted issues #2290 and #2294; no published source is
cited, and we attribute none.

## References

No published source is cited for these results in the formalization. For the
Favard recurrence, see the [Favard page](/RealRooted/theorems/favard/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily` and
`RealRooted.ThreeTermRecurrence.ShiftedChebyshevRootRegions`.
-/
