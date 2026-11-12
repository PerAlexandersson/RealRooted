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
authors = []
references = []
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

Rows of a constant-lag three-term recurrence with a perturbed first row interlace, and for the
shifted Chebyshev case the root windows are exact in the perturbation.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.

**Theorem (constant-lag family).** For real $b,d,c$ let $P_0=1$, $P_1=x+d+c$ and
$$
P_{n+2}=(x+d)\,P_{n+1}-b^2P_n .
$$
Each $P_n$ is monic of degree $n$. If $b\ne0$, then every $P_n$ has simple real roots and
$P_n\ll P_{n+1}$ for all $n$.

**Theorem (shifted Chebyshev case).** Let $S_n^{(c)}$ be the family with $(b,d)=(1,2)$. Then
$S_n^{(c)}(0)=n+1+nc$ and
$$
[x^k]S_n^{(c)}=\binom{n+k}{2k}+(1+c)\binom{n+k}{2k+1}.
$$
For $n\ge1$,
$$
\text{all roots of }S_n^{(c)}\le0\iff c\ge-1-\tfrac1n,\qquad
\text{all roots in }[-4,0]\iff|c|\le1+\tfrac1n .
$$
For $c<d$ and $n\ge1$ we have $S_n^{(d)}\ll S_n^{(c)}$.

**Theorem (reflected family).** Let $Q_n^{(c)}=x^nS_n^{(c)}(1/x)$. Then $Q_0=1$,
$Q_1=1+(2+c)x$ and
$$
Q_{n+2}=(1+2x)\,Q_{n+1}-x^2Q_n .
$$
Each $Q_n$ has constant term $1$ and is real-rooted. It has degree $n$ unless $n+1+nc=0$, and
then, for $n\ge1$, it has degree $n-1$. For $1\le k\le n$,
$$
[x^k]Q_n^{(c)}=\binom{2n-k}{k}+(1+c)\binom{2n-k}{k-1}.
$$
For $n\ge1$, all roots of $Q_n^{(c)}$ are negative if and only if $c\ge-1-1/n$, and all are
at most $-\tfrac14$ if and only if $|c|\le1+1/n$.

## References

The three-term recurrence is of Favard type; see the [Favard page](/RealRooted/theorems/favard/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.ThreeTermRecurrence.ShiftedChebyshevFamily` and
`RealRooted.ThreeTermRecurrence.ShiftedChebyshevRootRegions`.
-/
