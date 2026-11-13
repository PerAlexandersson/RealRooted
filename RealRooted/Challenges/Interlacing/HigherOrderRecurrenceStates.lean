module

import RealRooted.Recurrence.CubicTransition
import RealRooted.Recurrence.PFTripleMatrix
import RealRooted.Recurrence.QuarticInterlacing
import RealRooted.Recurrence.ResidueSubsequence

/-!
# Interlacing rows of cubic and quartic recurrences from ordered PF states

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "higher-order-recurrence-states"
formalized = "2026-11-03"
authors = []
tags = ["realrooted-original"]
references = [
  "Wagner1992",
]

[[definitions]]
name = "RealRooted.IsOrderedPFTriple"
module = "RealRooted.Recurrence.CubicTransition"
label = "Ordered PF triple"

[[definitions]]
name = "RealRooted.PreservesCubicTransition"
module = "RealRooted.Recurrence.CubicTransition"
label = "The cubic transition preserves ordered PF triples"

[[definitions]]
name = "RealRooted.PreservesPFTriple"
module = "RealRooted.Recurrence.PFTripleMatrix"
label = "The matrix [[0,0,1],[x,0,1],[cx,dx,a+bx]] preserves ordered PF triples"

[[definitions]]
name = "RealRooted.PreservesScaledPFTriple"
module = "RealRooted.Recurrence.PFTripleMatrix"
label = "The scaled matrix [[0,0,1],[lx,0,1],[cx,dx,a+bx]] preserves ordered PF triples"

[[definitions]]
name = "RealRooted.cubicTransitionFamily"
module = "RealRooted.Recurrence.CubicTransition"
label = "The row family of the cubic transition"

[[definitions]]
name = "RealRooted.quarticInterlacingStep"
module = "RealRooted.Recurrence.QuarticInterlacing"
label = "One step of the five-coordinate quartic state"

[[definitions]]
name = "RealRooted.QuarticInterlacingState.IsAdmissible"
module = "RealRooted.Recurrence.QuarticInterlacing"
label = "Admissible quartic state: PF coordinates, seven comparisons and a balance identity"

[[definitions]]
name = "RealRooted.quarticInterlacingRow"
module = "RealRooted.Recurrence.QuarticInterlacing"
label = "The row sequence of an iterated quartic state"

[[theorems]]
name = "RealRooted.PreservesCubicTransition.iff_nonneg"
module = "RealRooted.Recurrence.CubicTransition"
label = "The cubic transition preserves ordered PF triples iff its three parameters are nonnegative"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_interl_add_one"
module = "RealRooted.Recurrence.CubicTransition"
label = "Consecutive rows of the cubic family interlace"

[[theorems]]
name = "RealRooted.interl_quarticInterlacingRow_succ"
module = "RealRooted.Recurrence.QuarticInterlacing"
label = "Consecutive rows of an admissible quartic state interlace"

[[theorems]]
name = "RealRooted.PreservesPFTriple.iff"
module = "RealRooted.Recurrence.PFTripleMatrix"
label = "The three-coordinate matrix preserves ordered PF triples iff a, b, d ≥ 0 and c ≥ a"

[[theorems]]
name = "RealRooted.PreservesScaledPFTriple.iff"
module = "RealRooted.Recurrence.PFTripleMatrix"
label = "The scaled matrix preserves ordered PF triples iff a, b, d ≥ 0 and c ≥ a l"
headline = true

[[theorems]]
name = "RealRooted.isOrderedPFTriple_of_recurrence"
module = "RealRooted.Recurrence.PFTripleMatrix"
label = "Third-order recurrences with a, b, d ≥ 0 and e ≥ a + d have PF rows and ordered states"

[[theorems]]
name = "RealRooted.interl_of_recurrence"
module = "RealRooted.Recurrence.PFTripleMatrix"
label = "Consecutive rows of such a third-order recurrence interlace"

[[theorems]]
name = "RealRooted.isOrderedPFTriple_of_recurrence_scaled"
module = "RealRooted.Recurrence.PFTripleMatrix"
label = "The scaled state: a κ² − e κ + d ≤ 0 for some κ > 0 suffices"

[[theorems]]
name = "RealRooted.PreservesCubicTransition.of_nonneg"
module = "RealRooted.Recurrence.CubicTransition"
label = "Nonnegative parameters make the cubic transition preserve ordered PF triples"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_recurrence"
module = "RealRooted.Recurrence.CubicTransition"
label = "The cubic family satisfies a constant-coefficient cubic recurrence"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_isPFPolynomial"
module = "RealRooted.Recurrence.CubicTransition"
label = "Every row of the cubic family is PF"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_interl_add_two"
module = "RealRooted.Recurrence.CubicTransition"
label = "Rows of the cubic family at distance two interlace"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_interl_add_three"
module = "RealRooted.Recurrence.CubicTransition"
label = "Rows of the cubic family at distance three interlace"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_natDegree"
module = "RealRooted.Recurrence.CubicTransition"
label = "For γ, w > 0 the nth row of the cubic family has degree ⌊n/3⌋"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_roots_neg"
module = "RealRooted.Recurrence.CubicTransition"
label = "For γ > 0 all roots of the cubic family are negative"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_residue_interlaces"
module = "RealRooted.Recurrence.CubicTransition"
label = "For γ, w > 0 consecutive rows in each residue class modulo three interlace"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_residue_recurrence"
module = "RealRooted.Recurrence.CubicTransition"
label = "Residue-class subsequences satisfy the cubic recurrence with cubed roots"

[[theorems]]
name = "RealRooted.cubicRecurrence_residue_three"
module = "RealRooted.Recurrence.ResidueSubsequence"
label = "Every-third subsequence of a cubic recurrence: the cubed-roots recurrence"

[[theorems]]
name = "RealRooted.cubicCharacteristic_mul_certificate"
module = "RealRooted.Recurrence.ResidueSubsequence"
label = "Factor certificate for the characteristic polynomial of every-third subsequences"

[[theorems]]
name = "RealRooted.QuarticInterlacingState.IsAdmissible.step"
module = "RealRooted.Recurrence.QuarticInterlacing"
label = "The quartic transition preserves admissibility when 0 ≤ w ≤ v ≤ u and u > 0"

[[theorems]]
name = "RealRooted.quarticInterlacingRow_isPFPolynomial"
module = "RealRooted.Recurrence.QuarticInterlacing"
label = "Every row of an admissible quartic state is PF"

[[theorems]]
name = "RealRooted.quarticInterlacingRow_add_four"
module = "RealRooted.Recurrence.QuarticInterlacing"
label = "The rows of a quartic state satisfy a fourth-order recurrence"
-->

<!-- realrooted-catalog-content -->
# Interlacing rows of cubic and quartic recurrences from ordered PF states

Cubic and quartic recurrences with parameters in explicit ranges have rows that are
Pólya frequency polynomials and that interlace consecutively; for the cubic transitions the
parameter ranges are sharp.

## Results

We use the [zero-aware interlacing convention](rr:about). A polynomial
is *PF* if it is zero or has nonnegative coefficients and only real, nonpositive roots. A triple
$(q,p,r)$ is an *ordered PF triple* if $q,p,r$ are PF and $q\ll p$, $q\ll r$, $p\ll r$.

**Theorem (cubic transition).** For real $\alpha,\gamma,w$, the map
$$
(q,p,r)\ \longmapsto\ \bigl(\alpha q+p,\ r,\ \gamma r+w\,x\,q\bigr)
$$
sends every ordered PF triple to an ordered PF triple if and only if
$\alpha\ge0$, $\gamma\ge0$ and $w\ge0$.

**Proposition (cubic family).** Let $P_0=1$ and let $P_{n+1}$ be the middle coordinate after
$n$ steps of the cubic transition, started from $(1,\gamma,\gamma^2)$. Then $P_1=\gamma$,
$P_2=\gamma^2$ and
$$
P_{n+3}=(\alpha+\gamma)P_{n+2}-\alpha\gamma P_{n+1}+w\,x\,P_n .
$$
The constant term of $P_n$ is $\gamma^n$, and $P_n=\gamma^n$ if $w=0$. Let $\alpha,\gamma,w\ge0$.
Then every $P_n$ is PF and
$$
P_n\ll P_{n+1},\qquad P_n\ll P_{n+2},\qquad P_n\ll P_{n+3}.
$$
If $\gamma>0$, all roots of every $P_n$ are negative. If $\gamma,w>0$, then
$\deg P_n=\lfloor n/3\rfloor$, and $P_{3n+j}$ interlaces $P_{3(n+1)+j}$ with degree gap one for
$j=0,1,2$.

**Theorem (every-third subsequences).** Let $H$ satisfy $H_{n+3}=pH_{n+2}-qH_{n+1}+uH_n$
in a commutative ring. Then for all $j$ and $n$,
$$
H_{3(n+3)+j}=(p^3-3pq+3u)H_{3(n+2)+j}-(q^3-3pqu+3u^2)H_{3(n+1)+j}+u^3H_{3n+j}.
$$
The coefficients are the elementary symmetric functions of the cubes of the characteristic roots.
With $p=\alpha+\gamma$, $q=\alpha\gamma$ and $u=wx$, this is the recurrence of the residue-class
subsequences of the cubic family.

**Theorem (matrix criterion).** Let $\lambda>0$ and let $a,b,c,d$ be real. The map
$$
(p,u,r)\ \longmapsto\ \bigl(r,\ r+\lambda x\,p,\ c\,x\,p+d\,x\,u+(a+bx)\,r\bigr),
$$
given by the matrix $\begin{pmatrix}0&0&1\\\lambda x&0&1\\cx&dx&a+bx\end{pmatrix}$, sends every
ordered PF triple to an ordered PF triple if and only if $a,b,d\ge0$ and $c\ge a\lambda$.

**Corollary (third-order recurrences).** Let $a_s,b_s,d_s\ge0$ and $e_s$ be real, and let
$P_{-1}=P_0=0$, $P_1=1$ and
$$
P_{s+2}=(a_s+b_sx)P_{s+1}+e_s\,x\,P_s+d_s\,x^2P_{s-1}.
$$
Suppose that $a_s\kappa^2-e_s\kappa+d_s\le0$ for all $s$, for a fixed $\kappa>0$; for $\kappa=1$
this reads $e_s\ge a_s+d_s$. Then $(P_s,\ P_s+\kappa xP_{s-1},\ P_{s+1})$ is an ordered PF triple
for every $s$. In particular every $P_s$ is PF and $P_s\ll P_{s+1}$.

**Theorem (quartic transition).** For real $u,v,w$, consider the state
$S=(f_0,f_1,f_2,d,s)$ of five polynomials and the transition
$$
\begin{aligned}
f_0&\mapsto f_1, & f_1&\mapsto f_2,\\
f_2&\mapsto f_2+u\,s+(u+v-w)\,x\,f_1+w\,x\,f_0, & &\\
d&\mapsto d+s+x f_1, & s&\mapsto s+x f_1 .
\end{aligned}
$$
Call $S$ *admissible* if all five coordinates are nonzero PF polynomials, the comparisons
$$
f_0\ll f_1,\quad f_0\ll f_2,\quad f_1\ll f_2,\quad f_1\ll d,\quad f_1\ll s,\quad
f_2\ll s,\quad d\ll s
$$
hold, and $f_2=u\,d+v\,s-w\,x\,f_0$. If $0\le w\le v\le u$ and $u>0$, the transition maps
admissible states to admissible states. Hence, for an admissible initial state, the rows
$R_n=f_0^{(n)}$ of the iterated state are nonzero PF polynomials and $R_n\ll R_{n+1}$.

**Proposition (quartic recurrence).** For every initial state and all $u,v,w$,
$$
R_{n+4}=2R_{n+3}+\bigl((u+v-w)x-1\bigr)R_{n+2}+(2w-v)\,x\,R_{n+1}-w\,x\,R_n .
$$

## Use

A recurrence for a sequence $(P_n)$ keeps every row PF and every consecutive pair interlacing if
it is realized as a transition on a short state of polynomials that preserves a class of
ordered PF tuples and $P_n$ is a coordinate of the iterated state. The cubic and quartic
transitions are two instances.

## Proof

We use the cone lemmas of Wagner [@Wagner1992] (see the [Wagner page](rr:wagner))
for polynomials with nonnegative coefficients: if $h\ll f_i$ for all $i$, then
$h\ll\sum_ic_if_i$ for $c_i\ge0$; if $f_i\ll h$ for all $i$, then $\sum_ic_if_i\ll h$; and
$f\ll g$ implies $g\ll xf$. The sum of an interlacing pair of PF polynomials is PF.

For the cubic transition, the cone lemmas with $q\ll xq$, $p\ll xq$ and $r\ll xq$ give
sufficiency. Necessity follows from the triples $(1,0,0)$ and $(0,0,1)$, which are mapped to
$(\alpha,0,wx)$ and $(0,1,\gamma)$.

For the matrix criterion, let $L=r+\lambda xp$ and $N=aL+bxr+(c-a\lambda)xp+dxu$. For $r\ne0$,
every scalar in $N$ is nonnegative and $r$ and $L$ precede each summand, so the cone lemmas give
$r\ll L$, $r\ll N$ and $L\ll N$; the case $r=0$ is separate. Necessity follows from the triples
$(0,0,1)$, $(0,1,0)$ and $(1,0,0)$, which force $a,b,d\ge0$, and from $(K,0,1)$ with $K$
large, which forces $c\ge a\lambda$.

For the subsequences, let $c(z)=z^3-pz^2+qz-u$. Then
$$
c(z)\,\bigl(z^6+pz^5+(p^2-q)z^4+(pq-2u)z^3+(q^2-pu)z^2+quz+u^2\bigr)
=z^9-(p^3-3pq+3u)z^6+(q^3-3pqu+3u^2)z^3-u^3,
$$
so the residual of the new recurrence is a combination of seven shifted residuals of the
old one, and the argument is division free.

For the quartic transition, the seven comparisons are those that the cone lemmas need, and the
balance identity makes the update of the first auxiliary coordinate a nonnegative cone sum.

## References

The cone lemmas for directed interlacing are due to Wagner [@Wagner1992]; see the
[Wagner page](rr:wagner). For the interlacing convention, see the
[interlacing page](rr:interlacing).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Recurrence.CubicTransition`,
`RealRooted.Recurrence.PFTripleMatrix`, `RealRooted.Recurrence.QuarticInterlacing` and
`RealRooted.Recurrence.ResidueSubsequence`.
-/
