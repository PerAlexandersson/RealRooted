module

import RealRooted.Recurrence.CubicTransition
import RealRooted.Recurrence.QuarticInterlacing
import RealRooted.Recurrence.ResidueSubsequence

/-!
# Cubic and quartic recurrences from ordered PF states

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "higher-order-recurrence-states"
formalized = "2026-11-03"
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
name = "RealRooted.preservesCubicTransition_iff_nonneg"
module = "RealRooted.Recurrence.CubicTransition"
label = "The cubic transition preserves ordered PF triples iff its three parameters are nonnegative"
headline = true

[[theorems]]
name = "RealRooted.cubicTransitionFamily_interl_add_one"
module = "RealRooted.Recurrence.CubicTransition"
label = "Consecutive rows of the cubic family interlace"
headline = true

[[theorems]]
name = "RealRooted.interl_quarticInterlacingRow_succ"
module = "RealRooted.Recurrence.QuarticInterlacing"
label = "Consecutive rows of an admissible quartic state interlace"
headline = true

[[theorems]]
name = "RealRooted.preservesCubicTransition_of_nonneg"
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
label = "The nth row of the cubic family has degree ⌊n/3⌋"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_roots_neg"
module = "RealRooted.Recurrence.CubicTransition"
label = "All roots of the cubic family are negative"

[[theorems]]
name = "RealRooted.cubicTransitionFamily_residue_interlaces"
module = "RealRooted.Recurrence.CubicTransition"
label = "Consecutive rows in each residue class modulo three interlace"

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
# Cubic and quartic recurrences from ordered PF states

Write $p\ll q$ for the directed, zero-aware interlacing of the
[interlacing page](/RealRooted/concepts/interlacing/), and call a polynomial PF if
it is zero or has nonnegative coefficients and only real, nonpositive roots. A
recurrence for a polynomial sequence $(P_n)$ can be proved to keep every row PF
and every consecutive pair interlacing by realizing it as a *closed transition*
on a short state of polynomials: if the transition preserves a class of
ordered PF tuples and $P_n$ is a coordinate of the iterated state, then all rows
inherit the property. This page records two such transitions, with a cubic and a
quartic recurrence, and the algebra of recurrence subsequences. The standard
tools are the cone lemmas for directed interlacing, as in Wagner [@Wagner1992] (see
the [Wagner page](/RealRooted/theorems/wagner/)): if $h\ll f_i$ for summands $f_i$
with nonnegative coefficients then $h\ll\sum f_i$, if $f_i\ll h$ then
$\sum f_i\ll h$, and $f\ll g$ implies $g\ll xf$. In addition, the sum of an
interlacing pair of PF polynomials is PF.

## The cubic transition

A triple $(q,p,r)$ is an **ordered PF triple** if $q,p,r$ are PF and
$q\ll p$, $q\ll r$, $p\ll r$. For real parameters $\alpha,\gamma,w$ consider
$$
(q,p,r)\ \longmapsto\ \bigl(\alpha q+p,\ r,\ \gamma r+w\,x\,q\bigr).
$$

**Theorem.** The transition maps every ordered PF triple to an ordered PF triple
if and only if $\alpha\ge0$, $\gamma\ge0$ and $w\ge0$.

For sufficiency, all outputs are positive combinations of the inputs and of
$xq$, and the cone lemmas above give the six required facts; $q\ll xq$, $p\ll xq$
and $r\ll xq$ come from $f\ll g\Rightarrow g\ll xf$. Necessity is read off from the
triples $(1,0,0)$ and $(0,0,1)$, which are mapped to $(\alpha,0,wx)$ and
$(0,1,\gamma)$, so the nonnegative-coefficient condition forces the signs.

Start from $(1,\gamma,\gamma^2)$ and let $P_0=1$, and let $P_{n+1}$ be the middle
coordinate after $n$ steps. Then $P_0=1$, $P_1=\gamma$, $P_2=\gamma^2$ and
$$
P_{n+3}=(\alpha+\gamma)P_{n+2}-\alpha\gamma P_{n+1}+w\,x\,P_n .
$$
For $\alpha,\gamma,w\ge0$:

- every $P_n$ is PF, and consecutive rows interlace, $P_n\ll P_{n+1}$; rows at
  distance two and three interlace as well, $P_n\ll P_{n+2}$ and $P_n\ll P_{n+3}$;
- the constant term of $P_n$ is $\gamma^n$; for $\gamma>0$ all roots are negative,
  and if moreover $w>0$ then $\deg P_n=\lfloor n/3\rfloor$;
- for $\gamma,w>0$, the subsequences in each residue class modulo three
  interlace in the ordinary one-degree-gap sense:
  $P_{3n+j}$ and $P_{3(n+1)+j}$ interlace for $j=0,1,2$.

At $w=0$ the family is the geometric sequence $\gamma^n$ of constants.

## Subsequences of a cubic recurrence

Let $H$ satisfy $H_{n+3}=pH_{n+2}-qH_{n+1}+uH_n$ in a commutative ring. Then each
fixed-residue subsequence modulo three satisfies
$$
H_{3(n+3)+j}=(p^3-3pq+3u)H_{3(n+2)+j}-(q^3-3pqu+3u^2)H_{3(n+1)+j}+u^3H_{3n+j}.
$$
These coefficients are the elementary symmetric functions of the cubes of the
characteristic roots. The proof is division free: with
$c(z)=z^3-pz^2+qz-u$, the identity
$$
c(z)\,\bigl(z^6+pz^5+(p^2-q)z^4+(pq-2u)z^3+(q^2-pu)z^2+quz+u^2\bigr)
=z^9-(p^3-3pq+3u)z^6+(q^3-3pqu+3u^2)z^3-u^3
$$
turns the residual of the new recurrence into a combination of seven shifted
residuals of the old one. Applied with $p=\alpha+\gamma$, $q=\alpha\gamma$ and
$u=wx$, it gives the recurrence of the residue-class subsequences of the cubic
family.

## The quartic transition

For parameters $u,v,w$ consider a state $S=(f_0,f_1,f_2,d,s)$ of five polynomials
and the transition
$$
\begin{aligned}
f_0&\mapsto f_1, & f_1&\mapsto f_2,\\
f_2&\mapsto f_2+u\,s+(u+v-w)\,x\,f_1+w\,x\,f_0, & &\\
d&\mapsto d+s+x f_1, & s&\mapsto s+x f_1 .
\end{aligned}
$$
Call $S$ **admissible** if all five coordinates are nonzero PF polynomials, the
seven comparisons
$$
f_0\ll f_1,\quad f_0\ll f_2,\quad f_1\ll f_2,\quad f_1\ll d,\quad f_1\ll s,\quad
f_2\ll s,\quad d\ll s
$$
hold, and the balance identity $f_2=u\,d+v\,s-w\,x\,f_0$ holds.

**Theorem.** If $0\le w\le v\le u$ and $u>0$, the transition maps admissible
states to admissible states. Consequently, for an admissible initial state, the
rows $R_n=f_0^{(n)}$ of the iterated state are nonzero PF polynomials and
consecutive rows interlace, $R_n\ll R_{n+1}$.

The rows satisfy, for every initial state and all parameters, the fourth-order
recurrence
$$
R_{n+4}=2R_{n+3}+\bigl((u+v-w)x-1\bigr)R_{n+2}+(2w-v)\,x\,R_{n+1}-w\,x\,R_n .
$$
The state is closed by the cone lemmas above: the seven comparisons are
exactly the ones the transition needs, and the balance identity makes the first
auxiliary update a positive cone sum. The theorem is stated for an arbitrary admissible
initial state; it does not depend on any particular combinatorial sequence.

## What is new

These transitions and the subsequence algebra were developed in this library. The
formalization cites no source for the results themselves, and its docstrings say
that the quartic theorem is independent of any particular combinatorial sequence.
Only the cone lemmas used in the proofs are attributed (to Wagner), following the
docstrings; we attribute nothing further.

## References

The cone lemmas for directed interlacing are due to Wagner [@Wagner1992]; see the
[Wagner page](/RealRooted/theorems/wagner/). For the interlacing convention, see
the [interlacing page](/RealRooted/concepts/interlacing/). The transitions on
this page are not attributed to a published source.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Recurrence.CubicTransition`,
`RealRooted.Recurrence.QuarticInterlacing` and `RealRooted.Recurrence.ResidueSubsequence`.
-/
