module

import RealRooted.RecurrenceSpace.Operators
import RealRooted.RecurrenceSpace.Filtered
import RealRooted.RecurrenceSpace.Defect

/-!
# Finite certificates for differential-recurrence families

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "recurrence-space-certificates"
formalized = "2026-10-21"
references = []
authors = ["Alexandersson"]
years = [2026]
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.lagDefect"
module = "RealRooted.RecurrenceSpace.Defect"
label = "Defect of a pure-lag recurrence"

[[definitions]]
name = "RealRooted.liftDefect"
module = "RealRooted.RecurrenceSpace.Defect"
label = "Defect of a first-order differential lift"

[[definitions]]
name = "RealRooted.defectCorrection"
module = "RealRooted.RecurrenceSpace.Defect"
label = "Correction polynomial of the defect identity"

[[definitions]]
name = "RealRooted.FilteredOperator"
module = "RealRooted.RecurrenceSpace.Filtered"
label = "Filtered operator built from shift, index multiplication and differentiation"

[[theorems]]
name = "RealRooted.lagDefect_liftDefect"
module = "RealRooted.RecurrenceSpace.Defect"
label = "Universal source-and-lift defect identity"

[[theorems]]
name = "RealRooted.liftDefect_eq_zero_of_lagDefect_eq_zero"
module = "RealRooted.RecurrenceSpace.Defect"
label = "A source recurrence and k seeds give the differential lift"

[[theorems]]
name = "RealRooted.lagDefect_eq_zero_of_liftDefect_eq_zero"
module = "RealRooted.RecurrenceSpace.Defect"
label = "A differential lift and one seed give the pure-lag recurrence"

[[theorems]]
name = "RealRooted.derivativeRecurrence_of_liftDefect_eq_zero"
module = "RealRooted.RecurrenceSpace.Defect"
label = "A zero lift defect with a scalar leader is the derivative recurrence"

[[theorems]]
name = "RealRooted.shiftAction_pow_succ_sequenceDerivative_eq_zero"
module = "RealRooted.RecurrenceSpace.Operators"
label = "Differentiation raises the annihilating power of a shift polynomial by one"

[[theorems]]
name = "RealRooted.FilteredOperator.shiftAction_pow_apply_eq_zero"
module = "RealRooted.RecurrenceSpace.Filtered"
label = "A filtered operator of weight below h maps solutions into the kernel of the h-th power"

[[theorems]]
name = "RealRooted.FilteredOperator.apply_eq_zero_iff"
module = "RealRooted.RecurrenceSpace.Filtered"
label = "Filtered finite check: vanishing of the first h·k terms suffices"
headline = true
symcat = "recurrenceFiniteVerification"
-->

<!-- realrooted-catalog-content -->
# Finite certificates for differential-recurrence families

Many families of polynomials $P_0, P_1, \dotsc \in K[x]$ come with two descriptions: a pure-lag
recurrence with polynomial coefficients,
$$
P_{n+k} = \sum_{i<k} a_i(x)\, P_{n+i},
$$
and a first-order differential recurrence, or *lift*,
$$
d(n)\, P_{n+1} = A(n)\, P_n + B\, P_n',
$$
in which $d(n) = n d_1 + d_0$ and $A(n) = n A_1 + A_0$ are affine in the index $n$. The lift is
the form used by the root-window theorems for interlacing, while the pure-lag form is the one
that is natural for generating functions and closed formulas. This page records finite
certificates, each checking only finitely many terms or one polynomial identity, that pass
between the two descriptions.

Write $R_n = P_{n+k} - \sum_i a_i P_{n+i}$ for the *lag defect* of $P$ and
$L_n = d(n) P_{n+1} - A(n) P_n - B P_n'$ for the *lift defect*. Let
$\chi(S) = S^k - \sum_i a_i S^i$ be the characteristic polynomial of the lag recurrence, in the
forward shift $S$.

**Theorem** (source-and-lift defect identity). For every polynomial sequence $P$, with no
recurrence assumed,
$$
(\chi(S) L)_n = d(n+k)\, R_{n+1} - A(n+k)\, R_n - B\, R_n' + (J(S)P)_n,
$$
where $J$ is an explicit polynomial in $S$ whose coefficients are built from $a_i$, $a_i'$,
$d_1$, $A_1$ and $B$.

**Corollaries.** Suppose $J = \gamma\, \chi$ for some $\gamma \in K[x]$.

* If $P$ satisfies the pure-lag recurrence and $L_n = 0$ for $n < k$, then $L_n = 0$ for all $n$.
  The recurrence for $L$ is the same pure-lag recurrence, so $k$ seeds determine it.
* Conversely, if $L_n = 0$ for all $n$, the leaders $d(n+k)$ are nonzero and $R_0 = 0$, then
  $R_n = 0$ for all $n$. Hence the lift and one seed imply the pure-lag recurrence.
* If $d(n)$ is a nonzero scalar for each $n$, then $L = 0$ gives the derivative recurrence
  $P_{n+1} = d(n)^{-1}\bigl(B P_n' + A(n) P_n\bigr)$ used by the root-window theorems.

These statements back the recurrence-space tactics (`rr_replay_lift`, `rr_replay_source`): a
certificate for a new family reduces to checking $J = \gamma\chi$, a handful of seeds, and
nonvanishing leaders.

**Filtered operators.** More generally, let $L$ be a finite $K[x]$-linear combination of words
$N^u S^j D^s$, where $S$ is the forward shift, $N$ multiplies the $n$-th entry by $n$, and $D$
differentiates every entry. Say that $L$ has weight below $h$ if $u + s < h$ for every word.
Two facts reduce vanishing to a finite check.

* If $p(S)^q$ annihilates $f$, then $p(S)^{q+1}$ annihilates $D f$ and $N f$. Indeed, $p(S)$
  commutes with $D$ and with $N$ up to a correction that is again a shift polynomial, so each
  application of $D$ or $N$ costs one extra power of $p(S)$.
* Hence, if $p$ is monic of degree $k$, $p(S) f = 0$, and $L$ has weight below $h$, then
  $p(S)^h$ annihilates $L f$. A sequence annihilated by a monic shift polynomial of degree
  $hk$ vanishes as soon as its first $hk$ entries do.

**Theorem** (filtered finite check). Under these hypotheses, $L f = 0$ if and only if
$(L f)_n = 0$ for all $n < h k$.

The proofs are algebraic and, as far as we know, new in this packaging, although the closure
properties resemble standard arguments for holonomic and Ore-algebra recurrences.

## References

No published source is cited for these results. The lifts are consumed by the page on
[recurrence root windows](/RealRooted/theorems/recurrence-root-windows/); see also the page on
[Sturm sequence families](/RealRooted/families/sturm-sequence-families/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.RecurrenceSpace.Operators`,
`RealRooted.RecurrenceSpace.Filtered` and `RealRooted.RecurrenceSpace.Defect`.
-/
