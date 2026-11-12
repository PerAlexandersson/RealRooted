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

A pure-lag recurrence and a first-order differential lift for a polynomial sequence are linked by
one polynomial identity, and the lift follows from the recurrence and finitely many seeds.

## Results

Let $K$ be a field and $P_0,P_1,\dotsc\in K[x]$. A *pure-lag recurrence* of order $k$ with
coefficients $a_i\in K[x]$ is
$$
P_{n+k}=\sum_{i<k}a_i\,P_{n+i},
$$
and a *lift* with $d_1,d_0,A_1,A_0,B\in K[x]$ is
$$
d(n)\,P_{n+1}=A(n)\,P_n+B\,P_n',\qquad d(n)=nd_1+d_0,\quad A(n)=nA_1+A_0 .
$$
Let $S$ be the forward shift on sequences, and put
$$
R_n=P_{n+k}-\sum_{i<k}a_iP_{n+i},\qquad L_n=d(n)P_{n+1}-A(n)P_n-BP_n',
$$
the *lag defect* and the *lift defect*, and $\chi(S)=S^k-\sum_ia_iS^i$.

**Theorem (defect identity).** For every sequence $P$, with no recurrence assumed,
$$
(\chi(S)L)_n=d(n+k)\,R_{n+1}-A(n+k)\,R_n-B\,R_n'+(J(S)P)_n,
$$
where
$$
J(S)=\sum_{i<k}\Bigl((k-i)\,a_id_1\,S^{i+1}-\bigl((k-i)\,a_iA_1+B\,a_i'\bigr)S^i\Bigr).
$$

**Corollary (propagation).** Suppose $J=\gamma\,\chi$ for some $\gamma\in K[x]$.

- If $R_n=0$ for all $n$ and $L_n=0$ for $n<k$, then $L_n=0$ for all $n$.
- If $L_n=0$ for all $n$, $d(n+k)\ne0$ for all $n$, and $R_0=0$, then $R_n=0$ for all $n$.
- If $L_n=0$ for all $n$ and $d(n)=\delta_n\in K\setminus\{0\}$, then
  $P_{n+1}=\delta_n^{-1}\bigl(B\,P_n'+A(n)\,P_n\bigr)$.

**Theorem (filtered finite check).** Let $N$ multiply the $n$-th entry of a sequence by $n$, let
$D$ differentiate every entry, and let $F=\sum c_{u,j,s}\,N^uS^jD^s$ be a finite combination with
coefficients in $K[x]$ of weight below $h$, meaning $u+s<h$ for every word. Let $p$ be a monic
polynomial of degree $k$ in $S$ with coefficients in $K[x]$, and let $f$ satisfy $p(S)f=0$. Then
$p(S)^hFf=0$, and
$$
Ff=0\iff (Ff)_n=0\ \text{ for all } n<hk .
$$
Underlying this, if $p(S)^qf=0$ then $p(S)^{q+1}Df=0$.

## Use

The root-window theorems on the
[recurrence root windows](/RealRooted/theorems/recurrence-root-windows/) page use the derivative
recurrence in the third corollary. The tactics `rr_replay_lift` and `rr_replay_source` reduce a
certificate for a new family to $J=\gamma\chi$, finitely many seeds and nonvanishing leaders.

## References

See also the page on [Sturm sequence families](/RealRooted/families/sturm-sequence-families/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.RecurrenceSpace.Operators`,
`RealRooted.RecurrenceSpace.Filtered` and `RealRooted.RecurrenceSpace.Defect`.
-/
