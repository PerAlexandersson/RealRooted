module

import RealRooted.Interlacing.QuadraticRemainderCriterion

/-!
# A coefficient criterion for interlacing quadratics

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "quadratic-interlacing-criterion"
formalized = "2026-11-01"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.normalizedQuadraticFamily"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "The monic quadratic family H_y"

[[theorems]]
name = "RealRooted.exists_ordered_quadratic_roots_iff_remainder_signs"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "Alternating root order of two quadratics is equivalent to three sign conditions"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_quadratics_of_remainder_signs"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "The sign conditions give interlacing, simple roots and no common roots"

[[theorems]]
name = "RealRooted.interlaces_quadratic_mul_X_sub_C_of_remainder_signs"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "The sign conditions give differ-by-one interlacing with a linear multiple"

[[theorems]]
name = "RealRooted.normalizedQuadraticFamily_splits_simple_roots_mem_Ico"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "H_y has simple real roots in [-1, 0) for 0 ≤ y ≤ 1/3"

[[theorems]]
name = "RealRooted.normalizedQuadraticFamily_strictInterl_iff"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "H_y interlaces H_z exactly when z ≤ y"

[[theorems]]
name = "RealRooted.normalizedQuadraticFamily_interlaces_mul_X_add_one_iff"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "H_y interlaces (X + 1) H_z exactly when z ≤ y"

[[theorems]]
name = "RealRooted.normalizedQuadraticRows_interlaces_iff"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "Consecutive rows (X + 1)^n H_{y_n} interlace exactly when y_{n+1} ≤ y_n"
headline = true

[[theorems]]
name = "RealRooted.normalizedQuadraticRow_degree_coeff_roots"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "Rows have degree n + 2, positive coefficients and roots in [-1, 0)"
-->

<!-- realrooted-catalog-content -->
# A coefficient criterion for interlacing quadratics

Let $f=ax^2+bx+c$ and $g=Ax^2+Bx+d$ with $a,A>0$. We characterize, directly in
terms of the coefficients, when the roots of $f$ and $g$ occur in the order
$$
L<r_1<s_1<r_2<s_2
$$
where $r_1,r_2$ are the roots of $f$ and $s_1,s_2$ those of $g$. Put
$u=aB-Ab$ and $v=ad-Ac$, so that the cancelled linear remainder is
$ag-Af=ux+v$. The order holds exactly when

1. $u<0$;
2. $a v^2-b\,u\,v+c\,u^2<0$, where the left side equals $u^2f(-v/u)$, so that
   the root $-v/u$ of the remainder lies strictly between the roots of $f$;
3. $f(L)>0$ and $f'(L)<0$.

Under these conditions, $f$ and $g$ interlace, both have simple roots and they
share no root, and $f$ interlaces $(x-L)\,g$ in the differ-by-one sense. The
criterion avoids comparing square roots in applications.

## A one-parameter family

For $y\in[0,1/3]$ let
$$
H_y(x)=x^2+\frac{6+11y-3y^2}{7}\,x+\frac{1+3y+3y^2}{7}.
$$
Each $H_y$ has simple real roots in $[-1,0)$, and for $z,y\in[0,1/3]$ the
polynomial $H_y$ interlaces $H_z$, and also $(x+1)H_z$, if and only if
$z\le y$. Consequently, for any sequence $y_n\in[0,1/3]$ the rows
$(x+1)^nH_{y_n}$ have degree $n+2$, positive coefficients and roots in
$[-1,0)$, and consecutive rows interlace if and only if $y_{n+1}\le y_n$.

## What is new

The criterion and the family were developed in this library; no published
source is cited, and we attribute none.

## References

No published source is cited for these results in the formalization. For the
interlacing convention, see the [interlacing page](/RealRooted/concepts/interlacing/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Interlacing.QuadraticRemainderCriterion`.
-/
