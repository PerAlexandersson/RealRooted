module

import RealRooted.Interlacing.QuadraticRemainderCriterion

/-!
# Interlacing of quadratics

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "quadratic-interlacing-criterion"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.normalizedQuadraticFamily"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "The monic quadratic family H_y"

[[theorems]]
name = "RealRooted.exists_ordered_quadratic_roots_iff_remainder_signs"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "Alternating root order of two quadratics is equivalent to four sign conditions"
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

[[theorems]]
name = "RealRooted.normalizedQuadraticRow_degree_coeff_roots"
module = "RealRooted.Interlacing.QuadraticRemainderCriterion"
label = "Rows have degree n + 2, positive coefficients and roots in [-1, 0)"
-->

<!-- realrooted-catalog-content -->
# Interlacing of quadratics

Two quadratics with positive leading coefficients have alternating roots above a point $L$
exactly when four polynomial inequalities in their coefficients hold. The criterion involves no
square roots, so it applies directly to quadratics whose coefficients depend on parameters.

## Results

**Theorem (criterion).** Let $f=ax^2+bx+c$ and $g=Ax^2+Bx+d$ with $a,A>0$, and let
$L\in\mathbb R$. Put $u=aB-Ab$ and $v=ad-Ac$, so that $ag-Af=ux+v$. There are roots $r_1,r_2$ of $f$
and $s_1,s_2$ of $g$ with
$$
L<r_1<s_1<r_2<s_2
$$
if and only if
$$
u<0,\qquad a v^2-b\,u\,v+c\,u^2<0,\qquad f(L)>0,\qquad f'(L)<0 .
$$
The second inequality says $u^2f(-v/u)<0$, that is, the root $-v/u$ of the remainder lies
strictly between the roots of $f$. Under these inequalities, $f\ll g$, both $f$ and $g$ have
simple roots, they have no common root, and $f\ll(x-L)\,g$ with a degree gap of one.

**Example (a one-parameter family).** For $y\in[0,1/3]$ let
$$
H_y(x)=x^2+\frac{6+11y-3y^2}{7}\,x+\frac{1+3y+3y^2}{7}.
$$
Each $H_y$ has simple real roots, all in $[-1,0)$. For $y,z\in[0,1/3]$,
$$
H_y\ll H_z\iff z\le y\iff H_y\ll(x+1)H_z .
$$
For a sequence $y_n\in[0,1/3]$, the row $(x+1)^nH_{y_n}$ has degree $n+2$, positive
coefficients, and all roots in $[-1,0)$. Consecutive rows satisfy
$$
(x+1)^nH_{y_n}\ll(x+1)^{n+1}H_{y_{n+1}}\iff y_{n+1}\le y_n .
$$

## References

For interlacing in general, see [@Fisk2006x].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Interlacing.QuadraticRemainderCriterion`.
-/
