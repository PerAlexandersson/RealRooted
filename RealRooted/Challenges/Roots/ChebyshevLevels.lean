module

import RealRooted.Chebyshev.Levels

/-!
# Chebyshev level polynomials and critical values

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "chebyshev-level-polynomials"
formalized = "2026-11-01"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.Chebyshev.affineLevel"
module = "RealRooted.Chebyshev.Levels"
label = "The affine level family α (T_n(1 + λ X) - h)"

[[theorems]]
name = "RealRooted.derivative_interlaces_sub_C_of_mem_Icc"
module = "RealRooted.Chebyshev.Levels"
label = "f' interlaces f - s whenever s lies between two split levels"

[[theorems]]
name = "RealRooted.splits_sub_C_iff_eval_secondDerivative_nonpos"
module = "RealRooted.Chebyshev.Levels"
label = "Exact critical-value criterion for f - s to split"
headline = true

[[theorems]]
name = "RealRooted.Chebyshev.T_sub_C_splits"
module = "RealRooted.Chebyshev.Levels"
label = "T_n - h splits for |h| ≤ 1"

[[theorems]]
name = "RealRooted.Chebyshev.T_sub_C_splits_simple_roots_mem_Ioo"
module = "RealRooted.Chebyshev.Levels"
label = "For |h| < 1 the roots of T_n - h are simple and lie in (-1, 1)"

[[theorems]]
name = "RealRooted.Chebyshev.forall_pos_T_sub_C_splits_iff_abs_le_one"
module = "RealRooted.Chebyshev.Levels"
label = "All levels T_n - h split exactly when |h| ≤ 1"
headline = true

[[theorems]]
name = "RealRooted.Chebyshev.not_splits_T_add_C_of_one_lt"
module = "RealRooted.Chebyshev.Levels"
label = "T_d + c does not split for d ≥ 2 and c > 1"

[[theorems]]
name = "RealRooted.Chebyshev.affineLevel_add_three"
module = "RealRooted.Chebyshev.Levels"
label = "The affine level family satisfies an order-three recurrence"

[[theorems]]
name = "RealRooted.Chebyshev.affineLevel_isPFPolynomial"
module = "RealRooted.Chebyshev.Levels"
label = "For α, λ > 0 and |h| ≤ 1 the affine level polynomials are PF"
headline = true

[[theorems]]
name = "RealRooted.Chebyshev.affineLevel_splits_simple_roots_mem_Ioo"
module = "RealRooted.Chebyshev.Levels"
label = "For |h| < 1 the roots are simple and lie in (-2/λ, 0)"

[[theorems]]
name = "RealRooted.Chebyshev.forall_pos_affineLevel_isPFPolynomial_iff_abs_le_one"
module = "RealRooted.Chebyshev.Levels"
label = "All affine levels are PF exactly when |h| ≤ 1"
-->

<!-- realrooted-catalog-content -->
# Chebyshev level polynomials and critical values

**Critical-value criterion.** Let $f$ have positive leading coefficient and degree at
least two, and suppose $f'$ splits with simple roots. Then $f-s$ splits if and only if
$$
f''(r)\,\bigl(f(r)-s\bigr)\le0\quad\text{at every root }r\text{ of }f' ,
$$
and if the inequalities are strict, the roots of $f-s$ are moreover simple. If
$s\in[a,b]$ and both $f-a$ and $f-b$ split, then $f'$ interlaces $f-s$, and the roots of
$f-s$ lie in any interval containing the roots of $f-a$ and $f-b$.

## Chebyshev levels

Let $T_n$ be the Chebyshev polynomial of the first kind. For $n\ne0$ and $|h|\le1$ the
level polynomial $T_n-h$ splits with all roots in $[-1,1]$, and for $|h|<1$ its roots are
simple and lie in $(-1,1)$. For a fixed height $h$, all levels $T_n-h$, $n\ge1$, split if
and only if $|h|\le1$. Moreover $T_d+c$ does not split for $d\ge2$ and $c>1$.

## Affine levels

For $\alpha,\lambda,h\in\mathbb R$ let
$$
L_n(x)=\alpha\bigl(T_n(1+\lambda x)-h\bigr),
$$
which satisfies the order-three recurrence
$L_{n+3}=(3+2\lambda x)(L_{n+2}-L_{n+1})+L_n$. For $\alpha,\lambda>0$ and $|h|\le1$,
each $L_n$ ($n\ge1$) has degree $n$, leading coefficient $\alpha2^{n-1}\lambda^n$, and is a PF
polynomial with all roots in $[-2/\lambda,0]$; for $|h|<1$ its roots are simple and lie
in $(-2/\lambda,0)$. All $L_n$ ($n\ge1$) are PF if and only if $|h|\le1$.

## What is new

These results were developed in this library; no published source is cited, and we
attribute none.

## References

No published source is cited for these results in the formalization.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Chebyshev.Levels`.
-/
