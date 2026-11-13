module

import RealRooted.Chebyshev.Levels

/-!
# Chebyshev level polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "chebyshev-level-polynomials"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.Chebyshev.affineLevel"
module = "RealRooted.Chebyshev.Levels"
label = "The affine level family α (T_n(1 + λ X) - h)"

[[theorems]]
name = "RealRooted.derivative_interlaces_sub_C_of_mem_Icc"
module = "RealRooted.Chebyshev.Levels"
label = "f' interlaces f - s whenever s lies between two real-rooted levels"

[[theorems]]
name = "RealRooted.splits_sub_C_iff_eval_secondDerivative_nonpos"
module = "RealRooted.Chebyshev.Levels"
label = "Critical-value criterion for f - s to be real-rooted"
headline = true

[[theorems]]
name = "RealRooted.Chebyshev.T_sub_C_splits"
module = "RealRooted.Chebyshev.Levels"
label = "T_n - h is real-rooted for |h| ≤ 1"

[[theorems]]
name = "RealRooted.Chebyshev.T_sub_C_splits_simple_roots_mem_Ioo"
module = "RealRooted.Chebyshev.Levels"
label = "For |h| < 1 the roots of T_n - h are simple and lie in (-1, 1)"

[[theorems]]
name = "RealRooted.Chebyshev.forall_pos_T_sub_C_splits_iff_abs_le_one"
module = "RealRooted.Chebyshev.Levels"
label = "All levels T_n - h are real-rooted exactly when |h| ≤ 1"

[[theorems]]
name = "RealRooted.Chebyshev.not_splits_T_add_C_of_one_lt"
module = "RealRooted.Chebyshev.Levels"
label = "T_d + c is not real-rooted for d ≥ 2 and c > 1"

[[theorems]]
name = "RealRooted.Chebyshev.affineLevel_add_three"
module = "RealRooted.Chebyshev.Levels"
label = "The affine level family satisfies an order-three recurrence"

[[theorems]]
name = "RealRooted.Chebyshev.affineLevel_isPFPolynomial"
module = "RealRooted.Chebyshev.Levels"
label = "For α, λ > 0 and |h| ≤ 1 the affine level polynomials are PF"

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
# Chebyshev level polynomials

If $f'$ has simple real roots, a level $f-s$ is real-rooted exactly when $f-s$ is nonnegative
at the local maxima of $f$ and nonpositive at its local minima. All critical values of the
Chebyshev polynomial $T_n$ are $\pm1$, so $T_n-h$ is real-rooted for every $n$ exactly when
$|h|\le1$, and an affine change of variable turns these levels into Pólya frequency polynomials.

## Results

**Theorem (critical-value criterion).** Let $f\in\mathbb R[x]$ have positive leading
coefficient and degree at least $2$, and let $f'$ be real-rooted with simple roots. Then
$f-s$ is real-rooted if and only if
$$
f''(r)\,\bigl(f(r)-s\bigr)\le0\quad\text{for every root }r\text{ of }f' .
$$
If $f'$ is real-rooted and all these inequalities are strict, then $f-s$ is real-rooted with
simple roots.

**Proposition (intermediate levels).** Let $f$ have positive leading coefficient and degree at
least $1$, let $a\le s\le b$, and let $f-a$ and $f-b$ be real-rooted. Then $f'\ll f-s$, and
$f-s$ is real-rooted. If all roots of $f-a$ and of $f-b$ lie in $[L,U]$, then so do all roots of
$f-s$.

**Theorem (Chebyshev levels).** Let $T_n$ be the Chebyshev polynomial of the first kind and
$n\ge1$. If $|h|\le1$, then $T_n-h$ is real-rooted with all roots in $[-1,1]$; if $|h|<1$, its
roots are simple and lie in $(-1,1)$. For fixed $h$, the polynomial $T_n-h$ is real-rooted for
all $n\ge1$ if and only if $|h|\le1$. For $d\ge2$ and $c>1$, the polynomial $T_d+c$ is not
real-rooted.

**Theorem (affine levels).** For real $\alpha,\lambda,h$ put
$$
L_n(x)=\alpha\bigl(T_n(1+\lambda x)-h\bigr).
$$
Then $L_{n+3}=(3+2\lambda x)(L_{n+2}-L_{n+1})+L_n$ for all $n\ge0$. For $\alpha,\lambda>0$,
$|h|\le1$ and $n\ge1$, the polynomial $L_n$ has degree $n$, leading coefficient
$\alpha2^{n-1}\lambda^n$ and is a Pólya frequency polynomial with all roots in
$[-2/\lambda,0]$; if $|h|<1$, its roots are simple and lie in $(-2/\lambda,0)$. All $L_n$ with
$n\ge1$ are Pólya frequency polynomials if and only if $|h|\le1$.

## References

For Chebyshev polynomials, see [@Szego1939].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Chebyshev.Levels`.
-/
