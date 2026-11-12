module

import RealRooted.SymmetricDecomposition.FPolynomialRecurrence
import RealRooted.SymmetricDecomposition.FPolynomialSequence
import RealRooted.SymmetricDecomposition.EulerFPolynomial

/-!
# The f-polynomial transform: derivative recurrences, real roots and interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "f-transform-recurrences"
formalized = "2026-10-11"
authors = ["Brändén", "Solus"]
tags = []
references = [
  "BrandenSolus2019",
]

[[theorems]]
name = "RealRooted.fPolynomial_derivative"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "The derivative rule for the f-polynomial transform"

[[theorems]]
name = "RealRooted.fPolynomial_derivativeRecurrence_step"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "One transformed derivative-recurrence step"

[[theorems]]
name = "RealRooted.eq_fPolynomial_of_derivRec"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "A transformed recurrence identifies every row"

[[theorems]]
name = "RealRooted.natDegree_le_of_derivRec"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "Quadratic-linear derivative recurrences have at most linear degree growth"

[[theorems]]
name = "RealRooted.eq_fPolynomial_of_derivativeRecurrence_of_natDegree_zero"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "A constant initial row gives the transformed recurrence identity"

[[theorems]]
name = "RealRooted.splits_fPolynomial"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "The f-polynomial transform preserves splitting"

[[theorems]]
name = "RealRooted.roots_fPolynomial_natDegree_eq_map"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "The f-transform maps the roots r to r / (1 - r)"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_natDegree_of_roots_lt_one"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "The f-transform preserves interlacing of polynomials with roots below one"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_natDegree_of_one_lt_roots"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "The f-transform preserves interlacing of polynomials with roots above one"

[[theorems]]
name = "RealRooted.splits_of_eq_fPolynomial"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "Rows that are f-transforms of real-rooted rows are real-rooted"

[[theorems]]
name = "RealRooted.StrictInterl.of_mul_X_sub_C_left_of_roots_gt"
module = "RealRooted.SymmetricDecomposition.FPolynomialSequence"
label = "(x - r)f ≪ g gives f ≪ g if the roots of f exceed r and deg g = deg f + 1"

[[theorems]]
name = "RealRooted.StrictInterl.of_mul_X_sub_C_right_of_roots_ge"
module = "RealRooted.SymmetricDecomposition.FPolynomialSequence"
label = "f ≪ g gives f ≪ (x - r)g for equal degrees and all roots at least r"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_pad_of_mul_X_add_one"
module = "RealRooted.SymmetricDecomposition.FPolynomialSequence"
label = "f_m(u) ≪ (x + 1) f_m(v) gives f_k(u) ≪ f_{k+1}(v) for k ≥ m"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_sequence"
module = "RealRooted.SymmetricDecomposition.FPolynomialSequence"
label = "Half-growth sequences transfer consecutive interlacing"

[[theorems]]
name = "RealRooted.splits_fPolynomial_iff"
module = "RealRooted.SymmetricDecomposition.EulerFPolynomial"
label = "For deg p ≤ d the f-transform splits exactly when p splits"
headline = true

[[theorems]]
name = "RealRooted.fPolynomial_theta_add_C_mul"
module = "RealRooted.SymmetricDecomposition.EulerFPolynomial"
label = "The Euler shift θ + a becomes (a - nX) F + X (1 + X) F' under the f-transform"

[[theorems]]
name = "RealRooted.intervalEulerOperator_splits"
module = "RealRooted.SymmetricDecomposition.EulerFPolynomial"
label = "The interval Euler operator preserves splitting for roots in [-1, 0]"

[[theorems]]
name = "RealRooted.intervalEulerOperator_degree_pos_strictInterl"
module = "RealRooted.SymmetricDecomposition.EulerFPolynomial"
label = "For a > 0 the image keeps the degree n and the input interlaces it"

[[theorems]]
name = "RealRooted.forall_intervalEulerOperator_roots_mem_Icc_iff"
module = "RealRooted.SymmetricDecomposition.EulerFPolynomial"
label = "The window [-1, 0] is preserved exactly when a ≥ 0 or a ≤ -n"
-->

<!-- realrooted-catalog-content -->
# The f-polynomial transform: derivative recurrences, real roots and interlacing

The f-polynomial transform converts derivative recurrences into derivative recurrences, preserves
and reflects real-rootedness, and transfers interlacing of rows with half-growth degrees.

## Results

We write $f\ll g$ if $f$ interlaces $g$; common roots are allowed unless stated. For $d\ge0$ and
a polynomial $h$ of degree at most $d$ with coefficients $h_k$, the *f-polynomial transform* is
$$
f_d(h)=\sum_{k=0}^{d}h_k\,x^k(x+1)^{d-k}.
$$
It is the substitution $x\mapsto x/(x+1)$ homogenized to degree $d$.

**Theorem (derivative rule).** If $\deg p\le d$, then
$$
(x+1)^2\,f_d(p)'=d\,(x+1)\,f_d(p)+f_d(p').
$$

**Theorem (recurrences).** Let $a,b,q$ be polynomials with $\deg a\le2$, $\deg b\le1$,
$\deg q\le d$ and $\deg(aq'+bq)\le d+1$. Then
$$
f_{d+1}(aq'+bq)=(x+1)\,f_2(a)\,f_d(q)'+\bigl(f_1(b)-d\,f_2(a)\bigr)f_d(q).
$$
Consequently, let $Q_{n+1}=a_nQ_n'+b_nQ_n$ with $\deg a_n\le2$, $\deg b_n\le1$ and $\deg Q_n\le n$,
and let $P_0=f_0(Q_0)$ and
$$
P_{n+1}=(x+1)\,f_2(a_n)\,P_n'+\bigl(f_1(b_n)-n\,f_2(a_n)\bigr)P_n.
$$
Then $P_n=f_n(Q_n)$ for all $n$. The degree bound $\deg Q_n\le n$ holds if $Q_0$ is constant.

**Theorem (real roots).** Let $\deg p\le d$. Then $f_d(p)$ is real-rooted if and only if $p$ is
real-rooted. In particular, if $P_n=f_n(Q_n)$ with $\deg Q_n\le n$ and every $Q_n$ real-rooted,
then every $P_n$ is real-rooted.

**Theorem (roots and interlacing).** Let $p\ne0$ be real-rooted with $p(1)\ne0$. Then the roots
of $f_{\deg p}(p)$ are the numbers $r/(1-r)$ for the roots $r$ of $p$. If $f\ll g$ and all roots
of $f$ and $g$ are below $1$, or all are above $1$, then
$f_{\deg f}(f)\ll f_{\deg g}(g)$.

**Theorem (half-growth sequences).** Let $Q_j$ be nonzero real-rooted polynomials with
nonnegative coefficients, $\deg Q_j=\lfloor (j+1)/2\rfloor$ and $Q_j\ll Q_{j+1}$ for all $j$.
Then $f_n(Q_n)\ll f_{n+1}(Q_{n+1})$ for all $n\ge1$.

## Euler shifts

Let $\theta=x\,d/dx$. If $\deg p\le n$ and $a\in\mathbb R$, then
$$
f_n\bigl(\theta p+ap\bigr)=(a-nx)\,f_n(p)+x(1+x)\,f_n(p)'.
$$
Let $F$ be real-rooted of degree $n$ with positive leading coefficient and all roots in
$[-1,0]$, and let $a\in\mathbb R$. Then $(a-nx)F+x(1+x)F'$ is real-rooted. If $a>0$, it has
degree $n$ and positive leading coefficient, and $F\ll(a-nx)F+x(1+x)F'$. For $n\ge1$, all
real-rooted $F$ of degree $n$ with positive leading coefficient and roots in $[-1,0]$ are mapped
to polynomials with roots in $[-1,0]$ if and only if $a\ge0$ or $a\le-n$.

## Use

The alternating-runs polynomials of OEIS [A008970](https://oeis.org/A008970),
[A059427](https://oeis.org/A059427) and [A186370](https://oeis.org/A186370) are f-transforms of
peak polynomials, and the peak rows have the half-growth degree pattern. Real-rootedness and
interlacing of the peak rows therefore pass to the alternating-runs rows.

## Proof

The derivative rule is a direct computation. For the Euler shifts, every real-rooted $F$ of degree
$n$ with positive leading coefficient and roots in $[-1,0]$ is $f_n(q)$ for a Pólya frequency
polynomial $q$ of degree at most $n$, and $q\mapsto\theta q+aq$ preserves real-rootedness of such
polynomials.

## References

See [@BrandenSolus2019] and the
[symmetric-decomposition overview on symmetricfunctions.com](sf:symmetricIDecomposition).
<!-- /realrooted-catalog-content -->
-/
