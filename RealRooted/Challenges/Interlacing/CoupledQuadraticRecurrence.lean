module

import RealRooted.Interlacing.CoupledQuadraticRecurrence
import RealRooted.Interlacing.WeightedLadder

/-!
# Interlacing of a coupled quadratic recurrence and real roots of weighted ladder polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "coupled-quadratic-recurrence"
formalized = "2026-11-03"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.CoupledQuadraticRecurrence"
module = "RealRooted.Interlacing.CoupledQuadraticRecurrence"
label = "The coupled recurrence for A_n, B_n with varying affine terms and weights"

[[definitions]]
name = "RealRooted.ladderL"
module = "RealRooted.Interlacing.WeightedLadder"
label = "Weighted ladder polynomials L_n"

[[definitions]]
name = "RealRooted.LadderScalarRecurrence"
module = "RealRooted.Interlacing.WeightedLadder"
label = "The scalar third-order recurrence of the ladder polynomials with its three seeds"

[[theorems]]
name = "RealRooted.CoupledQuadraticRecurrence.strictInterl_B_succ_A_succ"
module = "RealRooted.Interlacing.CoupledQuadraticRecurrence"
label = "B_n interlaces A_n"
headline = true

[[theorems]]
name = "RealRooted.CoupledQuadraticRecurrence.strictInterl_A_succ_B_succ"
module = "RealRooted.Interlacing.CoupledQuadraticRecurrence"
label = "A_n interlaces B_{n+1}"

[[theorems]]
name = "RealRooted.CoupledQuadraticRecurrence.hasSimpleRoots_A_succ"
module = "RealRooted.Interlacing.CoupledQuadraticRecurrence"
label = "A_n has simple real roots"

[[theorems]]
name = "RealRooted.CoupledQuadraticRecurrence.A_succ_mul_A_sub_sq"
module = "RealRooted.Interlacing.CoupledQuadraticRecurrence"
label = "The recursion for Δ_n = A_n A_{n-1} − B_n²"

[[theorems]]
name = "RealRooted.CoupledQuadraticRecurrence.natDegree_A_succ"
module = "RealRooted.Interlacing.CoupledQuadraticRecurrence"
label = "deg A_n = 2n"

[[theorems]]
name = "RealRooted.hasSimpleRoots_ladderL"
module = "RealRooted.Interlacing.WeightedLadder"
label = "Weighted ladder polynomials have simple real roots"

[[theorems]]
name = "RealRooted.lt_zero_of_mem_roots_ladderL"
module = "RealRooted.Interlacing.WeightedLadder"
label = "All roots of the weighted ladder polynomials are negative"

[[theorems]]
name = "RealRooted.ladderL_add_three"
module = "RealRooted.Interlacing.WeightedLadder"
label = "The ladder polynomials satisfy a third-order scalar recurrence"

[[theorems]]
name = "RealRooted.LadderScalarRecurrence.splits"
module = "RealRooted.Interlacing.WeightedLadder"
label = "Every solution of the scalar ladder recurrence with the three seeds splits"
-->

<!-- realrooted-catalog-content -->
# Interlacing of a coupled quadratic recurrence and real roots of weighted ladder polynomials

Two coupled quadratic recurrences with varying linear terms produce interlacing polynomials
with simple real roots; the weighted ladder polynomials are obtained from them.

## Results

We write $f\ll g$ if $f$ interlaces $g$; common roots are allowed unless stated. Let
$\ell_n(t)=a_nt+b_n$ with $a_n>0$, let $u_0>0$, $u_n\ge0$ and $v_n>0$ for $n\ge1$, and put
$A_0=1$, $B_1=\ell_0$, $A_1=\ell_0^2-u_0$ and, for $n\ge1$,
$$
\begin{aligned}
B_{n+1}&=\ell_nA_n-v_nB_n,\\
A_{n+1}&=(\ell_n^2-u_n)A_n-2v_n\ell_nB_n+v_n^2A_{n-1}.
\end{aligned}
$$

**Theorem (coupled recurrence).** For every $n\ge1$, the polynomials $A_n$ and $B_n$ have
positive leading coefficients, degrees $2n$ and $2n-1$, and simple real roots, and
$$
B_n\ll A_n\ll B_{n+1}.
$$
Moreover $A_n$ and $B_n$ have no common root.

For $u,v>0$ define the *weighted ladder polynomials* by $L_0=1$, $L_1=1+ux$, $C_0=0$ and
$$
C_{n+1}=L_n+vxC_n,\qquad L_{n+1}=(1+ux)L_n+2vxC_n+v^2x^2L_{n-1}\quad(n\ge1).
$$

**Theorem (weighted ladder).** Every $L_n$ has degree $n$, nonnegative coefficients and simple
negative roots. Moreover
$$
L_{n+3}=(1+(u+v)x)L_{n+2}+vx\bigl(1+(v-u)x\bigr)L_{n+1}-v^3x^3L_n
$$
for all $n$, and every sequence of polynomials satisfying this recurrence with the seeds $1$,
$1+ux$ and $1+2(u+v)x+(u^2+v^2)x^2$ consists of real-rooted polynomials.

Consecutive ladder polynomials need not interlace: for $u=1$ and $v=3$, both roots of
$L_2=1+8x+10x^2$ exceed the root of $L_1$.

## Use

For $u=v=1$ the scalar recurrence is that of OEIS A046741.

## Proof

Put $\Delta_n=A_nA_{n-1}-B_n^2$. The recurrence gives $\Delta_1=-u_0$ and
$\Delta_{n+1}=v_n^2\Delta_n-u_nA_n^2$, so $\Delta_n<0$ on $\mathbb R$. At a root $\alpha$ of
$A_n$, this yields $B_{n+1}(\alpha)B_n(\alpha)=-v_nB_n(\alpha)^2<0$. At a root $\beta$ of
$B_{n+1}$, it yields $A_{n+1}(\beta)A_n(\beta)=v_n^2\Delta_n(\beta)-u_nA_n(\beta)^2<0$. Two
applications of the root-sign criterion for polynomials whose degrees differ by one carry the
induction.

The signed parity lifts $A_n(t)=t^{2n}L_n(-t^{-2})$ and $B_n(t)=t^{2n-1}C_n(-t^{-2})$ satisfy
the coupled recurrence with $\ell_n=t$, $u_n=u$ and $v_n=v$. Eliminating $C_n$ gives the scalar
recurrence.

## References

The root-sign criterion is the differ-by-one criterion on the
[Ma–Wang and Liu–Wang page](/RealRooted/theorems/ma-wang-liu-wang/). For the interlacing
convention, see the [interlacing page](/RealRooted/concepts/interlacing/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Interlacing.CoupledQuadraticRecurrence` and `RealRooted.Interlacing.WeightedLadder`.
-/
