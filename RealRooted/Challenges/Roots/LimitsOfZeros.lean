module

import RealRooted.Mathlib.Analysis.Complex.Hurwitz
import RealRooted.Mathlib.Analysis.Complex.LimitsOfZeros
import RealRooted.ThreeTermRecurrence.OrderTwoLimitZeros
import RealRooted.ThreeTermRecurrence.WangZhang

/-!
# Limits of zeros of recursive families

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "limits-of-zeros"
formalized = "2026-10-27"
references = []
tags = []
authors = ["Beraha", "Kahane", "Weiss", "Sokal", "Wang", "Zhang"]
years = [2004, 2017]

[[definitions]]
name = "Complex.IsLimitOfZeros"
module = "RealRooted.Mathlib.Analysis.Complex.Hurwitz"
label = "Limit of zeros of a sequence of functions"

[[theorems]]
name = "Complex.isLimitOfZeros_finset_two_dominant"
module = "RealRooted.Mathlib.Analysis.Complex.Hurwitz"
label = "Two equimodular dominant bases give a limit of zeros"
headline = true

[[theorems]]
name = "Complex.isLimitOfZeros_finset_unique_dominant"
module = "RealRooted.Mathlib.Analysis.Complex.Hurwitz"
label = "A unique dominant base with vanishing coefficient gives a limit of zeros"

[[theorems]]
name = "Complex.isLimitOfZeros_imp_dominant_or_coeff_zero"
module = "RealRooted.Mathlib.Analysis.Complex.LimitsOfZeros"
label = "Limits of zeros occur only at two dominant bases or a vanishing dominant coefficient"

[[theorems]]
name = "RealRooted.isLimitOfZeros_two_step_of_roots"
module = "RealRooted.ThreeTermRecurrence.OrderTwoLimitZeros"
label = "Limits of zeros of an order-two recurrence"

[[theorems]]
name = "RealRooted.not_isLimitOfZeros_two_step_of_roots"
module = "RealRooted.Mathlib.Analysis.Complex.LimitsOfZeros"
label = "Unequal characteristic roots exclude limits of zeros"

[[theorems]]
name = "RealRooted.eventually_not_splits_of_nonreal_limit"
module = "RealRooted.ThreeTermRecurrence.OrderTwoLimitZeros"
label = "A nonreal limit of zeros forces late polynomials to be not real-rooted"

[[theorems]]
name = "RealRooted.WangZhang.forall_splits_iff"
module = "RealRooted.ThreeTermRecurrence.WangZhang"
label = "Wang–Zhang criterion for an affine three-term recurrence"
-->

<!-- realrooted-catalog-content -->
# Limits of zeros of recursive families

A recurrence of the form $\sum_k\alpha_k\beta_k^n$ has zeros accumulating where two dominant
bases have equal modulus, or where the dominant coefficient vanishes.

## Results

A point $z_0\in\mathbb C$ is a *limit of zeros* of functions $(F_n)_{n\ge0}$ if every ball around
$z_0$ contains a zero of $F_n$ for all sufficiently large $n$ (the liminf notion of Sokal).
In the next three theorems let $f_n(z)=\sum_{k\in s}\alpha_k(z)\,\beta_k(z)^n$ with $s$ a
finite index set.

**Theorem (two dominant bases).** Let $\alpha_k,\beta_k$ be analytic at $z_0$. Suppose there
are distinct $i,j\in s$ with $\alpha_i(z_0)\ne0$, $\alpha_j(z_0)\ne0$, $\beta_j(z_0)\ne0$ and
$|\beta_i(z_0)|=|\beta_j(z_0)|$, that $|\beta_k(z_0)|<|\beta_j(z_0)|$ for every other $k\in s$,
and that $\beta_i/\beta_j$ is not constant near $z_0$. Then $z_0$ is a limit of zeros of
$(f_n)$.

**Theorem (unique dominant base).** Let $\alpha_k,\beta_k$ be analytic at $z_0$. Suppose
$\beta_i(z_0)\ne0$ and $|\beta_k(z_0)|<|\beta_i(z_0)|$ for every $k\ne i$, and that
$\alpha_i(z_0)=0$ while $\alpha_i$ does not vanish identically near $z_0$. Then $z_0$ is a
limit of zeros of $(f_n)$.

**Theorem (necessary condition).** Let $\alpha_k,\beta_k$ be continuous at $z_0$. If $z_0$ is a
limit of zeros of $(f_n)$, then at $z_0$ one of the following holds: two distinct bases
$\beta_i,\beta_j$ have equal modulus, at least that of every $\beta_k$; or there is $i$ with
$\alpha_i(z_0)=0$ and $|\beta_k(z_0)|<|\beta_i(z_0)|$ for all $k\ne i$; or every $\beta_k(z_0)$
vanishes.

**Theorem (order-two recurrences).** Let $W_{n+2}=A\,W_{n+1}+B\,W_n$ with $W_0=U$, $W_1=V$,
and suppose $U,V$ and functions $u,v$ are analytic at $z_0$, where on a ball around $z_0$ we
have $u+v=A$, $uv=-B$ and $u\ne v$.

- If $v(z_0)\ne0$, $|u(z_0)|=|v(z_0)|$, $u/v$ is not constant near $z_0$, and
  $V-vU$ and $uU-V$ do not vanish at $z_0$, then $z_0$ is a limit of zeros of $(W_n)$.
- If $|u(z_0)|\ne|v(z_0)|$ and the coefficient of the root of larger modulus does not vanish
  at $z_0$ ($V-vU$ if $|v(z_0)|<|u(z_0)|$, $uU-V$ if $|u(z_0)|<|v(z_0)|$), then $z_0$ is not
  a limit of zeros of $(W_n)$.
- If real polynomials $W_n$ are nonzero for all large $n$ and $z_0$ is a nonreal limit of
  their zeros, then $W_n$ is not real-rooted for all sufficiently large $n$.

**Theorem (Wang–Zhang).** Let $a,b,c,d>0$ and $W_0=1$, $W_1=x$,
$$W_{n+2}=(a x+b)\,W_{n+1}+(c x+d)\,W_n.$$
Then every $W_n$ is real-rooted if and only if $ad\le bc$.

## References

The first three theorems are Theorem 1.5(b), 1.5(a) and 1.5 of
A. D. Sokal, *Chromatic roots are dense in the whole complex plane*, Combinatorics,
Probability and Computing 13 (2004), a generalization of the Beraha–Kahane–Weiss theorem. The
criterion for affine three-term recurrences is Theorem 2.1 of Wang and Zhang,
arXiv:1712.06105.
<!-- /realrooted-catalog-content -->

The general theorems live in `RealRooted.Mathlib.Analysis.Complex.Hurwitz`, the order-two
consequences in `RealRooted.ThreeTermRecurrence.OrderTwoLimitZeros`, and the Wang–Zhang
criterion in `RealRooted.ThreeTermRecurrence.WangZhang`.
-/
