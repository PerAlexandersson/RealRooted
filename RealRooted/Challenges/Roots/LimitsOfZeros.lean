module

import RealRooted.Mathlib.Analysis.Complex.Hurwitz
import RealRooted.ThreeTermRecurrence.OrderTwoLimitZeros
import RealRooted.ThreeTermRecurrence.WangZhang

/-!
# Limits of zeros of recursive families

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "limits-of-zeros"
formalized = "2026-10-27"
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
name = "RealRooted.isLimitOfZeros_two_step_of_roots"
module = "RealRooted.ThreeTermRecurrence.OrderTwoLimitZeros"
label = "Limits of zeros of an order-two recurrence"

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

A point $z_0 \in \mathbb{C}$ is a *limit of zeros* of a sequence of functions
$(F_n)_{n \geq 0}$ (`Complex.IsLimitOfZeros`) if every ball around $z_0$ contains a zero
of $F_n$ for all sufficiently large $n$. This is the liminf notion used by Sokal.

**Theorem (two dominant bases).** Let $f_n(z) = \sum_{k \in s} \alpha_k(z)\,\beta_k(z)^n$
for a finite index set $s$ and functions $\alpha_k, \beta_k$ analytic at $z_0$. Suppose
that there are distinct $i, j \in s$ with $\alpha_i(z_0) \neq 0$, $\alpha_j(z_0) \neq 0$,
$\beta_j(z_0) \neq 0$, and $|\beta_i(z_0)| = |\beta_j(z_0)|$, that
$|\beta_k(z_0)| < |\beta_j(z_0)|$ for every other $k \in s$, and that $\beta_i / \beta_j$
is not constant near $z_0$. Then $z_0$ is a limit of zeros of $(f_n)$.

**Theorem (unique dominant base).** With $f_n$ as above, suppose that
$|\beta_k(z_0)| < |\beta_i(z_0)|$ for every $k \neq i$, and that $\alpha_i(z_0) = 0$ while
$\alpha_i$ does not vanish identically near $z_0$. Then $z_0$ is a limit of zeros of
$(f_n)$.

**Order-two recurrences.** Let $W_{n+2} = A\,W_{n+1} + B\,W_n$ with analytic coefficients,
and suppose that near $z_0$ the characteristic roots $u \neq v$ are analytic with
$u + v = A$ and $uv = -B$. If $v(z_0) \neq 0$, $|u(z_0)| = |v(z_0)|$, $u/v$ is not constant
near $z_0$, and the interpolation coefficients $W_1 - v W_0$ and $u W_0 - W_1$ do not
vanish at $z_0$, then $z_0$ is a limit of zeros of $(W_n)$. If a sequence of nonzero real
polynomials $W_n$ has a nonreal limit of zeros, then $W_n$ is not real-rooted for all
sufficiently large $n$.

**Theorem (Wang–Zhang).** Let $a, b, c, d > 0$ and $W_0 = 1$, $W_1 = x$,
$$W_{n+2} = (a x + b)\,W_{n+1} + (c x + d)\,W_n.$$
Then every $W_n$ is real-rooted if and only if $a d \leq b c$.

## References

The two-dominant and unique-dominant theorems are Theorem 1.5(b) and 1.5(a) of
A. D. Sokal, *Chromatic roots are dense in the whole complex plane*, Combinatorics,
Probability and Computing 13 (2004), a generalization of the Beraha–Kahane–Weiss theorem
on limits of zeros. The criterion for affine three-term recurrences is Theorem 2.1 of
Wang and Zhang, arXiv:1712.06105.
<!-- /realrooted-catalog-content -->

The general theorems live in `RealRooted.Mathlib.Analysis.Complex.Hurwitz`, the order-two
consequences in `RealRooted.ThreeTermRecurrence.OrderTwoLimitZeros`, and the Wang–Zhang
criterion in `RealRooted.ThreeTermRecurrence.WangZhang`.
-/
