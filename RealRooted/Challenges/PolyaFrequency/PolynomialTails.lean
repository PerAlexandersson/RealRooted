module

import RealRooted.PolyaFrequency.EventuallyPolynomial
import RealRooted.PolyaFrequency.EventuallyPolynomial.CausalClosure.ZeroPrefix
import RealRooted.Mathlib.Algebra.Group.ForwardDiff
import RealRooted.PolynomialValueEulerNumerator.PF
import RealRooted.PolynomialValueEulerNumerator.PF.Causal
import RealRooted.PolynomialValueEulerNumerator.Interlacing

/-!
# Pólya frequency sequences with polynomial tails and Euler numerators

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "pf-polynomial-tails"
formalized = "2026-09-10"
references = [
  "Branden2006",
  "Brenti1989",
]
authors = ["Brenti", "Brändén", "Alexandersson"]
years = [1989, 2006, 2026]
tags = ["realrooted-original"]

[[definitions]]
name = "Function.causalFwdDiff"
module = "RealRooted.Mathlib.Algebra.Group.ForwardDiff"
label = "Causal forward difference"

[[definitions]]
name = "RealRooted.polynomialValueEulerNumerator"
module = "RealRooted.PolynomialValueEulerNumerator"
label = "Euler numerator of a polynomial-value sequence"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.eventually_pos_of_eventually_polynomial"
module = "RealRooted.PolyaFrequency.EventuallyPolynomial"
label = "A Pólya frequency sequence with a polynomial tail is eventually positive"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.causalFwdDiff_of_eventually_polynomial"
module = "RealRooted.PolyaFrequency.EventuallyPolynomial.CausalClosure.ZeroPrefix"
label = "The causal forward difference of a Pólya frequency sequence with a polynomial tail"
headline = true

[[theorems]]
name = "Polynomial.forall_nat_eval_nonneg_iff_fwdDiff_iter"
module = "RealRooted.Mathlib.Algebra.Group.ForwardDiff"
label = "Newton's forward-difference test for nonnegativity on the natural numbers"

[[theorems]]
name = "RealRooted.polynomialValueSeq_causalFwdDiff_iter"
module = "RealRooted.PolynomialValueEulerNumerator"
label = "Iterated causal differences of polynomial values are the Euler numerator"

[[theorems]]
name = "RealRooted.isPFPolynomial_polynomialValueEulerNumerator_of_polyaFreqSeq"
module = "RealRooted.PolynomialValueEulerNumerator.PF.Causal"
label = "A Pólya frequency value sequence has a PF Euler numerator"

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_polynomialValueSeq_of_eulerNumerator"
module = "RealRooted.PolynomialValueEulerNumerator.PF"
label = "A PF Euler numerator makes the value sequence Pólya frequency"

[[theorems]]
name = "RealRooted.polynomialValueEulerNumerator_strictInterl_of_rootwiseLE"
module = "RealRooted.PolynomialValueEulerNumerator.Interlacing"
label = "Rootwise-ordered polynomials with roots in [−1, 0] have interlacing Euler numerators"
-->

<!-- realrooted-catalog-content -->
# Pólya frequency sequences with polynomial tails and Euler numerators

If a Pólya frequency sequence eventually agrees with a polynomial, its causal forward
difference is again a Pólya frequency sequence; this characterizes polynomial-value sequences
that are Pólya frequency through their Euler numerators.

A sequence $a = (a_0, a_1, \dotsc)$ is a *Pólya frequency (PF) sequence* if its lower
triangular Toeplitz matrix $(a_{i-j})_{i,j\ge0}$ is totally nonnegative. The *causal forward
difference* of $a$ keeps the initial value,
$$
(\Delta a)_0 = a_0, \qquad (\Delta a)_n = a_n - a_{n-1} \quad (n \ge 1),
$$
so it corresponds to multiplying $\sum_n a_n x^n$ by $1 - x$. A PF polynomial is a real
polynomial with nonnegative coefficients that is zero or has only real nonpositive roots.

## Results

**Theorem (polynomial tails).** Let $a$ be a PF sequence and let $p \ne 0$ be a real polynomial
with $a_n = p(n)$ for all large $n$. Then $a_n>0$ for all large $n$, and $\Delta a$ is a PF
sequence.

**Euler numerators.** For a real polynomial $p$ of degree $d$,
$$
\sum_{n \ge 0} p(n)\, x^n = \frac{W_p(x)}{(1-x)^{d+1}},
$$
where the *Euler numerator* $W_p$ has degree at most $d$ and its coefficients are the iterated
causal differences $\Delta^{d+1}$ of $(p(n))_{n\ge0}$.

**Theorem (Euler numerator criterion).** The value sequence $(p(n))_{n\ge0}$ is a PF sequence
if and only if $W_p$ is a PF polynomial.

**Theorem (rootwise order).** [@Branden2006, Thm. 4.6] Let $f, g$ be monic real-rooted
polynomials of the same positive degree with all roots in $[-1, 0]$, and suppose the increasing
roots of $f$ are coordinatewise at most those of $g$. Then the Euler numerators of $f$ and $g$
interlace.

**Theorem (Newton's forward-difference test).** A real polynomial $q$ satisfies $q(n) \ge 0$
for all $n \in \mathbb N$ if and only if there is $K \in \mathbb N$ such that $q(n) \ge 0$ for
all $n < K$ and $(\Delta_1^j q)(K) \ge 0$ for all $0 \le j \le \deg q$, where
$\Delta_1 q(x) = q(x+1) - q(x)$.

## Use

The Euler numerator criterion underlies Brenti's theorem on Euler numerators with roots in
$[-1,0]$ and Wagner's product theorem for polynomial values; both are on the
[Hadamard products](/RealRooted/theorems/hadamard-products/) page.

## Proof

For the polynomial-tail theorem, the Toeplitz minors of $\Delta a$ are limits of normalized
minors of the Toeplitz matrix of $a$ whose last row lies far out in the tail; an initial run of
zeros is handled by shifting. The direction from $W_p$ to the values is the convolution of
$W_p$ with the PF coefficient sequence of $(1-x)^{-(d+1)}$.

## References

F. Brenti, *Unimodal, log-concave and Pólya frequency sequences in combinatorics*,
Mem. Amer. Math. Soc. 81 (1989), no. 413, Theorem 4.4.4 [@Brenti1989]; P. Brändén, “On
linear transformations preserving the Pólya frequency property,” *Trans. Amer. Math. Soc.* 358
(2006), 3697–3716 [@Branden2006].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.PolyaFrequency.EventuallyPolynomial`
and its `CausalClosure` children, `RealRooted.Mathlib.Algebra.Group.ForwardDiff`, and
`RealRooted.PolynomialValueEulerNumerator`.
-/
