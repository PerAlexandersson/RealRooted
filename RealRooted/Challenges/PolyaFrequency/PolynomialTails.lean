module

import RealRooted.PolyaFrequency.EventuallyPolynomial
import RealRooted.PolyaFrequency.EventuallyPolynomial.CausalClosure.ZeroPrefix
import RealRooted.Mathlib.Algebra.Group.ForwardDiff
import RealRooted.PolynomialValueEulerNumerator.PF
import RealRooted.PolynomialValueEulerNumerator.PF.Causal
import RealRooted.PolynomialValueEulerNumerator.Interlacing

/-!
# Pólya-frequency sequences with polynomial tails

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
label = "A PF sequence with a polynomial tail is eventually positive"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.causalFwdDiff_of_eventually_polynomial"
module = "RealRooted.PolyaFrequency.EventuallyPolynomial.CausalClosure.ZeroPrefix"
label = "The causal forward difference of a PF sequence with a polynomial tail is PF"
headline = true

[[theorems]]
name = "Polynomial.forall_nat_eval_nonneg_iff_fwdDiff_iter"
module = "RealRooted.Mathlib.Algebra.Group.ForwardDiff"
label = "Newton's forward-difference test for nonnegativity on the natural numbers"
headline = true

[[theorems]]
name = "RealRooted.causalFwdDiff_iter_polynomialValueSeq_eq_eulerNumerator_coeff"
module = "RealRooted.PolynomialValueEulerNumerator"
label = "Iterated causal differences of polynomial values are the Euler numerator"

[[theorems]]
name = "RealRooted.isPFPolynomial_polynomialValueEulerNumerator_of_polyaFreqSeq"
module = "RealRooted.PolynomialValueEulerNumerator.PF.Causal"
label = "A PF polynomial-value sequence has a PF Euler numerator"
headline = true

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_polynomialValueSeq_of_eulerNumerator"
module = "RealRooted.PolynomialValueEulerNumerator.PF"
label = "A PF Euler numerator makes the polynomial-value sequence PF"

[[theorems]]
name = "RealRooted.polynomialValueEulerNumerator_strictInterl_of_rootwiseLE"
module = "RealRooted.PolynomialValueEulerNumerator.Interlacing"
label = "Rootwise-ordered polynomials with roots in [−1, 0] have interlacing Euler numerators"
-->

<!-- realrooted-catalog-content -->
# Pólya-frequency sequences with polynomial tails

A sequence $a = (a_0, a_1, \dotsc)$ is a *Pólya-frequency (PF) sequence* if its lower
triangular Toeplitz matrix $(a_{i-j})_{i,j\ge0}$ is totally nonnegative. This page collects
results about PF sequences that eventually agree with the values $p(n)$ of a nonzero real
polynomial $p$, together with the Euler-numerator machinery that these results feed.

The *causal forward difference* of $a$ keeps the initial value,
$$
(\Delta a)_0 = a_0, \qquad (\Delta a)_n = a_n - a_{n-1} \quad (n \ge 1),
$$
so that it corresponds to multiplying the generating series $\sum_n a_n x^n$ by $1 - x$.

**Theorem.** Let $a$ be a PF sequence and let $p \ne 0$ be a real polynomial with
$a_n = p(n)$ for all large $n$. Then $a$ is eventually strictly positive, and the causal
forward difference $\Delta a$ is again a PF sequence.

The difficulty is that total nonnegativity is not preserved by differencing in general. The
proof shows that the ordered initial-column minors of the Toeplitz matrix of $\Delta a$ are
limits of normalized minors of the Toeplitz matrix of $a$ whose last row is taken far out in
the polynomial tail; total nonnegativity then follows from the finite truncations. An
initial run of zeros is handled by shifting the sequence.

**Euler numerators.** For a real polynomial $p$ of degree $d$ the generating series of its
values has the form
$$
\sum_{n \ge 0} p(n)\, x^n = \frac{W_p(x)}{(1-x)^{d+1}},
$$
with the *Euler numerator* $W_p$ of degree at most $d$; its coefficients are the iterated
causal differences $\Delta^{d+1}$ of the value sequence. Applying the theorem above
$d + 1$ times gives the following equivalence.

**Theorem.** The value sequence $(p(n))_{n\ge0}$ is a PF sequence if and only if $W_p$ is a
PF polynomial, that is, $W_p$ is real-rooted with nonnegative coefficients and no positive
roots. The direction from $W_p$ to the values is the convolution of $W_p$ with the PF
sequence of coefficients of $(1-x)^{-(d+1)}$.

This is the structural reason behind Brenti's theorem and Wagner's product theorem for
polynomial values, which are stated on the page on Hadamard products. In particular, a
product of PF polynomial-value sequences is PF because the Euler numerator of $fg$ is the
Brändén–Ferroni–Jochemko product of the Euler numerators of $f$ and $g$.

**Theorem** (rootwise order). [@Branden2006, Thm. 4.6] Let $f, g$ be monic real-rooted
polynomials of the same positive degree with all roots in $[-1, 0]$, and suppose the roots of
$f$ are coordinatewise at most the roots of $g$. Then the Euler numerators of $f$ and $g$
interlace. The proof writes $W_p$ as the Cayley transform of Brändén's $\mathsf{E}$-transform
of $p$.

**Newton's forward-difference test.** For a real polynomial $q$ of degree $m$ and a natural
number $K$, Newton's formula
$$
q(K + r) = \sum_{j=0}^{m} \binom{r}{j}\, (\Delta_1^{j} q)(K),
$$
with the ordinary forward difference $\Delta_1 q(x) = q(x+1) - q(x)$, shows the following
finite test for nonnegativity at all natural numbers.

**Theorem.** A real polynomial $q$ satisfies $q(n) \ge 0$ for all $n \in \mathbb N$ if and only
if there is $K \in \mathbb N$ such that $q(n) \ge 0$ for all $n < K$ and
$(\Delta_1^j q)(K) \ge 0$ for all $0 \le j \le \deg q$. For necessity one uses that
$\Delta_1^j q$ has a positive leading coefficient whenever $q$ has, so each difference is
eventually nonnegative.

## References

F. Brenti, *Unimodal, log-concave and Pólya frequency sequences in combinatorics*,
Mem. Amer. Math. Soc. 81 (1989), no. 413, Theorem 4.4.4 [@Brenti1989]; P. Brändén, “On
linear transformations preserving the Pólya frequency property,” *Trans. Amer. Math. Soc.* 358
(2006), 3697–3716 [@Branden2006]. The results on polynomial tails and Newton's
forward-difference test (RealRooted issue #1955, with the proof found by the Aristotle prover)
have no source in the literature that we are aware of.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.PolyaFrequency.EventuallyPolynomial`
and its `CausalClosure` children, `RealRooted.Mathlib.Algebra.Group.ForwardDiff`, and
`RealRooted.PolynomialValueEulerNumerator`.
-/
