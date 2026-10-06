import RealRooted.Wronskian

/-!
# Wronskian criterion for interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "wronskian-criterion"

[[theorems]]
name = "RealRooted.strictInterl_iff_wronskian_eval_nonneg"
module = "RealRooted.Wronskian.Converse"
label = "Interlacing is a nonnegative Wronskian plus a multiplicity bound"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_of_wronskian_eval_nonneg"
module = "RealRooted.Wronskian.Converse"
label = "A nonnegative Wronskian and the multiplicity bound give interlacing"
headline = true

[[theorems]]
name = "RealRooted.wronskian_eval_nonneg_of_strictInterl"
module = "RealRooted.Wronskian.WeakForward"
label = "Interlacing gives a nonnegative Wronskian"

[[theorems]]
name = "RealRooted.strictInterl_of_wronskian_eval_nonneg_of_nodup"
module = "RealRooted.Wronskian.Converse"
label = "A nonnegative Wronskian gives interlacing when f has simple zeros"

[[theorems]]
name = "RealRooted.exists_wronskian_eval_nonneg_not_strictInterl"
module = "RealRooted.Wronskian.Converse"
label = "The multiplicity bound cannot be dropped"

[[theorems]]
name = "RealRooted.StrictInterlSameDegree.of_wronskian_pos"
module = "RealRooted.Bezoutian.WronskianConverse"
label = "A positive Wronskian gives strict interlacing in equal degree"

[[theorems]]
name = "RealRooted.strictInterl_of_wronskian_pos_succ"
module = "RealRooted.Bezoutian.WronskianConverse"
label = "A positive Wronskian gives interlacing in successor degree"

[[theorems]]
name = "RealRooted.laguerre_form_nonneg"
module = "RealRooted.Wronskian.Algebra"
label = "Laguerre's inequality"
-->

<!-- realrooted-catalog-content -->
# Wronskian criterion for interlacing

For nonzero real-rooted polynomials $g$ and $f$ we write $g \ll f$
(`StrictInterl g f`) as on the [interlacing page](/RealRooted/concepts/interlacing/):
the zeros interlace weakly and $f$ has the largest zero, so that
$\deg f - \deg g \in \{0, 1\}$. Shared and repeated zeros are allowed. The
Wronskian of the pair is
$$
W(g, f) = f' g - f g' .
$$
We write $\mathrm{mult}_r(p)$ for the multiplicity of $r$ as a zero of $p$,
which is $0$ when $p(r) \neq 0$.

**Theorem.** Let $f$ and $g$ have positive leading coefficients. If
$g \ll f$, then $f'(x) g(x) - f(x) g'(x) \geq 0$ for all $x \in \mathbb R$.

**Theorem** (weak converse). Let $f$ and $g$ be real-rooted with positive
leading coefficients and $\deg g \leq \deg f \leq \deg g + 1$. Suppose that
$f'(x) g(x) - f(x) g'(x) \geq 0$ for all $x \in \mathbb R$ and that
$\mathrm{mult}_r(f) \leq \mathrm{mult}_r(g) + 1$ for every $r \in \mathbb R$.
Then $g \ll f$. In particular, this holds when all zeros of $f$ are simple.

Together with the bound $\mathrm{mult}_r(f) \leq \mathrm{mult}_r(g) + 1$,
which every pair with $g \ll f$ satisfies, this gives a characterization.

**Theorem.** Let $f$ and $g$ be real-rooted with positive leading
coefficients and $\deg g \leq \deg f \leq \deg g + 1$. Then $g \ll f$ if and
only if $f'(x) g(x) - f(x) g'(x) \geq 0$ for all $x \in \mathbb R$ and
$\mathrm{mult}_r(f) \leq \mathrm{mult}_r(g) + 1$ for every $r \in \mathbb R$.

**The multiplicity condition is needed.** The polynomials $f = (x-1)^3$ and
$g = x^3$ are real-rooted with positive leading coefficients and equal
degree, and $f' g - f g' = 3x^2(x-1)^2 \geq 0$, but $g \ll f$ fails.

**Theorem** (strict converses). Let $f$ and $g$ be real-rooted with positive
leading coefficients, and suppose that $f'(x) g(x) - f(x) g'(x) > 0$ for all
$x \in \mathbb R$.

- If $\deg f = \deg g$, then the zeros $\beta_1 \le \dotsb \le \beta_n$ of
  $g$ and $\alpha_1 \le \dotsb \le \alpha_n$ of $f$ interlace strictly:
  $\beta_1 < \alpha_1 < \beta_2 < \dotsb < \beta_n < \alpha_n$.
- If $\deg f = \deg g + 1$, then $g \ll f$.

**Theorem** (Laguerre's inequality). If $p$ is zero or real-rooted, then
$p'(x)^2 - p(x) p''(x) \geq 0$ for all $x \in \mathbb R$, that is,
$W(p, p') \leq 0$.

## Proof idea

The forward direction removes common zeros one at a time, since
$W(hg, hf) = h^2 W(g, f)$. Without common zeros, the strict forward
theorems apply: positive definiteness of the Bézout matrix in equal degree,
and a padding argument in successor degree.

For the weak converse we again strip common zeros. The identity
$W(hg, hf) = h^2 W(g, f)$ with $h = x - r$ keeps the reduced Wronskian
nonnegative away from $r$, and continuity covers $r$ itself. Once no common
zero is left, the multiplicity bound makes every zero of $f$ simple. At a
zero $r$ of $f$ we have $W(g, f)(r) = g(r) f'(r) \neq 0$, so the Wronskian is
positive at every zero of $f$. Through the Vandermonde matrix of these zeros,
the Bézout matrix is congruent to a positive diagonal matrix, hence positive
definite, and the Wronskian is positive on all of $\mathbb R$. The strict
converses then give $g \ll f$.

The strict converses use signs at zeros. A positive Wronskian forces all
zeros to be simple. At a zero $r$ of $f$ we have $W(g, f)(r) = g(r) f'(r) > 0$,
and $f'$ alternates in sign along the zeros of $f$, so $g$ does as well. The
intermediate value theorem then places a zero of $g$ between consecutive
zeros of $f$, and the behaviour at $\pm\infty$ locates the remaining zeros.
Laguerre's inequality follows by induction on the zeros, since adjoining a
factor $x - a$ to $q$ turns $q'^2 - q q''$ into
$q^2 + (x - a)^2 (q'^2 - q q'')$.

## References

S. Fisk, [*Polynomials, roots, and
interlacing*](https://arxiv.org/abs/math/0612833), arXiv:math/0612833 (2006).
See also the Wronskian criterion in the
[interlacing overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The weak converse and the counterexample
live in `RealRooted.Wronskian.Converse`, the forward theorem in
`RealRooted.Wronskian.WeakForward`, the strict converses in
`RealRooted.Bezoutian.WronskianConverse`, and Laguerre's inequality in
`RealRooted.Wronskian.Algebra`.
-/
