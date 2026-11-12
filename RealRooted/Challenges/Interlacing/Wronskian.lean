module

import RealRooted.Wronskian
import RealRooted.Wronskian.Converse
import RealRooted.Wronskian.PolarLaguerre

/-!
# Wronskian criterion for interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "wronskian-criterion"
formalized = "2026-10-06"
authors = ["Fisk"]
tags = []
references = [
  "Fisk2006x",
]

[[theorems]]
name = "RealRooted.strictInterl_iff_wronskian_eval_nonneg"
module = "RealRooted.Wronskian.Converse"
label = "Interlacing is a nonnegative Wronskian plus a multiplicity bound"
headline = true
symcat = "wronskianCriterion"

[[theorems]]
name = "RealRooted.strictInterl_of_wronskian_eval_nonneg"
module = "RealRooted.Wronskian.Converse"
label = "A nonnegative Wronskian and the multiplicity bound give interlacing"

[[theorems]]
name = "RealRooted.wronskian_eval_nonneg_of_strictInterl"
module = "RealRooted.Wronskian.WeakForward"
label = "Interlacing gives a nonnegative Wronskian"

[[theorems]]
name = "RealRooted.strictInterl_of_wronskian_eval_nonneg_of_nodup"
module = "RealRooted.Wronskian.Converse"
label = "A nonnegative Wronskian gives interlacing when f has simple zeros"

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

[[theorems]]
name = "RealRooted.derivative_sq_le_natDegree_mul_laguerreForm"
module = "RealRooted.Wronskian.PolarLaguerre"
label = "Degree-weighted Laguerre inequality p'² ≤ deg p · (p'² − p p'')"

[[theorems]]
name = "RealRooted.polar_laguerreForm_nonneg"
module = "RealRooted.Wronskian.PolarLaguerre"
label = "Polar Laguerre inequality (M − 1) p'² ≥ M p p'' for M ≥ deg p"

[[theorems]]
name = "RealRooted.exists_wronskian_eval_nonneg_not_strictInterl"
module = "RealRooted.Wronskian.Converse"
label = "The multiplicity condition cannot be dropped: (x − 1)³ and x³"
-->

<!-- realrooted-catalog-content -->
# Wronskian criterion for interlacing

For real-rooted polynomials with positive leading coefficients and degrees differing by at most
one, $g$ interlaces $f$ if and only if the Wronskian $f'g-fg'$ is nonnegative on $\mathbb R$ and
no zero of $f$ has multiplicity more than one above its multiplicity in $g$.

## Results

For nonzero real-rooted polynomials we write $g\ll f$ if $g$ interlaces $f$, as on the
[interlacing page](/RealRooted/concepts/interlacing/): the zeros interlace weakly and $f$ has the
largest zero, so $\deg f-\deg g\in\{0,1\}$. Shared and repeated zeros are allowed. Let
$W(g,f)=f'g-fg'$, and let $\mathrm{mult}_r(p)$ be the multiplicity of $r$ as a zero of $p$, which
is $0$ if $p(r)\ne0$.

**Theorem (Wronskian criterion).** Let $f,g$ be real-rooted with positive leading coefficients
and $\deg g\le\deg f\le\deg g+1$. Then $g\ll f$ if and only if
$$
W(g,f)(x)\ge0\ \text{ for all }x\in\mathbb R\quad\text{and}\quad
\mathrm{mult}_r(f)\le\mathrm{mult}_r(g)+1\ \text{ for all }r\in\mathbb R .
$$
The forward direction holds for every pair with $g\ll f$ and positive leading coefficients. The
converse also holds when all zeros of $f$ are simple, without the multiplicity condition.

**Example.** The multiplicity condition cannot be dropped: for $f=(x-1)^3$ and $g=x^3$ we have
$W(g,f)=3x^2(x-1)^2\ge0$, but $g\ll f$ fails.

**Theorem (strict converses).** Let $f,g$ be real-rooted with positive leading coefficients and
$W(g,f)(x)>0$ for all $x\in\mathbb R$.

- If $\deg f=\deg g=n$, the zeros $\beta_1\le\dots\le\beta_n$ of $g$ and
  $\alpha_1\le\dots\le\alpha_n$ of $f$ satisfy $\beta_1<\alpha_1<\beta_2<\dots<\beta_n<\alpha_n$.
- If $\deg f=\deg g+1$, then $g\ll f$.

**Theorem (Laguerre's inequality).** If $p$ is real-rooted, then for all $t\in\mathbb R$,
$$
p'(t)^2-p(t)\,p''(t)\ge0 ,
$$
that is, $W(p,p')\le0$. Moreover
$$
p'(t)^2\le\deg(p)\,\bigl(p'(t)^2-p(t)\,p''(t)\bigr),
$$
and $(M-1)\,p'(t)^2\ge M\,p(t)\,p''(t)$ for every $M\ge\deg p$.

## Proof

Common zeros are removed one at a time, using $W(hg,hf)=h^2W(g,f)$. Without common zeros, a
positive Wronskian is handled by the Bézout matrix in equal degree and by padding in successor
degree.

## References

See [@Fisk2006x] and the Wronskian criterion in the
[interlacing overview on symmetricfunctions.com](sf:wronskianCriterion).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The weak converse and the counterexample
live in `RealRooted.Wronskian.Converse`, the forward theorem in
`RealRooted.Wronskian.WeakForward`, the strict converses in
`RealRooted.Bezoutian.WronskianConverse`, and Laguerre's inequality in
`RealRooted.Wronskian.Algebra`.
-/
