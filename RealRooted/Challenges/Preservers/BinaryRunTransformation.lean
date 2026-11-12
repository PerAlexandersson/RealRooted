module

public import RealRooted.BalancedRunTransformation.Interlacing
public import RealRooted.BalancedRunTransformation.Preservation
public import RealRooted.BinaryRunTransformation.Continuation
public import RealRooted.BinaryRunTransformation.MultiplierMotzkin
public import RealRooted.BinaryRunTransformation.SymbolCounterexample

/-!
# Binary-run transformation preserving PF polynomials and interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "binary-run-transformation"
formalized = "2026-09-28"
authors = []
tags = []
references = [
  "BorceaBranden2009I",
  "MaoWang2026x",
]

[[definitions]]
name = "RealRooted.binaryRunPolynomial"
module = "RealRooted.BinaryRunTransformation.Coefficients"
label = "Binary-run basis polynomials"

[[definitions]]
name = "RealRooted.binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Coefficients"
label = "Binary-run transformation"

[[definitions]]
name = "RealRooted.motzkinWeightedRow"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "Multiplier-weighted Motzkin rows"

[[definitions]]
name = "RealRooted.balancedRunTransform"
module = "RealRooted.BalancedRunTransformation"
label = "Balanced run transformation"

[[theorems]]
name = "RealRooted.IsPFPolynomial.binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Continuation"
label = "J_n maps PF polynomials of degree at most n to PF polynomials"

[[theorems]]
name = "RealRooted.binaryRunTransform_splits_and_roots_neg"
module = "RealRooted.BinaryRunTransformation.Continuation"
label = "A PF input with positive constant term has an image with only negative roots"

[[theorems]]
name = "RealRooted.strictInterl_binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Interlacing"
label = "J_n preserves interlacing on inputs of degree at most (n+1)/2"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_binaryRunTransform_succ"
module = "RealRooted.BinaryRunTransformation.CrossLength"
label = "J_n of (n+1)g - 2Θg interlaces J_{n+1} g"

[[theorems]]
name = "RealRooted.motzkinWeightedRow_strictInterl_succ"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "Weighted Motzkin rows form a Sturm chain"

[[theorems]]
name = "RealRooted.motzkinWeightedRow_inv_ascPochhammer_strictInterl_succ"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "The Sturm chain for γ_m = 1/(α)_m"

[[theorems]]
name = "RealRooted.motzkinWeightedRow_inv_ascPochhammer_succ_strictInterl"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "Monotonicity in α"

[[theorems]]
name = "RealRooted.motzkinAscentRow_strictInterl_succ"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "The rows with weights 1/(m+1)! form a Sturm chain"

[[theorems]]
name = "RealRooted.IsPFPolynomial.balancedRunTransform"
module = "RealRooted.BalancedRunTransformation.Preservation"
label = "The balanced run transformation maps PF polynomials of low degree to PF polynomials"

[[theorems]]
name = "RealRooted.strictInterl_balancedRunTransform"
module = "RealRooted.BalancedRunTransformation.Interlacing"
label = "The balanced run transformation preserves interlacing on low-degree inputs"
-->

<!-- realrooted-catalog-content -->
# Binary-run transformation preserving PF polynomials and interlacing

For each $n$, the binary-run transformation $J_n$ maps PF polynomials of degree at most $n$ to
PF polynomials, and preserves interlacing on inputs of degree at most $(n+1)/2$.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
A polynomial is *PF* (Pólya frequency) if it is zero or has nonnegative coefficients and only
real, nonpositive roots. Let $J_n$ be the linear map with $J_n(1)=1$ and, for $1\le m\le n$,
$$
J_n(x^m)=\frac1{\binom nm}\sum_k\binom{m-1}{k-1}\binom{n+1-m}{k}x^k .
$$

**Theorem (preservation).** If $p$ is PF with $\deg p\le n$, then $J_np$ is PF. If moreover
$p(0)>0$, then $J_np$ is real-rooted and all its roots are negative [@BorceaBranden2009I].

**Theorem (interlacing).** If $f\ll g$ have nonnegative coefficients and
$\deg g\le\lfloor(n+1)/2\rfloor$, then $J_nf\ll J_ng$.

**Theorem (interlacing across lengths).** Let $\Theta=x\,d/dx$. If $g$ is PF with $g(0)\ne0$
and $2\le\deg g$ and $2\deg g\le n+1$, then
$$
J_n\bigl((n+1)g-2\Theta g\bigr)\ll J_{n+1}(g).
$$

**Theorem (Motzkin-type rows).** Let $\gamma$ be a PF multiplier sequence with $\gamma_m>0$
for all $m$. Put
$$
G_n^\gamma(t)=\sum_{0\le m\le n/2}\frac{n!\,\gamma_m}{m!\,(n-2m)!}\,t^m,\qquad
R_n^\gamma=J_n\bigl(G_n^\gamma\bigr).
$$
Then $R_n^\gamma\ll R_{n+1}^\gamma$ for all $n$. This applies to $\gamma_m=1/(\alpha)_m$ for
every $\alpha>0$, where $(\alpha)_m=\alpha(\alpha+1)\cdots(\alpha+m-1)$. Writing
$R_n^{(\alpha)}$ for these rows, $R_n^{(\alpha+1)}\ll R_n^{(\alpha)}$ for all $n$ and
$\alpha>0$. The case $\alpha=2$, $\gamma_m=1/(m+1)!$, gives the Motzkin ascent polynomials.

**Theorem (balanced run transformation).** Let $n\ge2$, and let $K_n$ be the linear map with
$$
K_n(x^m)=\frac1{\binom nm}\sum_k\binom mk\binom{n-m}{k}x^k .
$$
If $p$ is PF and $\deg p\le\lfloor(n+1)/2\rfloor$, then $K_np$ is PF. If $f\ll g$ have
nonnegative coefficients and $\deg g\le\lfloor(n+1)/2\rfloor$, then $K_nf\ll K_ng$.

## Use

The map $x^m\mapsto\frac1{m+1}\binom nm J_n(x^m)$ is $J_n$ composed with a diagonal multiplier
sequence. Combined with the preservation of PF polynomials by that multiplier, the preservation
theorem gives the [Narayana transformation theorem](/RealRooted/families/narayana/)
[@MaoWang2026x]. The rows $R_n^\gamma$ for $\gamma_m=1/(m+1)!$ are the Motzkin ascent polynomials
(OEIS A114580).

## Proof

After scaling the input factors, a stable pointing construction controls the motion of every
critical value of the output. A polarized path-matching polynomial gives the small-parameter
anchor, and the sign of the critical value prevents collisions along the deformation.

## References

The preservation theorem is proved with the algebraic-symbol method of [@BorceaBranden2009I].
<!-- /realrooted-catalog-content -->

This module exposes the strictly negative root corollary of the checked
preservation theorem `RealRooted.IsPFPolynomial.binaryRunTransform`. The
stability, contraction, anchor, and continuation arguments remain in
`RealRooted.BinaryRunTransformation`.
-/
