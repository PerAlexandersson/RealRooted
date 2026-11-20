module

import RealRooted.Mathlib.Analysis.Complex.Hurwitz
import RealRooted.Mathlib.Analysis.Complex.LimitsOfZeros
import RealRooted.ThreeTermRecurrence.OrderTwoLimitZeros
import RealRooted.ThreeTermRecurrence.WangZhang
import RealRooted.EffectiveBKW.ZeroCount
import RealRooted.EffectiveBKW.Examples.Chebyshev
import RealRooted.EffectiveBKW.Tiling4.Theorem
import RealRooted.EffectiveBKW.PathCube.Proof

/-!
# Limits of zeros of recursive families

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "limits-of-zeros"
formalized = "2026-10-27"
references = [
  {key = "Sokal2004ChromaticRoots", at = "Thm. 1.5"},
  {key = "WangZhang2017RootGeometryIII", at = "Thm. 2.1"},
  {key = "Torres2026x", at = "Prop. 5.7, Thm. 7.1"},
]
authors = ["Beraha", "Kahane", "Weiss", "Sokal", "Wang", "Zhang", "Torres"]
years = [2004, 2017, 2026]

[[definitions]]
name = "Complex.IsLimitOfZeros"
module = "RealRooted.Mathlib.Analysis.Complex.Hurwitz"
label = "Limit of zeros of a sequence of functions"

[[theorems]]
name = "Complex.isLimitOfZeros_finset_two_dominant"
module = "RealRooted.Mathlib.Analysis.Complex.Hurwitz"
label = "Beraha–Kahane–Weiss–Sokal: two dominant bases of equal modulus give a limit of zeros"
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
label = "Wang–Zhang: W(n+2) = (ax + b)W(n+1) + (cx + d)W(n) is real-rooted iff ad ≤ bc"

[[theorems]]
name = "RealRooted.EffectiveBKW.PairExpansion.splits_nodup_forall_ge"
module = "RealRooted.EffectiveBKW.ZeroCount"
label = "Effective BKW: a dominating pair and its phase crossings give simple real zeros for n ≥ N"

[[theorems]]
name = "RealRooted.EffectiveBKW.Examples.Chebyshev.splits_nodup"
module = "RealRooted.EffectiveBKW.Examples.Chebyshev"
label = "Effective BKW, order two: the rows of 1/(1 − 2tz + z²)"

[[theorems]]
name = "RealRooted.EffectiveBKW.Tiling4.polynomial_roots"
module = "RealRooted.EffectiveBKW.Tiling4.Theorem"
label = "Effective BKW, order three: tilings of a 4 × n strip by 1 × 1 and 2 × 2 squares"

[[theorems]]
name = "RealRooted.EffectiveBKW.PathCube.row_splits_nodup"
module = "RealRooted.EffectiveBKW.PathCube.Proof"
label = "Effective BKW, order four: a four-state transfer family with a certified remainder bound"
-->

<!-- realrooted-catalog-content -->
# Limits of zeros of recursive families

The zeros of $f_n=\sum_k\alpha_k\beta_k^n$ accumulate where two dominant bases have equal
modulus or where the dominant coefficient vanishes. For polynomials given by a linear
recurrence, a nonreal accumulation point shows that the late members are not real-rooted.

## Results

A point $z_0$ is a *limit of zeros* of $(F_n)$ if every ball around $z_0$ contains a zero of
$F_n$ for all large $n$. Let $f_n=\sum_{k\in s}\alpha_k\beta_k^n$ with $s$ finite and
$\alpha_k,\beta_k$ analytic at $z_0$.

**Theorem (Beraha–Kahane–Weiss, Sokal).** [@Sokal2004ChromaticRoots, Thm. 1.5] The point
$z_0$ is a limit of zeros of $(f_n)$ in each of these cases:

- two bases $\beta_i,\beta_j$ have equal modulus at $z_0$, larger than that of every other
  base, $\alpha_i(z_0)\alpha_j(z_0)\beta_j(z_0)\ne0$, and $\beta_i/\beta_j$ is not constant
  near $z_0$;
- one base $\beta_i\ne0$ is strictly dominant at $z_0$, and $\alpha_i(z_0)=0$ while $\alpha_i$
  does not vanish identically near $z_0$.

Conversely, at a limit of zeros two bases have equal maximal modulus, or the strictly dominant
coefficient vanishes, or all bases vanish.

**Corollary (order-two recurrences).** Let $W_{n+2}=A\,W_{n+1}+B\,W_n$ with characteristic roots
$u\ne v$ near $z_0$. If $|u(z_0)|=|v(z_0)|$, $u/v$ is not constant and both coefficients of
$W_n=c_uu^n+c_vv^n$ are nonzero at $z_0$, then $z_0$ is a limit of zeros. If $|u(z_0)|\ne
|v(z_0)|$ and the dominant coefficient is nonzero, it is not. If real polynomials $W_n$ have a
nonreal limit of zeros, then $W_n$ is not real-rooted for all large $n$.

**Theorem (Wang–Zhang).** [@WangZhang2017RootGeometryIII, Thm. 2.1] Let $a,b,c,d>0$, $W_0=1$,
$W_1=x$ and $W_{n+2}=(ax+b)\,W_{n+1}+(cx+d)\,W_n$. Then every $W_n$ is real-rooted if and only
if $ad\le bc$.

**Effective version.** [@Torres2026x, Prop. 5.7, Thm. 7.1] A sign-changing version of the same picture proves
real-rootedness for every $n$, not only in the limit. Write $P_n=2\operatorname{Re}(A\lambda^n)
+r_n$ on an interval $J$ with a conjugate pair $\lambda,\bar\lambda$. If $|r_n|<2|A\lambda^n|$
on $J$ for $n\ge N$, then $P_n$ has the sign of $\cos\varphi$ wherever the phase
$\varphi=\arg(A\lambda^n)$ is a multiple of $\pi$, so consecutive multiples give sign changes.
Counting them and closing with the degree gives simple real zeros in $J$.
The remaining rows $n<N$ are checked exactly. This is the method of Torres's proof of the zig-zag
Eulerian conjecture, here as a general theorem with an explicit domination cutoff.
Applications: the Chebyshev rows of $1/(1-2tz+z^2)$, the tilings of a $4\times n$ strip by
$1\times1$ and $2\times2$ squares (with generating function
$(1-tz)/(1-(1+t)z-(2t+t^2)z^2+(t^2+t^3)z^3)$), and a four-state transfer family
$1,\ 1+t,\ 1+4t+t^2,\ 1+11t+11t^2+t^3,\dots$ with an exact certified remainder bound.

## Use

This is the standard tool for showing that a recursive family is not real-rooted: one exhibits
a nonreal point where the two characteristic roots have equal modulus. For $ad>bc$ this gives
the "only if" direction of the Wang–Zhang theorem.

## References

[@Sokal2004ChromaticRoots, Thm. 1.5], which generalizes the Beraha–Kahane–Weiss theorem;
[@WangZhang2017RootGeometryIII, Thm. 2.1]; [@Torres2026x, Prop. 5.7, Thm. 7.1] for the effective version.
<!-- /realrooted-catalog-content -->
-/
