module

import RealRooted.RootAmplitude.Convex
import RealRooted.RootAmplitude.Density
import RealRooted.RootAmplitude.Minimum
import RealRooted.RootAmplitude.Separation.Euler
import RealRooted.RootAmplitude.Separation.Finite
import RealRooted.RootAmplitude.Separation.Polynomial
import RealRooted.RootAmplitude.SmallestRoot
import RealRooted.RootAmplitude.SumSquares

/-!
# Root amplitudes and separated roots

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "root-amplitude"
formalized = "2026-09-08"
authors = []
tags = []
references = [
  "Kozlov2022",
]

[[theorems]]
name = "RealRooted.RootAmplitude.exp_neg_pi_sq_div_three_le_abs_eval_deriv_of_root_separation"
module = "RealRooted.RootAmplitude.Separation.Polynomial"
label = "Derivative bound from separated roots"
headline = true

[[theorems]]
name = "RealRooted.RootAmplitude.amplitude_at_smallest_root"
module = "RealRooted.RootAmplitude.SmallestRoot"
label = "One-fifth bound at the smallest root"

[[theorems]]
name = "RealRooted.RootAmplitude.exp_gain_le_amplitude_of_separation"
module = "RealRooted.RootAmplitude.Separation.Euler"
label = "Index-dependent bound for separated sequences"

[[theorems]]
name = "RealRooted.RootAmplitude.exp_neg_pi_sq_div_three_le_amplitude_of_separation"
module = "RealRooted.RootAmplitude.Separation.Euler"
label = "Uniform bound for separated sequences"

[[theorems]]
name = "RealRooted.RootAmplitude.amplitude_zero_le"
module = "RealRooted.RootAmplitude.Minimum"
label = "The smallest amplitude is minimal"

[[theorems]]
name = "RealRooted.RootAmplitude.amplitude_le_amplitude_of_sum"
module = "RealRooted.RootAmplitude.Minimum"
label = "Monotonicity from reciprocal-distance sums"

[[theorems]]
name = "RealRooted.RootAmplitude.amplitude_le_amplitude_of_convex"
module = "RealRooted.RootAmplitude.Convex"
label = "Monotonicity from convex gaps"

[[theorems]]
name = "RealRooted.RootAmplitude.gap_le_gap_of_criterion"
module = "RealRooted.RootAmplitude.Density"
label = "Convexity from logarithmic gaps"

[[theorems]]
name = "RealRooted.RootAmplitude.gap_le_gap_of_two_le"
module = "RealRooted.RootAmplitude.Density"
label = "Convexity from a large logarithmic gap"

[[theorems]]
name = "RealRooted.RootAmplitude.amplitude_at_smallest_root_of_sq_ratio"
module = "RealRooted.RootAmplitude.SmallestRoot"
label = "Smallest-root bound from a square ratio"

[[theorems]]
name = "RealRooted.RootAmplitude.amplitude_of_sum_sq"
module = "RealRooted.RootAmplitude.SumSquares"
label = "Amplitude bound from reciprocal squares"

[[theorems]]
name = "RealRooted.RootAmplitude.abs_eval_deriv_root_div_eval_zero_eq_amplitude"
module = "RealRooted.RootAmplitude.Separation.Polynomial"
label = "Derivative amplitude identity"

[[theorems]]
name = "RealRooted.RootAmplitude.amplitude_eq_lower_mul_upper"
module = "RealRooted.RootAmplitude.Separation.Finite"
label = "Lower and upper factors of an amplitude"

[[theorems]]
name = "RealRooted.RootAmplitude.IsMultiplicativelySeparatedOn.pow_le_ratio"
module = "RealRooted.RootAmplitude.Separation.Finite"
label = "Iterated multiplicative separation"

[[theorems]]
name = "RealRooted.RootAmplitude.IsMultiplicativelySeparatedOn.strictMonoOnRange"
module = "RealRooted.RootAmplitude.Separation.Finite"
label = "Strict increase from separation"
-->

<!-- realrooted-catalog-content -->
# Root amplitudes and separated roots

If the negative roots of a real-rooted polynomial are multiplicatively separated, then
$|s\,p'(s)|/p(0)$ is bounded below at every root $s$.

## Results

For a finite positive sequence $(g_j)_{j<n}$, the *amplitude* at $k$ is
$$\operatorname{amp}_k=\prod_{j\ne k}\Bigl|1-\frac{g_k}{g_j}\Bigr|.$$
The sequence is *$q$-separated* if $qg_i\le g_{i+1}$ for $i+1<n$. The $j$-th smallest
magnitude of a root of $p$ is $\mu_j$, counted with multiplicity.

**Theorem (separated roots).** Let $p$ be real-rooted with $p(0)\ne0$ and all roots negative,
let $d>0$, and suppose $(\mu_j)$ is $e^d$-separated. Then for every root index $k$
$$\Bigl|\frac{\mu_k\,p'(-\mu_k)}{p(0)}\Bigr|\ \ge\ e^{-\pi^2/(3d)}.$$
For a positive $e^d$-separated sequence $(g_j)_{j<n}$ and $k<n$,
$$\operatorname{amp}_k\ \ge\ e^{\,dk(k+1)/2-\pi^2/(3d)}\ \ge\ e^{-\pi^2/(3d)}.$$
For real-rooted $p$ with simple roots and $p(0)\ne0$, the left side of the first display
equals $\operatorname{amp}_k$ for $g_j=\mu_j$.

**Theorem (smallest root).** Let $p$ be real-rooted with $p(0)>0$ and all roots negative, and let
$s$ be a simple root of smallest magnitude. If $c>\tfrac12$ and
$$c\Bigl(\sum_r\frac1r\Bigr)^2\le\sum_r\frac1{r^2}$$
over the roots $r$ of $p$, then $|s\,p'(s)|\ge p(0)\,(2c-1)/c$. If
$\tfrac92a_0a_2\le a_1^2$ for the first three coefficients, which is the case $c=\tfrac59$,
then $|s\,p'(s)|\ge p(0)/5$.

**Theorem (square sums).** Let $\xi_j<0$ and $w_j$ be reals with $\xi_jw_j\ne0$ over a finite
index set, and let $N>0$ with $\sum_j(\xi_jw_j)^{-2}<N^{-2}$. Then
$N<|\xi_k(1-\xi_k)w_k|$ for every $k$.

**Theorem (monotone amplitudes).** Let $g$ be positive and strictly increasing.

- If $k+1<n$, $n\le2k+2$ and the consecutive gaps $g_{i+1}-g_i$ are nondecreasing, then
  $\operatorname{amp}_k\le\operatorname{amp}_{k+1}$.
- If $k+1<n$ and
  $\sum_{j=k+2}^{n-1}\frac1{g_j-g_{k+1}}\le\frac1{g_{k+1}}+\sum_{j<k}\frac1{g_{k+1}-g_j}$,
  then $\operatorname{amp}_k\le\operatorname{amp}_{k+1}$.
- If the gaps are nondecreasing and the tail products
  $\prod_{j=2k+2}^{n-1}\bigl(1+\frac{g_{k+1}-g_k}{g_j-g_{k+1}}\bigr)\le1+\frac{g_{k+1}-g_k}{g_k}$
  hold whenever $k+1<n$, then $\operatorname{amp}_0\le\operatorname{amp}_k$ for all $k<n$.

**Proposition (gap convexity).** Let $g$ be positive and $\ell_k=\log(g_{k+1}/g_k)$. Then
$g_{k+1}-g_k\le g_{k+2}-g_{k+1}$ if either $\ell_k\ge0$ and
$\ell_{k+1}\ge2\ell_k/(2+\ell_k)$, or $\ell_k>0$ and $\ell_{k+1}\ge2$.

**Proposition (factorization and separation).** For a positive strictly increasing sequence,
$$\operatorname{amp}_k=\prod_{i<k}\Bigl(\frac{g_k}{g_i}-1\Bigr)\prod_{j=k+1}^{n-1}
\Bigl(1-\frac{g_k}{g_j}\Bigr).$$
If $(g_j)$ is positive and $q$-separated with $q\ge0$, then $g_k/g_i\ge q^{k-i}$ for
$i\le k<n$, and $g$ is strictly increasing if $q>1$.

## References

These results arose in a proof that the rows of [OEIS A366159](https://oeis.org/A366159) are
real-rooted and interlace. The combinatorial objects are the Stirling complexes [@Kozlov2022].
<!-- /realrooted-catalog-content -->
-/
