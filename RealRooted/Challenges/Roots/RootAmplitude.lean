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
headline = true

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

The normalized amplitude of a finite positive sequence $(g_j)_{j<n}$ at the
index $k$ is
$\operatorname{amp}_k=\prod_{j\neq k}\lvert1-g_k/g_j\rvert$. For a positive
strictly increasing sequence, `amplitude_le_amplitude_of_convex` proves
$\operatorname{amp}_k \leq \operatorname{amp}_{k+1}$ when $n \leq 2k+2$ and
the consecutive gaps are nondecreasing.
The stronger `amplitude_zero_le` iterates this comparison when the corresponding
tail estimates hold, while
`amplitude_le_amplitude_of_sum` uses reciprocal-distance sums instead of convexity.

We give two ways to verify the gap hypothesis. If the sequence is positive and
the first logarithmic gap is nonnegative, the inequality in
`gap_le_gap_of_criterion` implies convexity at the next index. The simpler
`gap_le_gap_of_two_le` applies when the upper logarithmic gap is at least two.
For a multiplicatively separated sequence, we iterate
$q g_i \le g_{i+1}$ to obtain a power bound on any later-to-earlier ratio
and strict increase when $q > 1$. The factorization
`amplitude_eq_lower_mul_upper` then separates an amplitude into its lower and upper
products, which leads to the Euler bounds in the catalog. For $q = \exp d$
with $d > 0$, `exp_gain_le_amplitude_of_separation` keeps the
triangular index-dependent gain, and its uniform version discards that gain.

We connect these finite products to split real polynomials. If the roots are
simple and the constant term is nonzero, the absolute normalized derivative at
the root indexed by the sorted magnitude sequence equals the corresponding
amplitude. Consequently, negative roots with multiplicative separation satisfy
the same uniform lower bound for the normalized derivative. At a root of
smallest magnitude, a reciprocal-square proportion $c>1/2$ gives the factor
$(2c-1)/c$. If $\tfrac92a_0a_2\leq a_1^2$ for the first three coefficients,
which is the case $c=\tfrac59$, the bound is
$|s\,p'(s)|\geq p(0)/5$. The abstract square-sum result gives the related
estimate for any finite family of negative factors.

## References

These results were extracted from a formal proof that the rows of
[OEIS A366159](https://oeis.org/A366159) are real-rooted and interlace. The
motivating combinatorial objects are the Stirling complexes [@Kozlov2022].
<!-- /realrooted-catalog-content -->
-/
