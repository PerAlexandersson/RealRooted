module

import RealRooted.CoefficientShape.LocalLimit
import RealRooted.CombinatorialExamples.DerangementsExcNormal
import RealRooted.CombinatorialExamples.EulerianNormal
import RealRooted.CombinatorialExamples.NarayanaNormal
import RealRooted.CombinatorialExamples.StirlingPermutationsNormal
import RealRooted.Mathlib.Probability.CoeffDistribution
import RealRooted.Mathlib.Probability.LocalLimit
import RealRooted.ThreeTermRecurrence.Moments

/-!
# Central limit theorems for real-rooted coefficient distributions

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "harper-clt"
formalized = "2026-10-12"
references = [
  "Bender1973",
  "Bona2009",
  "Harper1967",
]
authors = ["Harper", "Bender", "Goncharov", "David", "Barton", "Bóna"]
years = [1944, 1962, 1967, 1973, 2009]

[[definitions]]
name = "Polynomial.standardizedCoeffDistribution"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Standardized coefficient distribution of a polynomial"

[[theorems]]
name = "Polynomial.tendsto_standardizedCoeffDistribution"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Harper: real-rooted coefficient distributions with divergent variance are normal"

[[theorems]]
name = "Polynomial.tendsto_localLimit_of_splits"
module = "RealRooted.CoefficientShape.LocalLimit"
label = "Bender: real-rooted coefficient rows with divergent variance obey a local limit law"
headline = true

[[theorems]]
name = "Polynomial.tendsto_localLimit_of_logConcave"
module = "RealRooted.Mathlib.Probability.LocalLimit"
label = "Bender: log-concave rows satisfying a central limit theorem obey a local limit law"

[[theorems]]
name = "Polynomial.tendsto_standardizedCoeffDistribution_prod_range"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Products of real-rooted factors with divergent total variance are asymptotically normal"

[[theorems]]
name = "Polynomial.tendsto_standardizedCoeffDistribution_prod_X_add_natCast"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Goncharov: Stirling numbers of the first kind are asymptotically normal"

[[theorems]]
name = "RealRooted.ThreeTermRecurrence.tendsto_derivative_eval_div_nat_mul_eval"
module = "RealRooted.ThreeTermRecurrence.Moments"
label = "Three-term recurrences: the mean grows like n λ'/λ"

[[theorems]]
name = "RealRooted.ThreeTermRecurrence.tendsto_variance_eval_div_nat"
module = "RealRooted.ThreeTermRecurrence.Moments"
label = "Three-term recurrences: the variance grows linearly"

[[theorems]]
name = "RealRooted.tendsto_standardizedCoeffDistribution_eulerianTilde"
module = "RealRooted.CombinatorialExamples.EulerianNormal"
label = "The Eulerian numbers are asymptotically normal"

[[theorems]]
name = "RealRooted.tendsto_standardizedCoeffDistribution_narayana"
module = "RealRooted.CombinatorialExamples.NarayanaNormal"
label = "The Narayana numbers are asymptotically normal"

[[theorems]]
name = "RealRooted.tendsto_standardizedCoeffDistribution_stirlingPermutations"
module = "RealRooted.CombinatorialExamples.StirlingPermutationsNormal"
label = "The second-order Eulerian numbers are asymptotically normal"

[[theorems]]
name = "RealRooted.tendsto_standardizedCoeffDistribution_sturmDerangementsExc"
module = "RealRooted.CombinatorialExamples.DerangementsExcNormal"
label = "Excedances of derangements are asymptotically normal"
-->

<!-- realrooted-catalog-content -->
# Central limit theorems for real-rooted coefficient distributions

If a real-rooted polynomial has nonnegative coefficients, its coefficient distribution is that of
a sum of independent Bernoulli variables. Hence the coefficients of such polynomials are
asymptotically normal, also in the local sense, as soon as the variance diverges.

## Results

For a polynomial $p$ with nonnegative coefficients and $p(1)\ne0$, the *coefficient distribution*
puts mass $p_k/p(1)$ at $k$. If $p$ is real-rooted with roots $-r_i\le0$, then
$p(x)/p(1)=\prod_i(1-q_i+q_ix)$ with $q_i=1/(1+r_i)$, so the mean is $\mu=\sum_iq_i$ and the
variance is $\sigma^2=\sum_iq_i(1-q_i)$.

**Theorem (Harper).** [@Harper1967; @Bender1973] Let $P_n$ be real-rooted polynomials with
nonnegative coefficients and $\sigma^2(P_n)\to\infty$. Then the standardized coefficient
distributions of $P_n$ converge weakly to the standard normal distribution.

**Theorem (Bender, local limit).** [@Bender1973, Thm. 2] Under the same hypotheses, with
$\varphi$ the standard Gaussian density,
$$
\sup_{k\ge0}\left|\sigma_n\,\frac{[x^k]P_n(x)}{P_n(1)}
-\varphi\!\left(\frac{k-\mu_n}{\sigma_n}\right)\right|\longrightarrow0
\qquad(n\to\infty).
$$
More generally, this holds for nonzero $P_n$ with log-concave nonnegative coefficients without
internal zeros, $\sigma^2(P_n)\to\infty$, and asymptotically normal coefficient distributions.

**Corollary (products; Goncharov).** If $L_i$ are real-rooted with nonnegative coefficients and
$\sum_{i<n}\sigma^2(L_i)\to\infty$, then the coefficients of $\prod_{i<n}L_i$ are asymptotically
normal. For $\prod_{i<n}(x+i)$ this is Goncharov's theorem on the Stirling numbers of the first
kind.

**Theorem (three-term recurrences; Bender).** Let $P_{n+2}=a\,P_{n+1}+b\,P_n$ with polynomials
$a,b$ independent of $n$, and let $\lambda(x)$ be the dominant root of $t^2=a(x)t+b(x)$ near
$x=1$, under a nondegeneracy condition on $P_0,P_1$. Then
$$
\frac{\mu(P_n)}n\to\frac{\lambda'}{\lambda},\qquad
\frac{\sigma^2(P_n)}n\to\frac{\lambda''}{\lambda}+\frac{\lambda'}{\lambda}-
\Bigl(\frac{\lambda'}{\lambda}\Bigr)^2\qquad\text{at }x=1.
$$

**Corollary (examples).** The following coefficient sequences are asymptotically normal: the
Eulerian numbers (David and Barton), the [Narayana numbers](rr:narayana), the second-order
Eulerian numbers [@Bona2009], and the derangement numbers refined by excedances.

## Use

Real-rootedness gives normal limit laws without computing a generating function: it suffices that
the variance diverges, and for recurrences Bender's formulas give the variance.

## Proof

The characteristic function of the standardized distribution is a product of centred Bernoulli
factors, and it is within $2|t|^3/\sigma$ of $e^{-t^2/2}$; Lévy's continuity theorem gives weak
convergence. For the local limit, log-concavity without internal zeros makes the coefficients
unimodal, so weak convergence makes window sums of coefficients uniformly close to Gaussian
integrals.

## References

[@Harper1967]; [@Bender1973, Thm. 2]; [@Bona2009]; V. L. Goncharov, “Some facts from
combinatorics,” *Izv. Akad. Nauk SSSR Ser. Mat.* 8 (1944), 3–48; F. N. David and
D. E. Barton, *Combinatorial Chance*, Griffin, London, 1962.
<!-- /realrooted-catalog-content -->
-/
