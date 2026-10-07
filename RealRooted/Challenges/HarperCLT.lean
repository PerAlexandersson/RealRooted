import RealRooted.Mathlib.Probability.CoeffDistribution
import RealRooted.CombinatorialExamples.EulerianNormal
import RealRooted.CombinatorialExamples.NarayanaNormal
import RealRooted.CombinatorialExamples.StirlingPermutationsNormal

/-!
# Harper's central limit theorem challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "harper-clt"
authors = ["Harper", "Bender", "Goncharov"]
years = [1944, 1967, 1973]

[[definitions]]
name = "Polynomial.standardizedCoeffDistribution"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Standardized coefficient distribution of a polynomial"

[[theorems]]
name = "Polynomial.coeffVariance_eq_sum"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Real-rooted coefficient distributions are Bernoulli sums"

[[theorems]]
name = "Polynomial.tendsto_standardizedCoeffDistribution"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Harper: real-rooted coefficient distributions are asymptotically normal"
headline = true

[[theorems]]
name = "Polynomial.tendsto_standardizedCoeffDistribution_one_add_X_pow"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "De Moivre–Laplace: the binomial distribution is asymptotically normal"

[[theorems]]
name = "Polynomial.tendsto_standardizedCoeffDistribution_prod_range"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Products of real-rooted factors with divergent total variance are asymptotically normal"

[[theorems]]
name = "Polynomial.tendsto_standardizedCoeffDistribution_prod_X_add_natCast"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Goncharov: Stirling numbers of the first kind are asymptotically normal"

[[theorems]]
name = "RealRooted.tendsto_standardizedCoeffDistribution_eulerianTilde"
module = "RealRooted.CombinatorialExamples.EulerianNormal"
label = "The Eulerian numbers are asymptotically normal"

[[theorems]]
name = "RealRooted.tendsto_standardizedCoeffDistribution_generalizedEulerian_two"
module = "RealRooted.CombinatorialExamples.EulerianNormal"
label = "The type B Eulerian numbers are asymptotically normal"

[[theorems]]
name = "RealRooted.tendsto_standardizedCoeffDistribution_narayana"
module = "RealRooted.CombinatorialExamples.NarayanaNormal"
label = "The Narayana numbers are asymptotically normal"

[[theorems]]
name = "RealRooted.tendsto_standardizedCoeffDistribution_stirlingPermutations"
module = "RealRooted.CombinatorialExamples.StirlingPermutationsNormal"
label = "The second-order Eulerian numbers are asymptotically normal"
-->

<!-- realrooted-catalog-content -->
# Harper's central limit theorem

For a polynomial $p$ with nonnegative coefficients, its **coefficient
distribution** puts mass $p_k / p(1)$ at $k$. Its mean and variance are
$$
\mu(p) = \frac{p'(1)}{p(1)}, \qquad
\sigma^2(p) = \frac{p''(1)}{p(1)} + \mu(p) - \mu(p)^2 .
$$

If $p$ is real-rooted, its roots $-r_i$ are nonpositive and
$p(x)/p(1) = \prod_i (1 - q_i + q_i x)$ with $q_i = 1/(1 + r_i)$. So the
coefficient distribution is that of a sum of independent Bernoulli variables,
with $\mu = \sum_i q_i$ and $\sigma^2 = \sum_i q_i (1 - q_i)$.

**Theorem** (Harper; Bender). Let $P_n$ be real-rooted polynomials with
nonnegative coefficients and $\sigma^2(P_n) \to \infty$. Then the standardized
coefficient distributions, the laws of $(K_n - \mu_n)/\sigma_n$, converge weakly
to the standard normal distribution.

For example, $(1 + x)^n$ has variance $n/4$, which recovers the de
Moivre–Laplace theorem for the binomial distribution.

The Eulerian polynomials, with coefficients $A(n+1, k)$, have mean
$(n+2)/2$ and variance $(n+2)/12$, so the Eulerian numbers are asymptotically
normal. Both moments follow from scalar recurrences at $x = 1$. The type $B$
Eulerian numbers have mean $n/2$ and variance $(n+1)/12$, so they are
asymptotically normal as well.

The Narayana polynomials satisfy
$(n+3) Q_{n+2} = (2n+3)(1+x) Q_{n+1} - n(1-x)^2 Q_n$. The last term vanishes to
second order at $x = 1$, so the same method gives mean $(n-1)/2$ and variance
$(n^2-1)/(4(2n-1))$. Hence the Narayana numbers are asymptotically normal.

The descent polynomials of Stirling permutations satisfy
$P_{n+1} = (2n+1) x P_n + x(1-x) P_n'$. Their coefficients, the second-order
Eulerian numbers, have mean $(2n+1)/3$ and variance $2(n^2-1)/(9(2n-1))$ for
$n \ge 1$, so they are asymptotically normal too.

Variances add under multiplication, so a product $\prod_{i<n} L_i$ of
real-rooted factors with nonnegative coefficients is asymptotically normal as
soon as $\sum_i \sigma^2(L_i) \to \infty$. For $L_i = x + i$ the variance is
$i/(i+1)^2 \ge 1/(2(i+1))$ for $i \ge 1$, and the harmonic series diverges. This
gives Goncharov's theorem: the unsigned Stirling numbers of the first kind, which
count permutations of $[n]$ by number of cycles, are asymptotically normal.

## Proof idea

The characteristic function of the standardized distribution is a product of
centred Bernoulli factors. Each factor differs from
$\exp(-q_i(1-q_i)t^2/2\sigma^2)$ by at most $2q_i(1-q_i)|t|^3/\sigma^3$, so the
product is within $2|t|^3/\sigma$ of $e^{-t^2/2}$. Lévy's continuity theorem
turns pointwise convergence of characteristic functions into weak convergence.

## References

L. H. Harper, “Stirling behavior is asymptotically normal,” *Annals of
Mathematical Statistics* 38 (1967), 410–414; E. A. Bender, “Central and local
limit theorems applied to asymptotic enumeration,” *Journal of Combinatorial
Theory, Series A* 15 (1973), 91–111; V. L. Goncharov, “Some facts from
combinatorics,” *Izv. Akad. Nauk SSSR Ser. Mat.* 8 (1944), 3–48.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Mathlib.Probability.CoeffDistribution`.
-/
