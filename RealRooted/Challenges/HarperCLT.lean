import RealRooted.Mathlib.Probability.CoeffDistribution

/-!
# Harper's central limit theorem challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "harper-clt"
authors = ["Harper", "Bender"]
years = [1967, 1973]

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
Theory, Series A* 15 (1973), 91–111.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Mathlib.Probability.CoeffDistribution`.
-/
