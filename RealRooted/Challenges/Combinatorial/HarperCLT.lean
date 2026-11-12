module

import RealRooted.Mathlib.Probability.CoeffDistribution
import RealRooted.CombinatorialExamples.DerangementsExcNormal
import RealRooted.CombinatorialExamples.EulerianNormal
import RealRooted.CombinatorialExamples.NarayanaNormal
import RealRooted.CombinatorialExamples.StirlingPermutationsNormal
import RealRooted.CoefficientShape.LocalLimit
import RealRooted.ThreeTermRecurrence.Moments

/-!
# Central limit theorems for real-rooted coefficient distributions

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "harper-clt"
formalized = "2026-10-12"
tags = []
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
name = "Polynomial.coeffVariance_eq_sum"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Variance of a real-rooted coefficient distribution is Σᵢ qᵢ(1 − qᵢ)"

[[theorems]]
name = "Polynomial.tendsto_standardizedCoeffDistribution"
module = "RealRooted.Mathlib.Probability.CoeffDistribution"
label = "Harper: real-rooted coefficient distributions are asymptotically normal"

[[theorems]]
name = "Polynomial.tendsto_localLimit_of_splits"
module = "RealRooted.CoefficientShape.LocalLimit"
label = "Bender: real-rooted coefficient rows satisfy a local limit theorem"
headline = true

[[theorems]]
name = "Polynomial.tendsto_localLimit_of_logConcave"
module = "RealRooted.Mathlib.Probability.LocalLimit"
label = "Bender: log-concave rows satisfying a CLT satisfy a local limit theorem"

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
name = "RealRooted.GeneralizedEulerian.tendsto_standardizedCoeffDistribution_two"
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

[[theorems]]
name = "RealRooted.tendsto_standardizedCoeffDistribution_sturmDerangementsExc"
module = "RealRooted.CombinatorialExamples.DerangementsExcNormal"
label = "Excedances of derangements are asymptotically normal"

[[theorems]]
name = "RealRooted.ThreeTermRecurrence.tendsto_derivative_eval_div_nat_mul_eval"
module = "RealRooted.ThreeTermRecurrence.Moments"
label = "Three-term recurrences: the mean grows like n λ'/λ"

[[theorems]]
name = "RealRooted.ThreeTermRecurrence.tendsto_variance_eval_div_nat"
module = "RealRooted.ThreeTermRecurrence.Moments"
label = "Three-term recurrences: the variance grows linearly"
-->

<!-- realrooted-catalog-content -->
# Central limit theorems for real-rooted coefficient distributions

The coefficients of a real-rooted polynomial with nonnegative coefficients are asymptotically
normal as soon as their variance diverges; the Eulerian, type $B$ Eulerian, Narayana,
second-order Eulerian and derangement excedance numbers and the Stirling numbers of the first
kind are examples.

## Results

For a polynomial $p$ with nonnegative coefficients and $p(1)\ne0$, the *coefficient distribution*
puts mass $p_k/p(1)$ at $k$. Its mean and variance are
$$
\mu(p)=\frac{p'(1)}{p(1)},\qquad
\sigma^2(p)=\frac{p''(1)}{p(1)}+\mu(p)-\mu(p)^2 .
$$
If $p$ is real-rooted with roots $-r_i\le0$, then $p(x)/p(1)=\prod_i(1-q_i+q_ix)$ with
$q_i=1/(1+r_i)$. The coefficient distribution is that of a sum of independent Bernoulli
variables, with $\mu=\sum_iq_i$ and $\sigma^2=\sum_iq_i(1-q_i)$.

**Theorem (Harper; Bender).** Let $P_n$ be real-rooted polynomials with nonnegative coefficients
and $\sigma^2(P_n)\to\infty$. Then the laws of $(K_n-\mu_n)/\sigma_n$, where $K_n$ has the
coefficient distribution of $P_n$, converge weakly to the standard normal distribution
[@Harper1967; @Bender1973].

**Theorem (Bender, local limit).** Let $P_n$ be nonzero real-rooted polynomials with nonnegative
coefficients and $\sigma^2(P_n)\to\infty$. Let $\mu_n,\sigma_n$ be the mean and standard
deviation of the coefficient distribution, and $\varphi$ the standard Gaussian density. Then
$$
\sup_{k\ge0}\left|\sigma_n\,\frac{[x^k]P_n(x)}{P_n(1)}
-\varphi\!\left(\frac{k-\mu_n}{\sigma_n}\right)\right|\longrightarrow0
\qquad(n\to\infty).
$$
More generally, the same holds for nonzero polynomials $P_n$ with nonnegative log-concave
coefficients without internal zeros, with $\sigma^2(P_n)\to\infty$, whose standardized coefficient
distributions converge weakly to the standard normal distribution [@Bender1973, Thm. 2].

**Theorem (products).** Let $L_i$ be real-rooted with nonnegative coefficients and $L_i(1)\ne0$.
If $\sum_{i<n}\sigma^2(L_i)\to\infty$, the standardized coefficient distributions of
$\prod_{i<n}L_i$ converge weakly to the standard normal distribution. For $(1+x)^n$ this is the
de Moivre–Laplace theorem. For $\prod_{i<n}(x+i)$, whose coefficients are the unsigned Stirling
numbers of the first kind, the factor $x+i$ has variance $i/(i+1)^2\ge1/(2(i+1))$ for $i\ge1$, and
the harmonic series diverges; this is Goncharov's theorem.

**Theorem (three-term recurrences).** Let $P_{n+2}=a\,P_{n+1}+b\,P_n$ with polynomials $a,b$
independent of $n$. Let $\lambda\ne\nu$ be the roots of $t^2=a(1)t+b(1)$ with $\lambda>|\nu|$ and
$\nu\ne0$, and assume that $\bigl(P_1(1)-\nu P_0(1)\bigr)/(\lambda-\nu)\ne0$. Let $\lambda(x)$ be
the root branch of $t^2=a(x)t+b(x)$ through $\lambda$. Then
$$
\frac{\mu(P_n)}n\to\frac{\lambda'(1)}{\lambda(1)},\qquad
\frac{\sigma^2(P_n)}n\to\frac{\lambda''}{\lambda}+\frac{\lambda'}{\lambda}-
\Bigl(\frac{\lambda'}{\lambda}\Bigr)^2\quad\text{at }x=1,
$$
where the limits are expressed algebraically in $a(1)$, $b(1)$ and their derivatives (Bender's
formulas).

**Examples.** Each family below has nonnegative real-rooted rows with variance tending to infinity,
so its coefficients are asymptotically normal.

- The Eulerian polynomials $P_n$ with coefficients $A(n+1,k)$ have mean $(n+2)/2$ and, for
  $n\ge1$, variance $(n+2)/12$ [David–Barton; Bender]. The type $B$ Eulerian polynomials have
  mean $n/2$ and, for $n\ge2$, variance $(n+1)/12$.
- Let $Q_n(x)=\sum_{k=0}^{n-1}N(n,k+1)x^k$, where $N(n,k)=\frac1n\binom nk\binom n{k-1}$. Thus
  $Q_n=N_{n-1,1}$ in the notation of the [Narayana page](/RealRooted/families/narayana/), and
  $(n+3)Q_{n+2}=(2n+3)(1+x)Q_{n+1}-n(1-x)^2Q_n$. For $n\ge1$, $Q_n$ has mean $(n-1)/2$ and
  variance $(n^2-1)/(4(2n-1))$.
- The descent polynomials of Stirling permutations satisfy $P_{n+1}=(2n+1)xP_n+x(1-x)P_n'$. Their
  coefficients, the second-order Eulerian numbers, have mean $(2n+1)/3$ and variance
  $2(n^2-1)/(9(2n-1))$ for $n\ge1$ [@Bona2009].
- The derangement excedance polynomials $d_n(x)=\sum_\sigma x^{\operatorname{exc}\sigma}$ have
  $d_n(1)=D_n$, the derangement number. For $n\ge2$ they have mean $n/2$ and variance
  $\frac{n-1}{12}\bigl(1-(-1)^n/D_n\bigr)$.

## Proof

The characteristic function of the standardized distribution is a product of centred Bernoulli
factors, and the product is within $2|t|^3/\sigma$ of $e^{-t^2/2}$; Lévy's continuity theorem gives
weak convergence. For the local limit theorem, log-concavity without internal zeros makes the
coefficients quasi-concave, and weak convergence with Pólya's theorem makes window sums of
coefficients uniformly close to Gaussian integrals.

## References

- [@Harper1967]
- [@Bender1973]
- [@Bona2009]
- V. L. Goncharov, “Some facts from combinatorics,” *Izv. Akad. Nauk SSSR Ser. Mat.* 8 (1944),
  3–48.
- F. N. David and D. E. Barton, *Combinatorial Chance*, Griffin, London, 1962.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Mathlib.Probability.CoeffDistribution`.
-/
