module

import RealRooted.CauchyInterlacing

/-!
# Courant–Fischer min-max theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "courant-fischer"
formalized = "2026-07-01"
references = [
  "Courant1920",
  "Fischer1905",
]
authors = ["Fischer", "Courant"]
years = [1905, 1920]

[[definitions]]
name = "RealRooted.sortedEigenvalues"
module = "RealRooted.CauchyInterlacing"
label = "Eigenvalues of a Hermitian matrix in decreasing order"

[[definitions]]
name = "RealRooted.rayleigh"
module = "RealRooted.CauchyInterlacing"
label = "Rayleigh quotient"

[[theorems]]
name = "RealRooted.courant_fischer"
module = "RealRooted.CauchyInterlacing"
label = "Courant–Fischer: the kth eigenvalue is a max-min of the Rayleigh quotient"
headline = true

[[theorems]]
name = "RealRooted.courantFischer_of_eigenbasis"
module = "RealRooted.CauchyInterlacing"
label = "Courant–Fischer from an orthonormal eigenbasis with antitone eigenvalues"
-->

<!-- realrooted-catalog-content -->
# Courant–Fischer min-max theorem

Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $A$ be a Hermitian
$N \times N$ matrix over $\mathbb K$ with eigenvalues
$\lambda_0 \geq \lambda_1 \geq \dotsb \geq \lambda_{N-1}$, listed with multiplicity.
The **Rayleigh quotient** of a vector $x \in \mathbb K^N$ is
$$
R_A(x) = \frac{\operatorname{Re}(x^* A x)}{\operatorname{Re}(x^* x)} .
$$

**Theorem** (Courant–Fischer). [@Courant1920; @Fischer1905] For every $k$ with $0 \leq k < N$:

1. there is a subspace $W \subseteq \mathbb K^N$ of dimension $k + 1$ such that
   $R_A(x) \geq \lambda_k$ for every nonzero $x \in W$;
2. every subspace $W \subseteq \mathbb K^N$ of dimension $k + 1$ contains a nonzero
   vector $x$ with $R_A(x) \leq \lambda_k$.

Hence $\lambda_k$ is the maximum over $(k+1)$-dimensional subspaces $W$ of the minimum
of $R_A$ on $W \setminus \{0\}$: part 1 gives $\lambda_k$ as a lower bound for some
subspace, and part 2 bounds the minimum on every subspace by $\lambda_k$.

The proof only uses the spectral decomposition. The same two statements hold for any
matrix $A$ with an orthonormal basis $b_0, \dotsc, b_{N-1}$ of $\mathbb K^N$ and real,
antitone numbers $\mu_0 \geq \dotsb \geq \mu_{N-1}$ such that $A b_j = \mu_j b_j$; the
Hermitian case specializes to the eigenbasis given by the spectral theorem.

## Proof idea

For part 1 we take the span of $b_0, \dotsc, b_k$. Writing a vector in the basis, the
numerator of the Rayleigh quotient is the sum of $\mu_j |\langle b_j, x\rangle|^2$ and the
denominator is the sum of $|\langle b_j, x\rangle|^2$; on the span only $j \leq k$
contributes, so the quotient is at least $\mu_k$. For part 2, the span of
$b_k, \dotsc, b_{N-1}$ has dimension $N - k$, so it meets every subspace of dimension
$k + 1$ in a nonzero vector, and the same expansion shows that $R_A$ is at most $\mu_k$
there.

The principle is the main tool behind the [Cauchy interlacing
theorem](/RealRooted/theorems/cauchy-interlacing/) and Weyl's rank-one interlacing.

## References

See [@Courant1920; @Fischer1905].
<!-- /realrooted-catalog-content -->

This module exposes the Courant–Fischer principle for Hermitian matrices and its
eigenbasis form. The proofs live in `RealRooted.CauchyInterlacing`.
-/
