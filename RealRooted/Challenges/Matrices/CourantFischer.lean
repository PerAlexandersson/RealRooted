module

import RealRooted.CauchyInterlacing

/-!
# Courant–Fischer min-max theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "courant-fischer"
formalized = "2026-07-01"
tags = []
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

The $k$-th largest eigenvalue of a Hermitian matrix is the maximum over $(k+1)$-dimensional
subspaces of the minimum of the Rayleigh quotient.

## Results

Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $A$ be a Hermitian $N\times N$ matrix over
$\mathbb K$ with eigenvalues $\lambda_0\ge\dots\ge\lambda_{N-1}$, listed with multiplicity. The
*Rayleigh quotient* of $x\in\mathbb K^N$ is
$$
R_A(x)=\frac{\operatorname{Re}(x^*Ax)}{\operatorname{Re}(x^*x)} .
$$

**Theorem (Courant–Fischer).** [@Courant1920; @Fischer1905] For every $0\le k<N$:

1. some subspace $W\subseteq\mathbb K^N$ of dimension $k+1$ satisfies $R_A(x)\ge\lambda_k$ for
   every nonzero $x\in W$;
2. every subspace $W\subseteq\mathbb K^N$ of dimension $k+1$ contains a nonzero $x$ with
   $R_A(x)\le\lambda_k$.

The same two statements hold for any matrix $A$ with an orthonormal basis $b_0,\dots,b_{N-1}$ of
$\mathbb K^N$ and real numbers $\mu_0\ge\dots\ge\mu_{N-1}$ such that $Ab_j=\mu_jb_j$, with
$\mu_k$ in place of $\lambda_k$.

## Use

The theorem is the tool behind the
[Cauchy interlacing theorem](rr:cauchy-interlacing) and Weyl's rank-one
interlacing.

## Proof

For part 1 take $W=\operatorname{span}(b_0,\dots,b_k)$. For part 2 the span of
$b_k,\dots,b_{N-1}$ has dimension $N-k$, so it meets every subspace of dimension $k+1$ in a
nonzero vector.

## References

See [@Courant1920; @Fischer1905].
<!-- /realrooted-catalog-content -->

This module exposes the Courant–Fischer principle for Hermitian matrices and its
eigenbasis form. The proofs live in `RealRooted.CauchyInterlacing`.
-/
