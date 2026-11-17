module

import RealRooted.CauchyInterlacing
import RealRooted.CauchyInterlacing.Polynomial
import RealRooted.CauchyInterlacing.RankOne

/-!
# Cauchy interlacing and Courant–Fischer

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "cauchy-interlacing"
formalized = "2026-07-10"
references = [
  "Fischer1905",
  "Courant1920",
  "Fisk2005x",
  "Godsil2017",
]
authors = ["Cauchy", "Fischer", "Courant", "Weyl", "Fisk"]
years = [1905, 1920, 2005]

[[definitions]]
name = "RealRooted.sortedEigenvalues"
module = "RealRooted.CauchyInterlacing"
label = "Eigenvalues of a Hermitian matrix in decreasing order"

[[definitions]]
name = "RealRooted.rayleigh"
module = "RealRooted.CauchyInterlacing"
label = "Rayleigh quotient"

[[theorems]]
name = "RealRooted.cauchy_interlacing"
module = "RealRooted.CauchyInterlacing"
label = "Cauchy: the eigenvalues of a principal submatrix interlace those of the matrix"
headline = true
symcat = "cauchyInterlacingTheorem"

[[theorems]]
objects = ["Characteristic polynomials of real symmetric matrices"]
property = "interlacing"
name = "RealRooted.principalSubmatrix_charpoly_interlaces"
module = "RealRooted.CauchyInterlacing.Polynomial"
label = "Characteristic polynomials of a principal submatrix interlace"

[[theorems]]
name = "RealRooted.courant_fischer"
module = "RealRooted.CauchyInterlacing"
label = "Courant–Fischer: the kth eigenvalue is a max-min of the Rayleigh quotient"

[[theorems]]
name = "RealRooted.sortedEigenvalues_le_add_vecMulVec"
module = "RealRooted.CauchyInterlacing.RankOne"
label = "Weyl: a rank-one update vv* raises every eigenvalue"

[[theorems]]
name = "RealRooted.sortedEigenvalues_add_vecMulVec_succ_le"
module = "RealRooted.CauchyInterlacing.RankOne"
label = "Weyl: the kth eigenvalue of A + vv* is at most the (k−1)st eigenvalue of A"

[[theorems]]
name = "RealRooted.charpoly_strictInterl_add_vecMulVec"
module = "RealRooted.CauchyInterlacing.RankOne"
label = "Weyl: characteristic polynomials of A and A + vvᵀ interlace"
-->

<!-- realrooted-catalog-content -->
# Cauchy interlacing and Courant–Fischer

The eigenvalues of a Hermitian matrix interlace those of each principal submatrix of one smaller
size, and those of every rank-one update $A+vv^*$. Both follow from the Courant–Fischer
description of eigenvalues as max-min values of the Rayleigh quotient.

## Results

Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $A$ be a Hermitian $N\times N$ matrix over
$\mathbb K$ with eigenvalues $\lambda_0\ge\dots\ge\lambda_{N-1}$, listed with multiplicity. The
*Rayleigh quotient* of $x\ne0$ is $R_A(x)=x^*Ax/x^*x$.

**Theorem (Courant–Fischer).** [@Fischer1905; @Courant1920] For every $0\le k<N$, some
subspace $W\subseteq\mathbb K^N$ of dimension $k+1$ satisfies $R_A(x)\ge\lambda_k$ for every
nonzero $x\in W$, and every subspace of dimension $k+1$ contains a nonzero $x$ with
$R_A(x)\le\lambda_k$.

**Theorem (Cauchy).** [@Fisk2005x] Let $A'$ be obtained from $A$ by deleting the $i$-th row
and column, with eigenvalues $\mu_0\ge\dots\ge\mu_{N-2}$. Then
$$
\lambda_{k+1}\le\mu_k\le\lambda_k\qquad(0\le k<N-1).
$$
If $A$ is real symmetric, then $\chi_{A'}\ll\chi_A$ for the characteristic polynomials.

**Theorem (Weyl, rank-one update).** Let $v\in\mathbb K^N$ and $B=A+vv^*$. Then
$\lambda_k(A)\le\lambda_k(B)$ for all $k$, and $\lambda_k(B)\le\lambda_{k-1}(A)$ for $k\ge1$.
If $A$ is real symmetric and $v$ is real, then $\chi_A\ll\chi_B$.

## Use

The characteristic polynomial of a real symmetric matrix is real-rooted, and these theorems turn
matrix operations into interlacing. Orthogonal polynomials are the characteristic polynomials
of the leading principal submatrices of a Jacobi matrix, so consecutive ones interlace
([orthogonal polynomials](rr:orthogonal-polynomials)).
[Totally nonnegative matrices](rr:totally-nonnegative-matrices) satisfy the same principal
interlacing.

## Proof

Courant–Fischer: take $W$ spanned by eigenvectors for $\lambda_0,\dots,\lambda_k$; the
eigenvectors for $\lambda_k,\dots,\lambda_{N-1}$ span a subspace of dimension $N-k$, which
meets every subspace of dimension $k+1$. Cauchy and Weyl follow by comparing the max-min values
for $A$ with those for $A'$ and $B$, whose Rayleigh quotients agree with or dominate that of $A$.

## References

[@Fischer1905; @Courant1920; @Fisk2005x], and [@Godsil2017] for the graph-theoretic
applications. See also [Cauchy interlacing](sf:cauchyInterlacingTheorem) on
symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
