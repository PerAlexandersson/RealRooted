module

import RealRooted.MatrixInterlacing.TotallyNonnegative
import RealRooted.Toeplitz.HessenbergRows
import RealRooted.Toeplitz.ParityStrict
import RealRooted.Toeplitz.SignedPerturbation
import RealRooted.Toeplitz.SiteWeightedRunRoots
import RealRooted.Toeplitz.TP2Hessenberg
import RealRooted.Toeplitz.TP2HessenbergStrict

/-!
# Interlacing rows of 1/(Q(z) − tz)

<!-- realrooted-catalog
version = 1
kind = "original"
section = "theorems"
slug = "hessenberg-rows"
formalized = "2026-11-09"
references = [
  "Branden2015",
]
authors = ["Brändén"]
years = [2015]
tags = ["realrooted-original"]

[[definitions]]
name = "Matrix.IsTP2"
module = "RealRooted.MatrixInterlacing.TotallyNonnegative"
label = "Nonnegative entries and nonnegative ordered 2 × 2 minors"

[[definitions]]
name = "RealRooted.hessenbergRow"
module = "RealRooted.Toeplitz.HessenbergRows"
label = "The rows P_k, the coefficients of 1 / (det (I + z A) − t z)"

[[theorems]]
name = "RealRooted.hessenbergRow_certificate"
module = "RealRooted.Toeplitz.TP2Hessenberg"
label = "Rows of 1/(det(I+zA)−tz) interlace, roots ≥ 0, for suitable TP2 Hessenberg A"
headline = true

[[theorems]]
name = "RealRooted.hessenbergRow_strict"
module = "RealRooted.Toeplitz.TP2HessenbergStrict"
label = "For d ≥ 2 and det A > 0: simple positive roots, no common roots of consecutive rows"

[[theorems]]
name = "Matrix.IsTP2.map_interlacingSeq"
module = "RealRooted.MatrixInterlacing.TotallyNonnegative"
label = "Brändén: a TP2 matrix preserves interlacing sequences with nonnegative coefficients"
tags = []

[[theorems]]
name = "RealRooted.siteWeightedRunPolynomial_certificate"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "Run polynomials B_N: B_N(0) = 1, negative real roots, B_N ≪ B_{N+1}"

[[theorems]]
name = "RealRooted.parityRow_certificate_of_natDegree_ne_zero"
module = "RealRooted.Toeplitz.ParityStrict"
label = "Rows of 1/(det(I+z²A)+γz−tz): simple real roots, strictly interlacing"

[[theorems]]
name = "RealRooted.ToeplitzPerturbation.strictInterl_row_succ"
module = "RealRooted.Toeplitz.SignedPerturbation"
label = "Rows of 1/(1 − tz + z² + ∑ cⱼ zʲ⁺¹) interlace when A(R) ≤ R² − 1 and B(R) ≤ 1"

[[theorems]]
name = "RealRooted.ToeplitzPerturbation.strictInterl_row_succ_of_sum_le"
module = "RealRooted.Toeplitz.SignedPerturbation"
label = "The bandwidth criterion ∑ j |cⱼ| ≤ (1/s)(1 − 1/s)^((s − 1)/2) suffices"
-->

<!-- realrooted-catalog-content -->
# Interlacing rows of 1/(Q(z) − tz)

For a power series $Q$ with $Q(0)=1$, the coefficients $P_n(t)$ of $1/(Q(z)-tz)$ are the
characteristic polynomials of the sections of a Hessenberg Toeplitz matrix. They are
real-rooted and interlace when $Q=\det(I+zA)$ for suitable TP2 matrices $A$, even if $Q$ is not
real-rooted, and when $Q$ is a small signed perturbation of $1+z^2$.

## Results

Define monic polynomials $P_n$ of degree $n$ by
$$
\sum_{n\ge0}P_n(t)\,z^n=\frac{1}{Q(z)-tz},\qquad Q(z)=1+\sum_{k\ge1}q_kz^k,
$$
so that $P_{n+1}=(t-q_1)P_n-\sum_{k\ge1}q_{k+1}P_{n-k}$. A real matrix is *TP2* if its entries
and its ordered $2\times2$ minors are nonnegative. Let $A$ be a real $d\times d$ matrix with

1. $A$ TP2,
2. every column of $A$ weakly decreasing down the rows, and
3. $A_{ij}=A_{jj}$ whenever $i\le j$.

**Theorem (TP2 rows).** If $Q(z)=\det(I+zA)$, then every $P_n$ has only real nonnegative roots
and $P_n\ll P_{n+1}$. If moreover $d\ge2$ and $\det A>0$, the roots are simple and positive and
$P_n$, $P_{n+1}$ have no common root. For $A=(c)$ the rows are $(t-c)^n$.

**Corollary (run polynomials).** Let $A$ satisfy conditions 1 and 2, let
$u_k=e_1^{\mathsf T}A^k\mathbf 1$ and $a_1,\dots,a_N\ge0$, and put
$$
B_N(t)=\sum_{S\subseteq[N]}\Bigl(\prod_{R}u_{|R|}\Bigr)\prod_{i\in S}a_it,
$$
where $R$ runs over the maximal runs of consecutive elements of $S$. Then $B_N$ has only
negative real roots and $B_N\ll B_{N+1}$. For $u_k=1$, $B_N(t)=\prod_i(1+a_it)$.

**Corollary (parity rows).** If $A$ satisfies conditions 1–3, $\det(I+zA)$ is nonconstant, and
$Q(z)=\det(I+z^2A)+\gamma z$ with $\gamma\in\mathbb R$, then every $P_n$ has simple real roots
and $P_n$, $P_{n+1}$ strictly interlace. The $4\times4$ matrix with rows $(2,2,2,2)$,
$(1,2,2,2)$, $(\tfrac12,1,2,2)$, $(0,\tfrac12,1,2)$ satisfies conditions 1–3, and
$\det(I+zA)=1+8z+16z^2+10z^3+2z^4$ is not real-rooted.

**Theorem (signed perturbations).** Let $Q(z)=1+z^2+\sum_{j=2}^sc_jz^{j+1}$ with real $c_j$ of
either sign, and put $A(R)=\sum_jj|c_j|R^{j+1}$ and $B(R)=\sum_jj(j-1)|c_j|R^{j+1}$. If
$A(R)\le R^2-1$ and $B(R)\le1$ for some $R>0$, then every $P_n$ has simple real roots and
$P_n$, $P_{n+1}$ strictly interlace. This holds in particular if
$\sum_jj|c_j|\le\frac1s\bigl(1-\frac1s\bigr)^{(s-1)/2}$.

## Use

For $c=0$ the signed perturbations are the Chebyshev polynomials of the second kind, the rows of
$1/(1-tz+z^2)$; see [Favard recurrences](rr:favard). That TP2 matrices preserve interlacing
sequences is a case of [Brändén's matrix criterion](rr:matrix-interlacing); see also
[totally nonnegative matrices](rr:totally-nonnegative-matrices). For polynomial $Q$, the
[circle criterion](rr:hessenberg-circle-criterion) gives simple interlacing roots when
$\operatorname{Im}\bigl(Q(z)/z\bigr)\ge0$ on an upper half-circle $|z|=R$.

## Proof

Let $J=\mathbf 1e_1^{\mathsf T}$ and $\mathbf f_k=(A+xJ)^k\mathbf 1$. By Brändén's theorem
[@Branden2015, Corollary 8.6], a TP2 matrix maps interlacing sequences of polynomials with
nonnegative coefficients to interlacing sequences, so every $\mathbf f_k$ is one, and condition 3
with the matrix determinant lemma gives $P_k(t)=(-1)^kf_{k,1}(-t)$. The run polynomials are
reversed first coordinates of $(a_NA+xJ)\cdots(a_1A+xJ)\mathbf 1$, and the parity rows come from
the TP2 block matrix $\begin{pmatrix}A&\mathbf 1c^{\mathsf T}\\0&A\end{pmatrix}$ with
$c_j=A_{jj}$.

## References

[@Branden2015, Corollary 8.6].
<!-- /realrooted-catalog-content -->
-/
