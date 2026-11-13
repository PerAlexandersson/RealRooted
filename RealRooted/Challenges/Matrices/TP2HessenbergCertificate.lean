module

import RealRooted.MatrixInterlacing.TP2Step
import RealRooted.MatrixInterlacing.TotallyNonnegative
import RealRooted.Toeplitz.HessenbergRows
import RealRooted.Toeplitz.HessenbergWronskian
import RealRooted.Toeplitz.ParityBlock
import RealRooted.Toeplitz.ParityRows
import RealRooted.Toeplitz.ParityStrict
import RealRooted.Toeplitz.ParityVector
import RealRooted.Toeplitz.RowDifferenceDeterminant
import RealRooted.Toeplitz.RunExamples
import RealRooted.Toeplitz.SiteWeightedRunRoots
import RealRooted.Toeplitz.SiteWeightedRuns
import RealRooted.Toeplitz.TP2Hessenberg
import RealRooted.Toeplitz.TP2HessenbergExamples
import RealRooted.Toeplitz.TP2HessenbergStrict
import RealRooted.Wronskian.CauchyBinet

/-!
# Hessenberg rows of TP2 matrices

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "tp2-hessenberg-certificate"
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
name = "RealRooted.hessenbergVector"
module = "RealRooted.Toeplitz.HessenbergRows"
label = "The vector recursion f_{k+1} = (A + X J) f_k"

[[definitions]]
name = "RealRooted.hessenbergRow"
module = "RealRooted.Toeplitz.HessenbergRows"
label = "The rows P_k, the coefficients of 1 / (det (I + z A) - t z)"

[[definitions]]
name = "RealRooted.siteWeightedRuns"
module = "RealRooted.Toeplitz.SiteWeightedRuns"
label = "The site-weighted run sum Z_N(z), a sum over subsets of products of run weights"

[[definitions]]
name = "RealRooted.runKernel"
module = "RealRooted.Toeplitz.SiteWeightedRuns"
label = "The run kernel u_k = e_1^T A^k 1"

[[definitions]]
name = "RealRooted.siteWeightedRunPolynomial"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "B_N(t) = Z_N(a_0 t, ..., a_{N-1} t)"

[[definitions]]
name = "RealRooted.parityBlock"
module = "RealRooted.Toeplitz.ParityBlock"
label = "The block matrix [[A, 1 c^T], [0, A]]"

[[definitions]]
name = "RealRooted.parityRow"
module = "RealRooted.Toeplitz.ParityRows"
label = "The rows P_n^gamma, the coefficients of 1 / (G(z^2) + gamma z - t z)"

[[theorems]]
name = "Matrix.IsTP2.map_interlacingSeq"
module = "RealRooted.MatrixInterlacing.TotallyNonnegative"
label = "A TP2 constant matrix preserves interlacing sequences with nonnegative coefficients"

[[theorems]]
name = "Matrix.IsTP2.interlacingSeqNonneg_cons_tp2AffineStep"
module = "RealRooted.MatrixInterlacing.TP2Step"
label = "The affine step (A + b X J) f preserves ordered interlacing"

[[theorems]]
name = "RealRooted.hessenbergDenominator_mul_mk_hessenbergRow"
module = "RealRooted.Toeplitz.HessenbergRows"
label = "The rows are the coefficients of the inverse of det (I + z A) - t z"

[[theorems]]
name = "RealRooted.hessenbergRow_eq"
module = "RealRooted.Toeplitz.HessenbergRows"
label = "P_k(t) = (-1)^k f_{k,1}(-t)"

[[theorems]]
name = "RealRooted.isInterlacingSeqNonneg_hessenbergVector"
module = "RealRooted.Toeplitz.TP2Hessenberg"
label = "Every stage of the vector recursion is an interlacing sequence"

[[theorems]]
name = "RealRooted.hessenbergRow_certificate"
module = "RealRooted.Toeplitz.TP2Hessenberg"
label = "The rows are monic, have nonnegative real roots and interlace"
headline = true

[[theorems]]
name = "RealRooted.hessenbergRow_exampleTwo"
module = "RealRooted.Toeplitz.TP2HessenbergExamples"
label = "The rows of [[1, 1], [0, 1]] begin 1, t - 2, (t - 1)(t - 3)"

[[theorems]]
name = "RealRooted.det_eq_last_mul_prod_of_forall_le"
module = "RealRooted.Toeplitz.RowDifferenceDeterminant"
label = "det B = B_dd prod (B_ii - B_{i+1,i}) for a matrix with constant upper-triangular columns"

[[theorems]]
name = "RealRooted.det_add_smul_runJ_eq"
module = "RealRooted.Toeplitz.TP2HessenbergStrict"
label = "det (A + r J) = det A for d >= 2"

[[theorems]]
name = "RealRooted.eval_hessenbergVector"
module = "RealRooted.Toeplitz.TP2HessenbergStrict"
label = "The vector recursion evaluated at r is (A + r J)^k 1"

[[theorems]]
name = "RealRooted.not_isRoot_hessenbergVector_succ_zero"
module = "RealRooted.Toeplitz.TP2HessenbergStrict"
label = "A simple root of f_{k,1} is not a root of f_{k+1,1}"

[[theorems]]
name = "RealRooted.hasSimpleRoots_hessenbergVector_zero"
module = "RealRooted.Toeplitz.TP2HessenbergStrict"
label = "Every f_{k,1} has simple roots"

[[theorems]]
name = "RealRooted.hessenbergRow_strict"
module = "RealRooted.Toeplitz.TP2HessenbergStrict"
label = "For d >= 2 and det A > 0: simple positive roots, no common roots of consecutive rows"

[[theorems]]
name = "RealRooted.hessenbergRow_exampleTwo_strict"
module = "RealRooted.Toeplitz.RunExamples"
label = "The rows of [[1, 1], [0, 1]] are strictly interlacing"

[[theorems]]
name = "RealRooted.siteWeightedRuns_runKernel"
module = "RealRooted.Toeplitz.SiteWeightedRuns"
label = "Transfer identity: Z_N = e_1^T (J + z A) ... (J + z A) 1"

[[theorems]]
name = "RealRooted.siteWeightedRuns_one_by_one"
module = "RealRooted.Toeplitz.RunExamples"
label = "For the kernel u = 1 the run sum is the product of (1 + z_i)"

[[theorems]]
name = "RealRooted.runVector_eq_reflect_affineVector"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "The transfer vector is the reflection of the affine vector for the matrices a_k A"

[[theorems]]
name = "RealRooted.isRealRootedIn_Iio_siteWeightedRunPolynomial"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "B_N is real-rooted with all roots negative"

[[theorems]]
name = "RealRooted.strictInterl_siteWeightedRunPolynomial"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "Consecutive B_N, B_{N+1} interlace"

[[theorems]]
name = "RealRooted.siteWeightedRunPolynomial_certificate"
module = "RealRooted.Toeplitz.SiteWeightedRunRoots"
label = "B_N(0) = 1, nonnegative coefficients, negative real roots, B_N interlaces B_{N+1}"

[[theorems]]
name = "RealRooted.le_eval_wronskian_sum_sum"
module = "RealRooted.Wronskian.CauchyBinet"
label = "Cauchy-Binet for the Wronskian of two linear combinations"

[[theorems]]
name = "RealRooted.le_eval_wronskian_hessenbergVector_succ"
module = "RealRooted.Toeplitz.HessenbergWronskian"
label = "The Wronskian of the Hessenberg step dominates each 2 x 2 minor term"

[[theorems]]
name = "RealRooted.parityBlock_isTP2"
module = "RealRooted.Toeplitz.ParityBlock"
label = "The block matrix is TP2 with decreasing columns"

[[theorems]]
name = "RealRooted.hessenbergDet_parityBlock"
module = "RealRooted.Toeplitz.ParityBlock"
label = "det (I + X B) = det (I + X A)^2 for the block matrix B"

[[theorems]]
name = "RealRooted.hessenbergSeries_parityBlock_natAdd_zero"
module = "RealRooted.Toeplitz.ParityRows"
label = "The first coordinate of the second block has series G(z) times the first coordinate series"

[[theorems]]
name = "RealRooted.parityRow_zero_two_mul"
module = "RealRooted.Toeplitz.ParityRows"
label = "Even rows: P_{2m}(t) = V_m(t^2)"

[[theorems]]
name = "RealRooted.parityRow_zero_two_mul_add_one"
module = "RealRooted.Toeplitz.ParityRows"
label = "Odd rows: P_{2m+1}(t) = t U_m(t^2)"

[[theorems]]
name = "RealRooted.parityRow_eq_comp"
module = "RealRooted.Toeplitz.ParityRows"
label = "The shift: P_n^gamma(t) = P_n^0(t - gamma)"

[[theorems]]
name = "RealRooted.le_eval_wronskian_parityBlock"
module = "RealRooted.Toeplitz.ParityVector"
label = "The Wronskian of the two first coordinates is bounded below by c_0^{2m} s"

[[theorems]]
name = "RealRooted.not_isRoot_parityVector_zero_succ_index"
module = "RealRooted.Toeplitz.ParityVector"
label = "f_{m,1} and f_{m+1,q+1} have no common root"

[[theorems]]
name = "RealRooted.parityRow_certificate_of_natDegree_ne_zero"
module = "RealRooted.Toeplitz.ParityStrict"
label = "Parity rows are monic, real-rooted with simple roots, strictly interlacing"

[[theorems]]
name = "RealRooted.parityRow_certificate_seed"
module = "RealRooted.Toeplitz.RunExamples"
label = "A 4 × 4 matrix satisfying the hypotheses whose G is not real-rooted"
-->

<!-- realrooted-catalog-content -->
# Hessenberg rows of TP2 matrices

For a TP2 matrix $A$ with weakly decreasing columns and constant upper triangles, the coefficients
$P_k(t)$ of $1/(\det(I+zA)-tz)$ have nonnegative real roots and consecutive ones interlace. The
same holds for run polynomials with weights from $A$ and for the parity-lifted rows of
$1/(\det(I+z^2A)+\gamma z-tz)$, although $\det(I+zA)$ need not be real-rooted.

## Results

A real matrix $A$ is *TP2* if all its entries and all its ordered $2\times2$ minors
$A_{i_1j_1}A_{i_2j_2}-A_{i_1j_2}A_{i_2j_1}$, $i_1<i_2$, $j_1<j_2$, are nonnegative. Let $A$ be a
real $d\times d$ matrix such that

1. $A$ is TP2,
2. every column of $A$ is weakly decreasing down the rows, and
3. $A_{ij}=A_{jj}$ whenever $i\le j$.

Put $F(z)=\det(I+zA)$ and define $P_k(t)$ by
$$
\sum_{k\ge0}P_k(t)\,z^k=\frac{1}{F(z)-tz}.
$$

**Theorem.** Every $P_k$ is monic of degree $k$ with only real nonnegative roots, and
$P_k\ll P_{k+1}$. If moreover $d\ge2$ and $\det A>0$, then every $P_k$ has simple positive roots,
and $P_k$ and $P_{k+1}$ have no common root.

For $d=1$ and $A=(c)$ the rows are $(t-c)^k$, so the condition $d\ge2$ cannot be dropped. For
$A=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ the rows begin $1,\ t-2,\ (t-1)(t-3)$.

**Theorem (run polynomials).** Let $A$ satisfy conditions 1 and 2, let
$u_k=e_1^{\mathsf T}A^k\mathbf 1$ and let $a_1,\dots,a_N\ge0$. Put
$$
B_N(t)=\sum_{S\subseteq[N]}\Bigl(\prod_{R}u_{|R|}\Bigr)\prod_{i\in S}a_it,
$$
where $R$ runs over the maximal intervals of consecutive elements of $S$. Then $B_N(0)=1$, $B_N$
has nonnegative coefficients and only negative real roots, and $B_N\ll B_{N+1}$.

For $u_k=1$ this is $B_N(t)=\prod_i(1+a_it)$.

**Theorem (parity rows).** Let $A$ satisfy conditions 1–3, assume that $F$ is nonconstant, and
for $\gamma\in\mathbb R$ define $P_n^\gamma(t)$ by
$$
\sum_{n\ge0}P_n^\gamma(t)\,z^n=\frac1{F(z^2)+\gamma z-tz}.
$$
Then $P_n^\gamma$ is monic of degree $n$ with simple real roots, $P_n^\gamma\ll P_{n+1}^\gamma$,
and the two have no common root.

The $4\times4$ matrix with rows $(2,2,2,2)$, $(1,2,2,2)$, $(\tfrac12,1,2,2)$, $(0,\tfrac12,1,2)$
satisfies conditions 1–3, and $F(z)=1+8z+16z^2+10z^3+2z^4$ is not real-rooted.

## Use

Fisk's theorem for totally nonnegative matrices on the
[matrix interlacing](rr:matrix-interlacing) page is a special case of Brändén's theorem; see also
[totally nonnegative matrices](rr:totally-nonnegative-matrices).

## Proof

Let $J=\mathbf 1e_1^{\mathsf T}$ and $\mathbf f_k=(A+xJ)^k\mathbf 1$. By Brändén's theorem
[@Branden2015, Corollary 8.6], a TP2 matrix maps interlacing sequences of polynomials with
nonnegative coefficients to interlacing sequences, so every $\mathbf f_k$ is one, and condition 3
with the matrix determinant lemma gives $P_k(t)=(-1)^kf_{k,1}(-t)$; strictness comes from
$\det(A+rJ)=\det A\ne0$ for every real $r$. The run polynomials are
reversals of first coordinates of $(a_NA+xJ)\cdots(a_1A+xJ)\mathbf 1$, and the parity rows come
from the TP2 block matrix $\begin{pmatrix}A&\mathbf 1c^{\mathsf T}\\0&A\end{pmatrix}$, with
$c_j=A_{jj}$ and determinant polynomial $F(z)^2$, together with a Cauchy–Binet bound on
Wronskians for strictness.

## References

- [@Branden2015, Corollary 8.6]
<!-- /realrooted-catalog-content -->
-/
