module

import RealRooted.MatrixInterlacing.TP2Step
import RealRooted.MatrixInterlacing.TotallyNonnegative
import RealRooted.Toeplitz.HessenbergRows
import RealRooted.Toeplitz.TP2Hessenberg
import RealRooted.Toeplitz.TP2HessenbergExamples

/-!
# The finite TP2 Hessenberg certificate

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
-->

<!-- realrooted-catalog-content -->
# The finite TP2 Hessenberg certificate

For a finite TP2 matrix with decreasing columns and constant upper triangles, the rows
$1/(\det(I+zA)-tz)$ are monic, have nonnegative real roots, and consecutive rows interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
A real matrix $A$ is *TP2* if all its entries and all its ordered $2\times2$ minors
$A_{i_1j_1}A_{i_2j_2}-A_{i_1j_2}A_{i_2j_1}$, $i_1<i_2$, $j_1<j_2$, are nonnegative.

**Theorem.** Let $A$ be a real $d\times d$ matrix, $d\ge1$, such that

1. $A$ is TP2,
2. every column of $A$ is weakly decreasing down the rows, and
3. $A_{ij}=A_{jj}$ whenever $i\le j$.

Put $F(z)=\det(I+zA)$ and define $P_k(t)$ by
$$\sum_{k\ge0}P_k(t)\,z^k=\frac{1}{F(z)-t\,z}.$$
Then $P_k$ is monic of degree $k$, has only real nonnegative roots, and $P_k\ll P_{k+1}$. The
matrix may be singular and may be larger than $\deg F$.

**Proposition (vector recursion).** Let $J=\mathbf 1e_1^{\mathsf T}$, $\mathbf f_0=\mathbf 1$ and
$\mathbf f_{k+1}(x)=(A+xJ)\,\mathbf f_k(x)$. Under conditions 1 and 2, each $\mathbf f_k$ is an
interlacing sequence of polynomials with nonnegative coefficients, in the order of the rows.
More generally, for $b\ge0$ and an interlacing sequence $\mathbf f$ with nonnegative
coefficients, if all coordinates of $(A+bxJ)\mathbf f$ are nonzero, then the first coordinate
$f_1$ followed by the coordinates of $(A+bxJ)\mathbf f$ is again such a sequence.

**Proposition (first coordinate).** Under condition 3,
$$P_k(t)=(-1)^k f_{k,1}(-t).$$

**Example.** For $A=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ we have $\det(I+zA)=(1+z)^2$, and the
rows begin $1,\ t-2,\ (t-1)(t-3)$.

## Use

The strict version (simple positive roots and strict interlacing when $d\ge2$ and $\det A>0$)
is on the [strict certificate](/RealRooted/theorems/tp2-hessenberg-strictness/) page. The
weighted-run and parity-lift consequences are on the
[site-weighted run polynomials](/RealRooted/theorems/site-weighted-run-polynomials/) and
[parity lift](/RealRooted/theorems/parity-lift-tp2-kernels/) pages.

## Proof

Brändén's constant-matrix theorem [@Branden2015, Corollary 8.6] says that a TP2 constant matrix
maps an interlacing sequence with nonnegative coefficients to one of the same kind. It gives
the vector recursion, since $(f_1,\dots,f_d,xf_1)$ is interlacing and the new $2\times2$ minors
of $[A\mid b\mathbf 1]$ are $b(A_{ij}-A_{kj})\ge0$. Fisk's theorem for totally nonnegative
matrices (see the [matrix interlacing](/RealRooted/theorems/matrix-interlacing/) page) is a
special case. Condition 3 gives $A=\mathbf 1c^{\mathsf T}-L$ with $L$ strictly lower
triangular, and the matrix determinant lemma identifies $P_k$ with $f_{k,1}$ as displayed.

## References

[@Branden2015]. See also the [totally nonnegative
matrices](/RealRooted/theorems/totally-nonnegative-matrices/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.MatrixInterlacing` and
`RealRooted.Toeplitz` modules named in the metadata.
-/
