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
headline = true

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

Call a real matrix $A$ *TP2* if all its entries and all its ordered $2\times 2$ minors
$A_{i_1 j_1}A_{i_2 j_2}-A_{i_1 j_2}A_{i_2 j_1}$, $i_1<i_2$, $j_1<j_2$, are nonnegative;
minors of larger size are not constrained.

**Theorem.** Let $A$ be a real $d\times d$ matrix, $d\ge 1$, such that

1. $A$ is TP2,
2. every column of $A$ is weakly decreasing down the rows, and
3. $A_{ij}=A_{jj}$ whenever $i\le j$ (so $A_{ij}=c_j$ in the upper triangle).

Put $F(z)=\det(I+zA)$ and define polynomials $P_k(t)$ by
$$\sum_{k\ge 0}P_k(t)\,z^k=\frac{1}{F(z)-t\,z}.$$
Then every $P_k$ is monic of degree $k$ and has only real, nonnegative roots, and consecutive
rows interlace: the roots of $P_{k+1}$ are separated by, and enclose, the roots of $P_k$.
The matrix may be singular, and may be larger than the degree of $F$.

**The vector recursion.** Let $J=\mathbf 1e_1^{\mathsf T}$ and define
$\mathbf f_0=\mathbf 1$, $\mathbf f_{k+1}(x)=(A+xJ)\,\mathbf f_k(x)$. Under conditions 1 and 2
alone, each $\mathbf f_k$ is an interlacing sequence of polynomials with nonnegative
coefficients, in the order of the rows. More generally, for $b\ge 0$ the vector
$(A+bxJ)\mathbf f$ is again such a sequence whenever $\mathbf f$ is, and the first coordinate
$f_1$ of $\mathbf f$ is interlaced by every coordinate of the output. This is the form needed
for weighted renewal problems; it does not use condition 3.

**Identification of the first coordinate.** Condition 3 says that $A=\mathbf 1c^{\mathsf T}-L$
with $L$ strictly lower triangular. Solving the triangular system for the generating series of
$(-1)^k\mathbf f_k(-t)$, and comparing with the matrix determinant lemma for
$\det(I+zA)=1+z\,c^{\mathsf T}(I-zL)^{-1}\mathbf 1$, gives
$$P_k(t)=(-1)^k f_{k,1}(-t).$$
Hence the roots of $P_k$ are the negatives of those of $f_{k,1}$, which are nonpositive because
$f_{k,1}$ has nonnegative coefficients. Each $f_{k,1}$ is interlaced by the first coordinate of
the next vector, which gives the interlacing of consecutive rows.

**Classical input.** The vector recursion rests on Brändén's constant-matrix theorem
[@Branden2015, Corollary 8.6, arXiv:1410.6601]: a constant matrix with nonnegative entries and
nonnegative ordered $2\times 2$ minors maps an interlacing sequence with nonnegative
coefficients to one of the same kind. It is formalized here in this TP2 form
(`Matrix.IsTP2.map_interlacingSeq`), from which the totally nonnegative statement
(Fisk's theorem, see the [matrix interlacing](/RealRooted/theorems/matrix-interlacing/) page)
is a special case. The augmented vector $(f_1,\dots,f_d,xf_1)$ is interlacing by Wagner's
$x$-multiplication transport, and the new $2\times 2$ minors of the augmented constant matrix
$[A\mid b\mathbf 1]$ are $b\,(A_{ij}-A_{kj})\ge 0$ because the columns of $A$ decrease.

**Example.** For $A=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ we have $\det(I+zA)=(1+z)^2$ and the
rows begin $1,\ t-2,\ (t-1)(t-3)$.

## What is new

The proof is new, developed for RealRooted (issue #2482), and is of independent research
interest: the identification of the Hessenberg generating function with the first coordinate
of an interlacing-preserving vector recursion is not taken from the literature, and the
classical constant-matrix theorem is used only as the preservation input. The strict version
(simple positive roots and strict interlacing when $d\ge 2$ and $\det A>0$) is on the
[strict certificate](/RealRooted/theorems/tp2-hessenberg-strictness/) page; the weighted
renewal and parity-lift consequences are on the
[site-weighted run polynomials](/RealRooted/theorems/site-weighted-run-polynomials/) and
[parity lift](/RealRooted/theorems/parity-lift-tp2-kernels/) pages.

## References

See [@Branden2015]. See also the [totally nonnegative
matrices](/RealRooted/theorems/totally-nonnegative-matrices/) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.MatrixInterlacing` and
`RealRooted.Toeplitz` modules named in the metadata.
-/
