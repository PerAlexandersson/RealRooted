module

import RealRooted.Wronskian.CauchyBinet
import RealRooted.Toeplitz.HessenbergWronskian
import RealRooted.Toeplitz.ParityBlock
import RealRooted.Toeplitz.ParityRows
import RealRooted.Toeplitz.ParityStrict
import RealRooted.Toeplitz.ParityVector
import RealRooted.Toeplitz.RunExamples

/-!
# Parity lifting of finite TP2 kernels with strict interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "parity-lift-tp2-kernels"
formalized = "2026-11-09"
references = [
  "Branden2015",
]
authors = ["Brändén"]
years = [2015]
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.parityBlock"
module = "RealRooted.Toeplitz.ParityBlock"
label = "The block matrix [[A, 1 c^T], [0, A]]"

[[definitions]]
name = "RealRooted.parityRow"
module = "RealRooted.Toeplitz.ParityRows"
label = "The rows P_n^gamma, the coefficients of 1 / (G(z^2) + gamma z - t z)"

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
headline = true

[[theorems]]
name = "RealRooted.parityRow_certificate_seed"
module = "RealRooted.Toeplitz.RunExamples"
label = "The certificate applies to the regression seed, whose G is not real-rooted"
-->

<!-- realrooted-catalog-content -->
# Parity lifting of finite TP2 kernels with strict interlacing

Rows defined by $1/(G(z^2)+\gamma z-tz)$ for a finite TP2 kernel $A$ are monic, have simple real
roots, and consecutive rows interlace without common roots.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
Let $A$ be a real $q\times q$ matrix, $q\ge1$, that is TP2 (nonnegative entries and nonnegative
ordered $2\times2$ minors), has weakly decreasing columns, and satisfies $A_{ij}=A_{jj}$ for
$i\le j$. Put $G(w)=\det(I+wA)$.

**Theorem (parity rows).** Assume that $G$ is nonconstant, for instance $\operatorname{tr}A\ne0$.
For $\gamma\in\mathbb R$ define $P_n(t)$ by
$$\sum_{n\ge0}P_n(t)\,z^n=\frac1{G(z^2)+\gamma z-tz}.$$
Then $P_n$ is monic of degree $n$, real-rooted with simple roots, $P_n\ll P_{n+1}$, and $P_n$
and $P_{n+1}$ have no common root. The matrix may be singular, $q$ may exceed $\deg G$, and $G$
need not be real-rooted.

**Example.** The matrix $((2,2,2,2),(1,2,2,2),(1/2,1,2,2),(0,1/2,1,2))$ satisfies the
hypotheses, and $G=1+8w+16w^2+10w^3+2w^4$ is not real-rooted.

## Proof

The rows satisfy $P_n^\gamma(t)=P_n^0(t-\gamma)$, $P_{2m}(t)=V_m(t^2)$ and
$P_{2m+1}(t)=t\,U_m(t^2)$, where $U_m$ and $V_m$ come from the block matrix
$\begin{pmatrix}A&\mathbf 1c^{\mathsf T}\\0&A\end{pmatrix}$, which is TP2 with decreasing columns
and has determinant polynomial $\det(I+zB)=G(z)^2$. Strictness follows from a lower bound for
Wronskians of the first coordinates, obtained from a Cauchy–Binet expansion.

## References

The constant-matrix theorem [@Branden2015, Corollary 8.6] gives the weak interlacing.
Related pages: the [finite TP2 Hessenberg
certificate](/RealRooted/theorems/tp2-hessenberg-certificate/) and its [strict
version](/RealRooted/theorems/tp2-hessenberg-strictness/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Toeplitz` and
`RealRooted.Wronskian` modules named in the metadata.
-/
