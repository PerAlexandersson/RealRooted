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

Let $A$ be a real $q\times q$ matrix with nonnegative entries and nonnegative ordered $2\times 2$
minors (TP2), weakly decreasing columns, and $A_{ij}=c_j=A_{jj}$ for $i\le j$. Put
$G(w)=\det(I+wA)$ and assume that $G$ is nonconstant (for instance $\operatorname{tr}A\ne0$). The
matrix may be singular and larger than $\deg G$; $G$ need not be real-rooted.

**Theorem.** For every $\gamma\in\mathbb R$ define polynomials $P_n(t)$ by
$$\sum_{n\ge0}P_n(t)\,z^n=\frac1{G(z^2)+\gamma z-tz}.$$
Then every $P_n$ is monic of degree $n$ with only real roots, all of them simple, and consecutive
rows strictly interlace: the roots of $P_n$ lie strictly between those of $P_{n+1}$ and the two
polynomials have no common root.

**Proof.** The row $P_n^\gamma(t)=P_n^0(t-\gamma)$, so take $\gamma=0$. Since
$(G(z^2)-tz)(G(z^2)+tz)=G(z^2)^2-t^2z^2$,
$$P_{2m}(t)=V_m(t^2),\qquad P_{2m+1}(t)=t\,U_m(t^2),$$
where $\sum_mU_m(u)w^m=1/(G(w)^2-uw)$ and $\sum_mV_m(u)w^m=G(w)/(G(w)^2-uw)$.

Let $B=\begin{pmatrix}A&\mathbf 1c^{\mathsf T}\\0&A\end{pmatrix}$ ($c_j=A_{0j}$). The block
matrix is again TP2 with decreasing columns and the same upper-triangular structure, and
$\det(I+zB)=G(z)^2$. So $U_m$ is, up to the reflection $u\mapsto-u$ and the sign $(-1)^m$, the first
coordinate $f_{m,1}$ of the vector recursion $\mathbf f_{m+1}=(B+xJ)\mathbf f_m$, and the resolvent
identity for the triangular system shows that $V_m$ is the same transform of the first coordinate
$f_{m,q+1}$ of the second block.

Strictness comes from Wronskians. For ordered interlacing polynomials the Wronskian
$\mathcal W(f,g)=fg'-f'g$ is nonnegative on $\mathbb R$ (already in the library as
`wronskian_eval_nonneg_of_strictInterl`), and for a constant matrix $R$
$$\mathcal W\bigl((Rh)_i,(Rh)_j\bigr)
=\sum_{k<\ell}\det R[\{i,j\},\{k,\ell\}]\,\mathcal W(h_k,h_\ell).$$
Applied to $R=[B\mid\mathbf 1]$ and the augmented vector $(f_{m,1},\dots,f_{m,2q},xf_{m,1})$, every
summand is nonnegative, and the term with rows and columns $1,q+1$ has the minor $c_0^2>0$. Since
$\mathcal W(f_{1,1},f_{1,q+1})=\sum_jc_j>0$ we get
$\mathcal W(f_{m,1},f_{m,q+1})\ge c_0^{2(m-1)}\sum_jc_j>0$
pointwise. Hence $f_{m,1}$ and $f_{m,q+1}$ have no common root, both have simple roots, and at a
root $r$ of $f_{m,1}$ the row identity $f_{m+1,q+1}(r)=\sum_jc_jf_{m,q+j}(r)$ has summands of a
common weak sign with the first nonzero, so $f_{m,1}$ and $f_{m+1,q+1}$ have no common root
either. After the reflection, $V_m\ll U_m$ and $U_m\ll V_{m+1}$ strictly, with all roots positive
($U_m(0)V_m(0)>0$). The sign criterion for strict interlacing of consecutive degrees at the roots
of the higher polynomial, applied to $V_m(t^2)$, $tU_m(t^2)$, $V_{m+1}(t^2)$, then gives strict
interlacing of $P_{2m},P_{2m+1},P_{2m+2}$ and simplicity.

If the first diagonal entry $c_0$ vanishes, the first column of $A$ is zero, and deleting it with
the first row changes neither the hypotheses nor $G$; repeating this leaves a matrix with
$c_0>0$ because $G$ is nonconstant.

**Example.** The matrix $((2,2,2,2),(1,2,2,2),(1/2,1,2,2),(0,1/2,1,2))$ has
$G=1+8w+16w^2+10w^3+2w^4$, which is not real-rooted, and the theorem applies.

## What is new

The proof is new, developed for RealRooted, and is of independent research
interest: the block-matrix reduction, the Wronskian expansion for constant matrices, and the
parity extraction are not taken from the literature. The classical constant-matrix theorem of
Brändén [@Branden2015, Corollary 8.6] enters only through the weak certificate and the TP2 affine
step.

## References

See [@Branden2015]. See also the [finite TP2 Hessenberg
certificate](/RealRooted/theorems/tp2-hessenberg-certificate/) and its [strict
version](/RealRooted/theorems/tp2-hessenberg-strictness/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Toeplitz` and
`RealRooted.Wronskian` modules named in the metadata.
-/
