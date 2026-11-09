module

import RealRooted.Toeplitz.RowDifferenceDeterminant
import RealRooted.Toeplitz.RunExamples
import RealRooted.Toeplitz.TP2HessenbergStrict

/-!
# Strict TP2 Hessenberg certificate

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "tp2-hessenberg-strictness"
formalized = "2026-11-09"
references = [
  "Branden2015",
]
authors = ["Brändén"]
years = [2015]
tags = ["realrooted-original"]

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
headline = true

[[theorems]]
name = "RealRooted.hessenbergRow_exampleTwo_strict"
module = "RealRooted.Toeplitz.RunExamples"
label = "The rows of [[1, 1], [0, 1]] are strictly interlacing"
-->

<!-- realrooted-catalog-content -->
# Strict TP2 Hessenberg certificate

Let $A$ be a real $d\times d$ matrix with $d\ge 2$ satisfying the hypotheses of the
[finite TP2 Hessenberg certificate](/RealRooted/theorems/tp2-hessenberg-certificate/)
(nonnegative entries and ordered $2\times2$ minors, weakly decreasing columns,
$A_{ij}=A_{jj}=c_j$ for $i\le j$) and, in addition, $\det A>0$. Let $P_k(t)$ be the coefficients of
$1/(\det(I+zA)-tz)$.

**Theorem.** Every row $P_k$ has only simple, strictly positive real roots, and consecutive rows
$P_k,P_{k+1}$ have no common root. Together with the weak interlacing of the certificate this is
strict interlacing.

**Proof.** Subtracting each row of $A+rJ$ from the one above it gives a lower triangular matrix with
diagonal $c_i-A_{i+1,i}$ and $c_d$; hence
$\det A=c_d\prod_{i<d}(c_i-A_{i+1,i})$, every $c_j>0$, and, for $d\ge2$, $\det(A+rJ)=\det A$
for every real $r$ ($r$ only enters the lower-left corner, off the diagonal). So $A+rJ$ is
invertible and $\mathbf f_k(r)=(A+rJ)^k\mathbf 1\ne0$. If $r$ is a simple root of $f_{k,1}$ then by
weak interlacing all $f_{k,j}(r)$ have the sign opposite to $f_{k,1}'(r)$, and
$f_{k+1,1}(r)=\sum_jc_jf_{k,j}(r)$ can vanish only if the whole vector $\mathbf f_k(r)$ vanishes,
a contradiction. A weakly interlacing pair with no common root has simple roots, so simplicity
passes from $f_{k,1}$ to $f_{k+1,1}$. Finally $f_{k,1}(0)>0$ excludes the root $0$.

**Remark.** For $d=1$ and $A=(c)$, $\mathbf f_k=(x+c)^k$ has a root of multiplicity $k$; the
hypothesis $d\ge2$ is needed.

## What is new

The proof is new, developed for RealRooted (issue #2482), and is of independent research
interest; the classical constant-matrix theorem of Brändén [@Branden2015, Corollary 8.6] enters
only through the weak certificate on which this page builds.

## References

See [@Branden2015].
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Toeplitz` modules named in
the metadata.
-/
