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

If $\det A>0$ and $d\ge2$, the rows of the finite TP2 Hessenberg certificate have simple
positive roots and consecutive rows have no common root.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
Let $A$ be a real $d\times d$ matrix with $d\ge2$ satisfying the hypotheses of the
[finite TP2 Hessenberg certificate](/RealRooted/theorems/tp2-hessenberg-certificate/)
(TP2, weakly decreasing columns, $A_{ij}=A_{jj}=c_j$ for $i\le j$) and $\det A>0$. Let $P_k(t)$
be the coefficients of $1/(\det(I+zA)-tz)$.

**Theorem.** Every $P_k$ has only simple, strictly positive real roots, and $P_k$ and $P_{k+1}$
have no common root. Together with $P_k\ll P_{k+1}$ from the certificate, consecutive rows
interlace strictly.

For $d=1$ and $A=(c)$ one has $\mathbf f_k=(x+c)^k$, which has a root of multiplicity $k$; the
hypothesis $d\ge2$ is needed.

## Proof

Subtracting each row of $A+rJ$ from the one above gives
$\det A=c_d\prod_{i<d}(c_i-A_{i+1,i})$, so every $c_j>0$, and $\det(A+rJ)=\det A$ for all real
$r$. Hence $\mathbf f_k(r)=(A+rJ)^k\mathbf 1\ne0$. At a simple root $r$ of $f_{k,1}$ the values
$f_{k,j}(r)$ all have the sign opposite to $f_{k,1}'(r)$, so $f_{k+1,1}(r)=\sum_jc_jf_{k,j}(r)$
does not vanish. Interlacing pairs without common root have simple roots, which gives
simplicity of every $f_{k,1}$.

## References

[@Branden2015, Corollary 8.6] gives the weak certificate on which this page builds.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.Toeplitz` modules named in
the metadata.
-/
