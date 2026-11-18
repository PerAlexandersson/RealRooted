module

import RealRooted.MultiplierSequence.Bidiagonal
import RealRooted.WangYeh.Affine
import RealRooted.WangYeh.PF
import RealRooted.WangYeh.TriangularArray
import RealRooted.WangYeh.TriangularMatrix

/-!
# Wang–Yeh criterion

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "wang-yeh"
formalized = "2026-10-06"
references = [
  "WangYeh2005",
]
authors = ["Wang", "Yeh"]
years = [2005]

[[definitions]]
name = "RealRooted.bidiagonalOperator"
module = "RealRooted.MultiplierSequence.Bidiagonal"
label = "Coefficient-bidiagonal operator"

[[theorems]]
name = "RealRooted.wangYehAffine_eq_zero_or_splits"
module = "RealRooted.WangYeh.Affine"
label = "Wang–Yeh: (bx + a)f + (dx + c)g is zero or real-rooted when g ≪ f and bc ≤ ad"
headline = true
symcat = "wangYehAffineCriterion"

[[theorems]]
name = "RealRooted.IsPFPolynomial.wangYeh_bidiagonal"
module = "RealRooted.WangYeh.PF"
label = "Affine bidiagonal transforms with bc ≤ ad preserve PF polynomials"
symcat = "wangYehPfPreserver"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.row_of_bilinear_recurrence"
module = "RealRooted.WangYeh.TriangularMatrix"
label = "Rows of a bilinear triangular recurrence are Pólya frequency sequences"

[[theorems]]
name = "RealRooted.wangYeh_triangularRows_pf"
module = "RealRooted.WangYeh.TriangularArray"
label = "Row polynomials of a bilinear triangular recurrence are PF polynomials"
-->

<!-- realrooted-catalog-content -->
# Wang–Yeh criterion

If $g\ll f$ have positive leading coefficients and $bc\le ad$, then $(bx+a)f+(dx+c)g$ is zero
or real-rooted. Specializations give a bidiagonal preserver of PF polynomials and PF rows for
triangular arrays with bilinear recurrences, such as the Eulerian and Stirling triangles.

## Results

A polynomial is *PF* if it has nonnegative coefficients and is zero or real-rooted with only
nonpositive roots. A sequence is PF if its Toeplitz matrix is totally nonnegative.

**Theorem (Wang–Yeh).** [@WangYeh2005, Thm. 1] Let $f,g\in\mathbb R[x]$ have positive
leading coefficients with $g\ll f$, and let $a,b,c,d\in\mathbb R$ satisfy $bc\le ad$. Then
$$
(bx+a)\,f(x)+(dx+c)\,g(x)
$$
is zero or real-rooted.

**Corollary (PF preserver).** Let $p=\sum_ku_kx^k$ be PF and let $a,b,c,d\in\mathbb R$ satisfy
$bc\le ad$. Put
$$
v_k=(a+c(k-1))\,u_{k-1}+(b+dk)\,u_k,\qquad u_{-1}=0.
$$
If every $v_k$ is nonnegative, then $\sum_kv_kx^k$ is PF.

**Corollary (bilinear triangular arrays).** Let $A(n,k)$ be a nonnegative lower-triangular array
with $A(0,0)=1$, $A(n+1,0)=(a(n+1)+c)A(n,0)$ and
$$
A(n+1,k+1)=(r(n+1)+s(k+1)+t)\,A(n,k)+(a(n+1)+b(k+1)+c)\,A(n,k+1)
$$
for all $n,k\ge0$. If
$$
as\le rb\qquad\text{and}\qquad(a+c)s\le(r+s+t)b,
$$
then every row $(A(n,0),A(n,1),\dotsc)$ is a PF sequence. Equivalently, every row polynomial
$\sum_kA(n,k)x^k$ is PF.

## Use

The criterion is a standard way to prove that the rows of a triangular array with a bilinear
recurrence are real-rooted. Related criteria for $af+bg$ are the
[Liu–Wang and Ma–Wang criteria](rr:ma-wang-liu-wang).

## Proof

By the [Hermite–Biehler theorem](rr:hermite-biehler-hurwitz), $g\ll f$ makes $f+ig$ stable in
the upper half-plane, and multiplying by $(b-id)x+(a-ic)$, whose zero lies in the closed lower
half-plane exactly when $bc\le ad$, keeps it stable; the real part of the product is
$(bx+a)f+(dx+c)g$. For the PF preserver, the image of $p$ is $(ax+b)p+(cx+d)xp'$, and
$p\ll xp'$. Each row of the triangular array is such an image of the previous row.

## References

[@WangYeh2005, Thm. 1 and Cors. 2–3]
<!-- /realrooted-catalog-content -->
-/
