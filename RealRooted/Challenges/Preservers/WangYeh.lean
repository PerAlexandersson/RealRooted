module

public import RealRooted.MultiplierSequence.Bidiagonal
public import RealRooted.WangYeh.Affine
public import RealRooted.WangYeh.PF
public import RealRooted.WangYeh.TriangularArray
public import RealRooted.WangYeh.TriangularMatrix

/-!
# Wang–Yeh criterion for affine combinations of interlacing polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "wang-yeh"
formalized = "2026-10-06"
tags = []
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
label = "(bx + a) f + (dx + c) g is real-rooted or zero when ad ≥ bc"
headline = true
symcat = "wangYehAffineCriterion"

[[theorems]]
name = "RealRooted.IsPFPolynomial.wangYeh_bidiagonal"
module = "RealRooted.WangYeh.PF"
label = "Affine bidiagonal transforms preserve Pólya-frequency polynomials"
symcat = "wangYehPfPreserver"

[[theorems]]
name = "RealRooted.IsPolyaFreqSeq.row_of_bilinear_recurrence"
module = "RealRooted.WangYeh.TriangularMatrix"
label = "Rows of a bilinear triangular recurrence are Pólya-frequency sequences"

[[theorems]]
name = "RealRooted.wangYeh_triangularRows_pf"
module = "RealRooted.WangYeh.TriangularArray"
label = "Row polynomials of a bilinear triangular recurrence are Pólya-frequency"
-->

<!-- realrooted-catalog-content -->
# Wang–Yeh criterion for affine combinations of interlacing polynomials

If $g\ll f$ have positive leading coefficients and $bc\le ad$, then $(bx+a)f+(dx+c)g$ is zero
or real-rooted; this implies a PF-preserver and PF rows for bilinear triangular arrays.

## Results

We write $g\ll f$ for `StrictInterl g f`, as on the
[interlacing page](/RealRooted/concepts/interlacing/); it requires $f$ and $g$ to be nonzero
and real-rooted. A polynomial is *PF* if it has nonnegative coefficients and is zero or
real-rooted with only nonpositive roots. A sequence is PF if its Toeplitz matrix is totally
nonnegative.

**Theorem (Wang–Yeh).** Let $f,g\in\mathbb R[x]$ have positive leading coefficients with
$g\ll f$, and let $a,b,c,d\in\mathbb R$ satisfy $bc\le ad$. Then
$$
(bx+a)\,f(x)+(dx+c)\,g(x)
$$
is zero or real-rooted. The four coefficients have no sign assumptions.

**Theorem (PF preserver).** Let $p=\sum_kx_kx^k$ be PF and let $a,b,c,d\in\mathbb R$ satisfy
$bc\le ad$. Put
$$
y_k=(a+c(k-1))\,x_{k-1}+(b+dk)\,x_k,\qquad x_{-1}=0.
$$
If every $y_k$ is nonnegative, then $\sum_ky_kx^k$ is PF. In Lean this is the
coefficient-bidiagonal operator `bidiagonalOperator (fun k ↦ b + d * k) (fun k ↦ a + c * k)`.

**Theorem (bilinear triangular arrays).** Let $A(n,k)$ be a nonnegative lower-triangular array
with $A(0,0)=1$, $A(n+1,0)=(a(n+1)+c)A(n,0)$ and
$$
A(n+1,k+1)=(r(n+1)+s(k+1)+t)\,A(n,k)+(a(n+1)+b(k+1)+c)\,A(n,k+1)
$$
for all $n,k\ge0$. If
$$
as\le rb\qquad\text{and}\qquad(a+c)s\le(r+s+t)b,
$$
then every row $(A(n,0),A(n,1),\dots)$ is a PF sequence. Equivalently, every row polynomial
$\sum_kA(n,k)x^k$ is PF.

## Proof

Put $H=(bx+a)f+(dx+c)g$ and $K=(bx+a)g-(dx+c)f$. By the Hermite–Biehler theorem, $g\ll f$
makes $f+ig$ stable in the upper half-plane. The complex combination $H+iK$ is $f+ig$ times
the linear factor $(b-id)x+(a-ic)$, whose zero lies in the closed lower half-plane exactly
when $bc\le ad$. Hence $H+iK$ is stable and its real part $H$ is zero or real-rooted. If
$b=d=0$, the claim is the classical fact that every real combination $af+cg$ is real-rooted.

For the PF preserver, a nonconstant PF polynomial $p$ satisfies $p\ll xp'$, and the
bidiagonal image of $p$ is $(cx+d)\,xp'+(ax+b)\,p$, which has Wang–Yeh form with $f=xp'$,
$g=p$ and the condition $bc\le ad$. Each row of the triangular array is the bidiagonal image of
the previous row.

## References

The affine criterion and PF preserver are [@WangYeh2005, Thm. 1 and Cors. 2–3]. See also the
[Wang–Yeh criterion](sf:wangYehAffineCriterion) and the
[Wang–Yeh PF preserver](sf:wangYehPfPreserver) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

The affine criterion lives in `RealRooted.WangYeh.Affine`, the PF preserver in
`RealRooted.WangYeh.PF`, and the triangular-array corollaries in
`RealRooted.WangYeh.TriangularArray` and `RealRooted.WangYeh.TriangularMatrix`.
-/
