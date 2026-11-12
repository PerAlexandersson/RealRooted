module

import RealRooted.WangYeh.TriangularMatrix
import RealRooted.WangYeh.TriangularArray
import RealRooted.WangYeh.PF
import RealRooted.WangYeh.Affine
public import RealRooted.MultiplierSequence.Bidiagonal

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
name = "RealRooted.Challenges.WangYeh.eq_zero_or_splits_affine_add"
label = "(bx + a) f + (dx + c) g is real-rooted or zero when ad ≥ bc"
headline = true
symcat = "wangYehAffineCriterion"

[[theorems]]
name = "RealRooted.Challenges.WangYeh.isPFPolynomial_bidiagonalOperator"
label = "Affine bidiagonal transforms preserve Pólya-frequency polynomials"
symcat = "wangYehPfPreserver"

[[theorems]]
name = "RealRooted.Challenges.WangYeh.isPolyaFreqSeq_row_of_bilinear_recurrence"
label = "Rows of a bilinear triangular recurrence are Pólya-frequency sequences"

[[theorems]]
name = "RealRooted.Challenges.WangYeh.isPFPolynomial_rows_of_bilinear_recurrence"
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

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace WangYeh

/-- **Wang–Yeh affine criterion** (Wang–Yeh 2005, Theorem 1).  If `g ≪ f`, both with positive
leading coefficient, and `b * c ≤ a * d`, then `(bX + a) f + (dX + c) g` is zero or splits. -/
theorem eq_zero_or_splits_affine_add {f g : ℝ[X]} {a b c d : ℝ} (hgf : StrictInterl g f)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) (hdet : b * c ≤ a * d) :
    (C b * X + C a) * f + (C d * X + C c) * g = 0 ∨
      ((C b * X + C a) * f + (C d * X + C c) * g).Splits :=
  wangYehAffine_eq_zero_or_splits hgf hf_pos hg_pos hdet

/-- **Wang–Yeh PF preserver** (Wang–Yeh 2005, Corollary 2).  The coefficient-bidiagonal
operator `y_k = (b + d k) x_k + (a + c (k - 1)) x_{k-1}` maps a PF polynomial to a PF
polynomial when `b * c ≤ a * d` and the output has nonnegative coefficients. -/
theorem isPFPolynomial_bidiagonalOperator {p : ℝ[X]} {a b c d : ℝ} (hp : IsPFPolynomial p)
    (hdet : b * c ≤ a * d)
    (hout : HasNonnegCoeffs
      (bidiagonalOperator (fun k ↦ b + d * (k : ℝ)) (fun k ↦ a + c * (k : ℝ)) p)) :
    IsPFPolynomial
      (bidiagonalOperator (fun k ↦ b + d * (k : ℝ)) (fun k ↦ a + c * (k : ℝ)) p) :=
  hp.wangYeh_bidiagonal hdet hout

/-- **Wang–Yeh triangular arrays** (Wang–Yeh 2005, Corollary 3).  A nonnegative
lower-triangular array with `A 0 0 = 1` and the bilinear row recurrence has a PF sequence in
every row, provided `a * s ≤ r * b` and `(a + c) * s ≤ (r + s + t) * b`. -/
theorem isPolyaFreqSeq_row_of_bilinear_recurrence (A : ℕ → ℕ → ℝ) (r s t a b c : ℝ)
    (hlower : ∀ i j, i < j → A i j = 0) (hbase : A 0 0 = 1)
    (hzero : ∀ n, A (n + 1) 0 = (a * (n + 1 : ℝ) + c) * A n 0)
    (hsucc : ∀ n k, A (n + 1) (k + 1) =
      (r * (n + 1 : ℝ) + s * (k + 1 : ℝ) + t) * A n k +
        (a * (n + 1 : ℝ) + b * (k + 1 : ℝ) + c) * A n (k + 1))
    (hnonneg : ∀ n k, 0 ≤ A n k) (hrb : a * s ≤ r * b)
    (hboundary : (a + c) * s ≤ (r + s + t) * b) (n : ℕ) :
    IsPolyaFreqSeq (A n) :=
  wangYeh_triangularMatrix_rows_pf A r s t a b c (fun h ↦ hlower _ _ h) hbase hzero hsucc
    hnonneg hrb hboundary n

/-- **Wang–Yeh triangular arrays, row polynomials.**  If `P 0 = 1`, the coefficients of
consecutive rows satisfy the bilinear recurrence, every row has nonnegative coefficients, and
`a * s ≤ r * b` and `(a + c) * s ≤ (r + s + t) * b`, then every row polynomial is PF. -/
theorem isPFPolynomial_rows_of_bilinear_recurrence (P : ℕ → ℝ[X]) (r s t a b c : ℝ)
    (hbase : P 0 = 1)
    (hzero : ∀ n, (P (n + 1)).coeff 0 = (a * (n + 1 : ℝ) + c) * (P n).coeff 0)
    (hsucc : ∀ n k, (P (n + 1)).coeff (k + 1) =
      (r * (n + 1 : ℝ) + s * (k + 1 : ℝ) + t) * (P n).coeff k +
        (a * (n + 1 : ℝ) + b * (k + 1 : ℝ) + c) * (P n).coeff (k + 1))
    (hnonneg : ∀ n, HasNonnegCoeffs (P n)) (hrb : a * s ≤ r * b)
    (hboundary : (a + c) * s ≤ (r + s + t) * b) (n : ℕ) :
    IsPFPolynomial (P n) :=
  wangYeh_triangularRows_pf P r s t a b c hbase hzero hsucc hnonneg hrb hboundary n

end WangYeh
end Challenges
end RealRooted
