module

import RealRooted.TotallyNonnegPencil
import RealRooted.TotallyNonnegPencil.Interlacing
import RealRooted.TotallyNonnegPencil.Checkerboard
import RealRooted.TotallyNonnegPencil.CheckerboardInterlacing
import RealRooted.TotallyNonnegPencil.StrictInterlacing

/-!
# Determinant pencils of totally nonnegative matrices

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "totally-nonnegative-pencils"
formalized = "2026-11-07"
authors = []
references = []
tags = ["realrooted-original"]

[[theorems]]
name = "Matrix.IsTotallyNonneg.isPFPolynomial_det_one_add_X_smul"
module = "RealRooted.TotallyNonnegPencil"
label = "det(I + X A) is a PF polynomial for a totally nonnegative matrix A"

[[theorems]]
name = "Matrix.IsTotallyNonneg.isPFPolynomial_det_map_add_X_smul_checkerboard"
module = "RealRooted.TotallyNonnegPencil.Checkerboard"
label = "det(M + X · checkerboard L) is PF for totally nonnegative M, L with det M > 0"
headline = true

[[theorems]]
name = "Matrix.IsTotallyNonneg.leading_det_X_smul_one_add_map_interlaces"
module = "RealRooted.TotallyNonnegPencil.Interlacing"
label = "The leading section interlaces the full determinant pencil det(X I + H)"

[[theorems]]
name = "Matrix.IsLowerTriangular.leading_det_map_add_X_smul_interlaces"
module = "RealRooted.TotallyNonnegPencil.Interlacing"
label = "Leading sections of det(M + X A) interlace for triangular A with TNN inverse"

[[theorems]]
name = "Matrix.IsLowerTriangular.leading_det_map_add_X_smul_checkerboard_interlaces"
module = "RealRooted.TotallyNonnegPencil.CheckerboardInterlacing"
label = "Leading sections of checkerboard-signed determinant pencils interlace"

[[theorems]]
name = "Matrix.IsLowerTriangular.checkerboard_inv_mul_leading_charpoly_strictInterlaces"
module = "RealRooted.TotallyNonnegPencil.StrictInterlacing"
label = "Principal sections of (checkerboard L)⁻¹ M interlace, with simple roots and no common root"
-->

<!-- realrooted-catalog-content -->
# Determinant pencils of totally nonnegative matrices

Determinants $\det(I+xA)$ of totally nonnegative matrices, and their checkerboard-signed
generalizations, are Pólya frequency polynomials, and their leading sections interlace.

## Results

A real matrix is *totally nonnegative* (TNN) if all its minors are nonnegative. For a matrix $L$
the checkerboard matrix has entries $(-1)^{i+j}L_{ij}$.

**Theorem (pencils).** If $A$ is TNN, then $\det(I+xA)$ is a Pólya frequency polynomial. More
generally, if $M$ and $L$ are TNN with $\det M>0$, then
$\det\bigl(M+x\cdot\mathrm{checkerboard}(L)\bigr)$ is a Pólya frequency polynomial.

**Theorem (interlacing of leading sections).** Let $H$ be a TNN $(n+1)\times(n+1)$ matrix and
$H_n$ its leading principal $n\times n$ section. Then $\det(xI_n+H_n)\ll\det(xI_{n+1}+H)$.
More generally, let $A$ be lower triangular with $\det A\ne0$ and TNN inverse, and let $M$ be
TNN. Then the leading $n\times n$ section of $\det(M+xA)$ interlaces $\det(M+xA)$. For
$A=\mathrm{checkerboard}(L)$ with $L$ lower triangular, TNN and $\det L>0$, this gives the same
conclusion for the pencil $\det(M+x\cdot\mathrm{checkerboard}(L))$.

**Theorem (principal interlacing).** Let $L$ be lower triangular and TNN with $\det L>0$, let $M$
be TNN with $\det M\ne0$ and positive superdiagonal entries, and suppose that for each $i$
either $M_{i+1,i}>0$, or $L_{i+1,i}>0$ and $M_{ii}>0$. Put $H=(\mathrm{checkerboard}\,L)^{-1}M$
and let $H'$ be $H$ without its last row and column. Then
$\chi_{H'}\ll\chi_H$, both $\chi_H$ and $\chi_{H'}$ have simple roots, they have no common
root, and all roots of $\chi_H$ are positive.

## Proof

The last theorem uses the oscillatory case of principal interlacing for
[totally nonnegative matrices](rr:totally-nonnegative-matrices).

## References

The background on totally nonnegative and oscillatory matrices is on the
[totally nonnegative matrices](rr:totally-nonnegative-matrices) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.TotallyNonnegPencil`
modules named in the metadata.
-/
