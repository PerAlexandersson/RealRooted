module

import RealRooted.TotallyNonnegPencil
import RealRooted.TotallyNonnegPencil.Interlacing
import RealRooted.TotallyNonnegPencil.Checkerboard
import RealRooted.TotallyNonnegPencil.CheckerboardInterlacing
import RealRooted.TotallyNonnegPencil.StrictInterlacing

/-!
# Pólya-frequency determinant pencils of totally nonnegative matrices

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
label = "Strict interlacing of principal-section characteristic polynomials of (checkerboard L)⁻¹ M"
-->

<!-- realrooted-catalog-content -->
# Pólya-frequency determinant pencils of totally nonnegative matrices

A real matrix is *totally nonnegative* if all its minors are nonnegative.

**Pencils.** If $A$ is totally nonnegative, then $\det(I+xA)$ is a PF polynomial: it has
nonnegative coefficients and only real, nonpositive roots. More generally, for totally
nonnegative $M$ and $L$ with $\det M>0$, the checkerboard-signed pencil
$\det\bigl(M+x\cdot\mathrm{checkerboard}(L)\bigr)$ is a PF polynomial, where the
checkerboard matrix has entries $(-1)^{i+j}L_{ij}$.

**Interlacing of leading sections.** If $H$ is an $(n+1)\times(n+1)$ totally nonnegative
matrix, then $\det(xI_n+H_n)$ interlaces $\det(xI_{n+1}+H)$, where $H_n$ is the leading
principal $n\times n$ section; no Hessenberg assumption is needed. In the pencil form, let
$A$ be lower triangular with invertible determinant and totally nonnegative inverse, and let
$M$ be totally nonnegative. Then the leading section of $\det(M+xA)$ interlaces the full
$\det(M+xA)$. Taking $A=\mathrm{checkerboard}(L)$ for a lower-triangular totally
nonnegative $L$ with $\det L>0$ gives the same conclusion for checkerboard-signed
pencils.

**Strict principal interlacing.** For lower-triangular totally nonnegative $L$ with
$\det L>0$ and totally nonnegative $M$ with $\det M\ne0$, positive superdiagonal entries of
$M$ and a positivity condition on the subdiagonal, the matrix
$H=(\mathrm{checkerboard}\,L)^{-1}M$ has a characteristic polynomial with only simple
positive roots, its leading principal section has simple roots, the two characteristic
polynomials interlace and share no root.

## What is new

These results were developed in this library; no published source is cited, and we
attribute none. See the [totally nonnegative
matrices](/RealRooted/theorems/totally-nonnegative-matrices/)
page for the background.

## References

No published source is cited for these results in the formalization.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the `RealRooted.TotallyNonnegPencil`
modules named in the metadata.
-/
