module

import RealRooted.MatrixInterlacing.TotallyNonnegative
import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
import RealRooted.Mathlib.LinearAlgebra.Matrix.Gaussian
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularRankDeficient
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer.Closure
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Spectrum
import RealRooted.OscillatoryInterlacing
import RealRooted.TotallyNonnegInterlacing
import RealRooted.TotallyNonnegPencil
import RealRooted.TotallyNonnegPencil.Checkerboard
import RealRooted.TotallyNonnegPencil.Interlacing

/-!
# Totally nonnegative matrices

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "totally-nonnegative-matrices"
formalized = "2026-09-05"
references = [
  "Karlin1968",
  "Cryer1976",
  "Fisk2006x",
  "FallatJohnson2011",
]
authors = ["Gantmacher", "Krein", "Karlin", "Cryer", "Fisk"]
years = [1937, 1968, 1976, 2006]

[[definitions]]
name = "Matrix.IsTotallyNonnegRect"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg"
label = "Totally nonnegative rectangular matrix"

[[theorems]]
name = "Matrix.IsTotallyNonneg.charpoly_factorization_nonneg"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Spectrum"
label = "A totally nonnegative matrix has real nonnegative eigenvalues"

[[theorems]]
objects = ["Characteristic polynomials of totally nonnegative matrices"]
property = "interlacing"
name = "Matrix.IsTotallyNonneg.leading_charpoly_interlaces"
module = "RealRooted.TotallyNonnegInterlacing"
label = "Leading principal submatrices of a TNN matrix have interlacing characteristic polynomials"
headline = true

[[theorems]]
name = "Matrix.IsTotallyNonneg.leading_charpoly_strictInterlaces"
module = "RealRooted.OscillatoryInterlacing"
label = "Oscillatory matrices: principal interlacing with simple roots and no common root"

[[theorems]]
name = "Matrix.exists_charpoly_eq_prod_strictAnti_of_compounds_primitive"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein"
label = "Gantmacher–Krein: primitive compounds give a simple positive spectrum"

[[theorems]]
name = "Matrix.IsTotallyNonnegRect.mul"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul"
label = "Products of totally nonnegative matrices are totally nonnegative"

[[theorems]]
name = "Matrix.IsTotallyNonnegRect.isInterlacingSeq_filter_mulVec"
module = "RealRooted.MatrixInterlacing.TotallyNonnegative"
label = "Fisk: totally nonnegative matrices map interlacing sequences to interlacing sequences"
symcat = "tnnMixingInterlacing"

[[theorems]]
name = "Matrix.IsTotallyNonnegRect.signVariations_mulVec_le"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularRankDeficient"
label = "Totally nonnegative matrices diminish sign variations"
symcat = "variationDiminishingProperty"

[[theorems]]
name = "Matrix.HasNonnegInitialColumnMinors.isTotallyNonneg_of_upper_zero_of_det_ne_zero"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer.Closure"
label = "Cryer: initial-column minors decide total nonnegativity of a triangular matrix"

[[theorems]]
name = "Matrix.det_gaussianMatrix_submatrix_pos"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.Gaussian"
label = "Karlin: Gaussian matrices are strictly totally positive"

[[theorems]]
name = "Matrix.IsTotallyNonneg.isPFPolynomial_det_one_add_X_smul"
module = "RealRooted.TotallyNonnegPencil"
label = "det(I + xA) is a PF polynomial for a totally nonnegative matrix A"
tags = ["realrooted-original"]

[[theorems]]
name = "Matrix.IsTotallyNonneg.isPFPolynomial_det_map_add_X_smul_checkerboard"
module = "RealRooted.TotallyNonnegPencil.Checkerboard"
label = "det(M + x · checkerboard L) is PF for totally nonnegative M, L with det M > 0"
tags = ["realrooted-original"]

[[theorems]]
name = "Matrix.IsTotallyNonneg.leading_det_X_smul_one_add_map_interlaces"
module = "RealRooted.TotallyNonnegPencil.Interlacing"
label = "The leading section of det(xI + H) interlaces the full pencil for TNN H"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Totally nonnegative matrices

A real matrix is totally nonnegative if all its minors are nonnegative. Such matrices have real
nonnegative eigenvalues, their principal submatrices have interlacing characteristic
polynomials, and they map interlacing sequences of polynomials to interlacing sequences.

## Results

A real matrix is *totally nonnegative* (TNN) if every square minor is nonnegative. By the
Cauchy–Binet formula, products of TNN matrices are TNN.

**Theorem (Gantmacher–Krein).** Let $A$ be a TNN $n\times n$ matrix. Then
$\det(xI-A)=\prod_{i=1}^n(x-\mu_i)$ with all $\mu_i\ge0$. If every compound matrix of a real
square matrix is primitive, its eigenvalues are real, positive and simple.

**Theorem (principal interlacing).** Let $A$ be a TNN $(N+1)\times(N+1)$ matrix, and let $A'$
and $A''$ be obtained by deleting the last, respectively the first, row and column. Then
$\chi_{A'}\ll\chi_A$ and $\chi_{A''}\ll\chi_A$. If moreover $\det A\ne0$ and the super- and
subdiagonal entries of $A$ are positive (the oscillatory case), then $\chi_A$ and $\chi_{A'}$
have simple roots and no common root, and all eigenvalues of $A$ are positive.

**Theorem (Fisk).** [@Fisk2006x, Thm. 3.7] Let $f_1,\dots,f_n$ be real-rooted polynomials with
positive leading coefficients and $f_i\ll f_j$ for $i<j$, and let $A$ be a TNN $m\times n$
matrix. Then the nonzero entries of $A(f_1,\dots,f_n)^{\mathsf T}$ are real-rooted with positive
leading coefficients and form an interlacing sequence in row order.

**Theorem (variation diminishing; Cryer; Karlin).** A TNN $m\times n$ matrix $A$ satisfies
$\operatorname{var}(Ac)\le\operatorname{var}(c)$ for $c\in\mathbb R^n$, where $\operatorname{var}$
counts sign changes after deleting zeros. A nonsingular lower-triangular matrix is TNN as soon as
every minor formed from arbitrary rows and an initial segment of the columns is nonnegative
[@Cryer1976]. For $a>0$, every minor of $\bigl(e^{-a(i-j)^2}\bigr)$ with strictly increasing
rows and columns is positive [@Karlin1968].

**Theorem (determinant pencils).** If $A$ is TNN, then $\det(I+xA)$ is a PF polynomial. More
generally, if $M$ and $L$ are TNN with $\det M>0$, then $\det(M+x\,L^{\pm})$ is a PF polynomial,
where $L^{\pm}=\bigl((-1)^{i+j}L_{ij}\bigr)$. If $H$ is a TNN $(n+1)\times(n+1)$ matrix with
leading $n\times n$ section $H_n$, then $\det(xI_n+H_n)\ll\det(xI_{n+1}+H)$.

## Use

Total nonnegativity is the matrix form of real-rootedness: by the
[Aissen–Schoenberg–Whitney theorem](rr:aissen-schoenberg-whitney) a polynomial with nonnegative
coefficients is real-rooted exactly when its Toeplitz matrix is TNN. Planar networks and the
[Lindström–Gessel–Viennot lemma](rr:lindstrom-gessel-viennot) give TNN matrices, and Fisk's
theorem turns them into interlacing sequences. The
[chain polynomials](rr:branden-leite) of a TNN matrix are another example.

## Proof

The eigenvalues of the $q$-th compound matrix are the $q$-fold products of eigenvalues of $A$.
Perron–Frobenius theory for primitive compounds makes each top product real and positive, and a
TNN matrix is a limit of nonsingular TNN matrices. Principal interlacing reduces to Cauchy
interlacing for a symmetric matrix with the same characteristic polynomial and principal
sections. Fisk's theorem follows from the matrix criterion for interlacing preservers, since the
$2\times2$ minors of a TNN matrix satisfy its interlacing condition. Cryer's criterion follows
from the Gaussian kernel by a limit.

## References

F. R. Gantmacher and M. G. Krein, *Oscillation Matrices and Kernels and Small Vibrations of
Mechanical Systems*, 1937; revised English edition, AMS Chelsea, 2002;
[@Karlin1968; @Cryer1976; @FallatJohnson2011]; [@Fisk2006x, Thm. 3.7]. See also
[totally nonnegative matrices](sf:totallyNonnegativeMatrix), the
[variation-diminishing property](sf:variationDiminishingProperty) and
[TNN mixing](sf:tnnMixingInterlacing) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
