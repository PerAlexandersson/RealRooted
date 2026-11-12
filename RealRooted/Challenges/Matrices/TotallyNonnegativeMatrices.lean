module

import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Gaussian
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer.Closure
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Spectrum
public import RealRooted.MatrixInterlacing.TotallyNonnegative
import RealRooted.OscillatoryInterlacing
import RealRooted.TetradiagonalFactorization
import RealRooted.TotallyNonnegInterlacing
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Compound
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignRegularRankDeficient
public import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation
public import RealRooted.Basic.ProperPosition

/-!
# Totally nonnegative matrices challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "totally-nonnegative-matrices"
formalized = "2026-09-05"
tags = []
references = [
  "Fisk2006x",
  "Cryer1976",
  "Karlin1968",
  "FallatJohnson2011",
]
authors = ["Gantmacher", "Krein", "Karlin", "Cryer", "Fisk"]
years = [1937, 1968, 1976, 2006]

[[definitions]]
name = "Matrix.IsTotallyNonnegRect"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg"
label = "Totally nonnegative rectangular matrix"

[[definitions]]
name = "Fin.signVariations"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation"
label = "Sign variations of a vector"

[[definitions]]
name = "Matrix.HasNonnegInitialColumnMinors"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer"
label = "Nonnegative initial-column minors"

[[definitions]]
name = "RealRooted.IsNonnegativeLowerSplit"
module = "RealRooted.TetradiagonalFactorization"
label = "Nonnegative split of a lower matrix into two bidiagonal factors"

[[definitions]]
name = "RealRooted.CanonicalLowerSplitSucceeds"
module = "RealRooted.TetradiagonalFactorization"
label = "Success of the zero-aware canonical split"

[[definitions]]
name = "RealRooted.tetradiagonalMatrix"
module = "RealRooted.TetradiagonalFactorization"
label = "Tetradiagonal lower-Hessenberg matrix"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.exists_charpoly_eq_prod_nonneg"
label = "A totally nonnegative matrix has real nonnegative eigenvalues"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.leading_charpoly_interlaces"
label = "Leading principal submatrices interlace"
headline = true

[[theorems]]
name = "Matrix.IsTotallyNonnegRect.isInterlacingSeq_filter_mulVec"
module = "RealRooted.MatrixInterlacing.TotallyNonnegative"
label = "Totally nonnegative matrices mix interlacing sequences"
symcat = "tnnMixingInterlacing"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.trailing_charpoly_interlaces"
label = "Trailing principal submatrices interlace"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.exists_ofReal_eq_of_mem_spectrum"
label = "The complex spectrum lies on the nonnegative real axis"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.exists_charpoly_eq_prod_pos"
label = "Oscillatory matrices have real positive eigenvalues"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.leading_charpoly_strictInterlaces"
label = "Oscillatory matrices: principal interlacing with simple roots and no common root"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.isTotallyNonnegRect_mul"
label = "Products of totally nonnegative matrices"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.signVariations_mulVec_le"
label = "Variation-diminishing property"
symcat = "variationDiminishingProperty"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.isTotallyNonneg_of_initialColumnMinors"
label = "Cryer's criterion for lower-triangular matrices"

[[theorems]]
name = "Matrix.exists_charpoly_eq_prod_strictAnti_of_forall_compound_primitive"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein"
label = "Gantmacher–Krein: primitive compounds give a simple positive spectrum"

[[theorems]]
name = "Matrix.charpoly_splits_of_forall_compound_primitive"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein"
label = "Primitive compounds make the characteristic polynomial real-rooted with positive roots"

[[theorems]]
name = "RealRooted.canonicalLowerSplitSucceeds_iff"
module = "RealRooted.TetradiagonalFactorization"
label = "The canonical algorithm succeeds exactly when a nonnegative bidiagonal split exists"

[[theorems]]
name = "RealRooted.canonicalSecondFactor_maximal"
module = "RealRooted.TetradiagonalFactorization"
label = "Every nonnegative split is bounded by the canonical pivots"

[[theorems]]
name = "RealRooted.canonicalLowerSplitSucceeds_of_lower_bound"
module = "RealRooted.TetradiagonalFactorization"
label = "A positive lower bound for the pivots forces the canonical split to succeed"

[[theorems]]
name = "RealRooted.positivePivotReconstruction_unique"
module = "RealRooted.TetradiagonalFactorization"
label = "Positive-pivot reconstruction of a tetradiagonal factorization is unique"

[[theorems]]
name = "RealRooted.tetradiagonalPolynomial_eq_charpoly"
module = "RealRooted.TetradiagonalFactorization"
label = "The four-term recurrence gives the characteristic polynomials of tetradiagonal sections"

[[theorems]]
name = "Matrix.det_gaussianMatrix_submatrix_pos"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.Gaussian"
label = "Karlin: Gaussian matrices are strictly totally positive"
-->

<!-- realrooted-catalog-content -->
# Totally nonnegative matrices

Totally nonnegative matrices have real nonnegative eigenvalues, their principal submatrices have
interlacing characteristic polynomials, and they map interlacing sequences to interlacing
sequences.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
A real matrix is **totally nonnegative** (TNN) if every square minor is nonnegative. Products of
TNN matrices are TNN, by the Cauchy–Binet formula.

**Theorem (Gantmacher–Krein).** Let $A$ be a TNN $n\times n$ matrix. Then
$\det(xI-A)=\prod_{i=1}^n(x-\mu_i)$ with all $\mu_i\ge0$; equivalently, every complex eigenvalue
of $A$ is a nonnegative real number. If moreover all compound matrices of some power $A^k$,
$k\ge1$, have positive entries, then all $\mu_i>0$.

**Theorem (primitive compounds).** If every compound matrix of a real square matrix $A$ is
primitive, then $\det(xI-A)=\prod_i(x-\mu_i)$ with $\mu_1>\dots>\mu_n>0$, so the eigenvalues are
real, positive and simple.

**Theorem (principal interlacing).** Let $A$ be a TNN $(N+1)\times(N+1)$ matrix, and let $A'$
and $A''$ be obtained by deleting the last, respectively the first, row and column. Then the
characteristic polynomials of $A'$ and of $A''$ both interlace that of $A$. If moreover
$\det A\ne0$ and the super- and subdiagonal entries of $A$ are positive (the oscillatory case),
then the characteristic polynomials of $A$ and $A'$ have simple roots and no common root, and
all eigenvalues of $A$ are positive.

**Theorem (TNN mixing, Fisk).** [@Fisk2006x, Thm. 3.7] Let $f_1,\dots,f_n$ be real-rooted
polynomials with positive leading coefficients and $f_i\ll f_j$ for $i<j$, and let $A$ be a TNN
$m\times n$ matrix. Then the nonzero entries of $A(f_1,\dots,f_n)^{\mathsf T}$ are real-rooted
with positive leading coefficients and form an interlacing sequence in row order.

**Theorem (variation diminishing).** If $A$ is a TNN $m\times n$ matrix and $c\in\mathbb R^n$,
then $\operatorname{var}(Ac)\le\operatorname{var}(c)$, where $\operatorname{var}$ counts sign
changes after deleting zero entries.

**Theorem (Cryer).** [@Cryer1976] A nonsingular lower-triangular real matrix is TNN as soon as
every minor formed from arbitrary rows and an initial segment of the columns is nonnegative.

**Theorem (Karlin).** [@Karlin1968] For $a>0$ the Gaussian matrix $\bigl(e^{-a(i-j)^2}\bigr)$ is
strictly totally positive: every minor with strictly increasing rows and columns is positive.

**Theorem (tetradiagonal factorization).** Index rows and columns from $0$. Let $T$ be the
lower-Hessenberg matrix with diagonal entries $d_i$, superdiagonal entries $1$, and, in row $i$,
subdiagonal entry $s_i$ and second subdiagonal entry $t_i$. The characteristic polynomial $p_N$
of the leading $N\times N$ section satisfies
$$
p_N=(x-d_{N-1})\,p_{N-1}-s_{N-1}\,p_{N-2}-t_{N-1}\,p_{N-3}\qquad(N\ge3),
$$
with $p_0=1$, $p_1=x-d_0$ and $p_2=(x-d_1)(x-d_0)-s_1$, for all signs of the coefficients.

Write $T$ as a product of a unit lower matrix with subdiagonal $\ell$ and second subdiagonal $m$,
and an upper-bidiagonal matrix with diagonal entries $u_n>0$ and superdiagonal entries $1$.
Then $d_0=u_0$, $d_{n+1}=u_{n+1}+\ell_n$, $s_{n+1}=\ell_nu_n+m_n$ and $t_{n+2}=m_{n+1}u_n$,
and these equations determine $u$, $\ell$ and $m$ uniquely.

Let $(\ell_n)$ and $(m_n)$ be sequences with $m_n\ge0$. A *nonnegative split* consists of
sequences $a_n,b_n\ge0$ with $a_n+b_n=\ell_n$ and $a_{n+1}b_n=m_{n+1}$; it factors the lower
factor into two unit lower-bidiagonal matrices with nonnegative entries. The *canonical pivots*
are $u_0=\ell_0$ and
$$
u_{n+1}=\begin{cases}
\ell_{n+1}&\text{if }u_n=0,\\
\ell_{n+1}-m_{n+1}/u_n&\text{otherwise.}
\end{cases}
$$
The canonical split $b_n=u_n$, $a_{n+1}=m_{n+1}/u_n$ (or $0$ if $u_n=0$) *succeeds* if every
$u_n\ge0$ and $u_n=0$ implies $m_{n+1}=0$. A nonnegative split exists if and only if the
canonical split succeeds, and then $b_n\le u_n$ for every nonnegative split. The canonical split
succeeds if there are positive numbers $v_n$ with $v_0\le\ell_0$ and
$v_{n+1}+m_{n+1}/v_n\le\ell_{n+1}$. The criterion follows Branquinho, Foulquié-Moreno and
Mañas, with the cases of a vanishing pivot made explicit.

## Proof

The eigenvalues of the $q$-th compound matrix are the $q$-fold products of eigenvalues of $A$.
Perron–Frobenius theory for primitive compounds makes each top product real and positive, and a
TNN matrix is a limit of nonsingular TNN matrices (Whitney density). Principal interlacing is
reduced to Cauchy interlacing for a symmetric matrix with the same characteristic polynomial and
principal sections, again followed by approximation. Mixing reduces to the matrix criterion for
interlacing preservers, since the $2\times2$ minors of a TNN matrix satisfy the affine
interlacing condition. Cryer's criterion follows from the Gaussian kernel by a limit.

## References

F. R. Gantmacher and M. G. Krein, *Oscillation Matrices and Kernels and Small Vibrations of
Mechanical Systems*, 1937; revised English edition, AMS Chelsea, 2002. See also [@Karlin1968;
@Cryer1976; @FallatJohnson2011] and [@Fisk2006x, Thm. 3.7]. The entries on symmetricfunctions.com
are [TNN matrices](sf:totallyNonnegativeMatrix),
[variation-diminishing property](sf:variationDiminishingProperty) and
[TNN mixing](sf:tnnMixingInterlacing).
<!-- /realrooted-catalog-content -->

This module exposes the spectral, interlacing, mixing, sign-variation and
Cryer theorems for totally nonnegative matrices.  The matrix theory lives in
`RealRooted.Mathlib.LinearAlgebra.Matrix`; principal interlacing lives in
`RealRooted.TotallyNonnegInterlacing` and `RealRooted.OscillatoryInterlacing`,
and mixing in `RealRooted.MatrixInterlacing.TotallyNonnegative`.
-/

public section

open Matrix Polynomial

namespace RealRooted
namespace Challenges
namespace TotallyNonnegativeMatrices

/-- Total nonnegativity is closed under products (Cauchy–Binet). -/
theorem isTotallyNonnegRect_mul {l n m : ℕ} {L : Matrix (Fin l) (Fin n) ℝ}
    {A : Matrix (Fin n) (Fin m) ℝ} (hL : L.IsTotallyNonnegRect)
    (hA : A.IsTotallyNonnegRect) :
    (L * A).IsTotallyNonnegRect :=
  hL.mul hA

/-- **Gantmacher–Krein**: the characteristic polynomial of a totally
nonnegative real matrix factors into linear factors with nonnegative real
roots. -/
theorem exists_charpoly_eq_prod_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsTotallyNonneg) :
    ∃ μ : Fin n → ℝ, (∀ i, 0 ≤ μ i) ∧ A.charpoly = ∏ i, (X - C (μ i)) :=
  hA.charpoly_factorization_nonneg

/-- Every complex eigenvalue of a totally nonnegative real matrix is a
nonnegative real number. -/
theorem exists_ofReal_eq_of_mem_spectrum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsTotallyNonneg) {z : ℂ} (hz : z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))) :
    ∃ r : ℝ, 0 ≤ r ∧ (r : ℂ) = z :=
  hA.complex_spectrum_nonneg hz

/-- **Gantmacher–Krein**, oscillatory case: if all compounds of a positive
power of a totally nonnegative matrix have positive entries, then its
eigenvalues are real and positive. -/
theorem exists_charpoly_eq_prod_pos {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyNonneg) {k : ℕ} (hk : k ≠ 0)
    (hpos : ∀ q, 1 ≤ q → q ≤ n → ∀ s t, 0 < compound q (A ^ k) s t) :
    ∃ μ : Fin n → ℝ, (∀ i, 0 < μ i) ∧ A.charpoly = ∏ i, (X - C (μ i)) :=
  exists_charpoly_eq_prod_of_pow_compound_pos hA (Nat.pos_of_ne_zero hk) hpos

/-- **Principal interlacing**: deleting the last row and column of a totally
nonnegative matrix gives a characteristic polynomial interlacing the original
one. -/
theorem leading_charpoly_interlaces {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) :
    Interlaces (A.submatrix Fin.castSucc Fin.castSucc).charpoly A.charpoly :=
  hA.leading_charpoly_interlaces

/-- **Principal interlacing**: deleting the first row and column of a totally
nonnegative matrix gives a characteristic polynomial interlacing the original
one. -/
theorem trailing_charpoly_interlaces {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) :
    Interlaces (A.submatrix Fin.succ Fin.succ).charpoly A.charpoly :=
  hA.trailing_charpoly_interlaces

/-- **Strict principal interlacing** for oscillatory matrices: a nonsingular
totally nonnegative matrix with positive super- and subdiagonal has simple
eigenvalues, all positive, which strictly interlace those of its leading
principal submatrix. -/
theorem leading_charpoly_strictInterlaces {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin N, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < A i.succ i.castSucc) :
    Interlaces (A.submatrix Fin.castSucc Fin.castSucc).charpoly A.charpoly ∧
      (∀ x : ℝ, A.charpoly.IsRoot x → A.charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (A.submatrix Fin.castSucc Fin.castSucc).charpoly.IsRoot x →
        (A.submatrix Fin.castSucc Fin.castSucc).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬(A.charpoly.IsRoot x ∧
        (A.submatrix Fin.castSucc Fin.castSucc).charpoly.IsRoot x)) ∧
      ∀ x ∈ A.charpoly.roots, 0 < x :=
  hA.leading_charpoly_strictInterlaces hdet hsuper hsub

/-- **Variation diminishing** (Karlin): multiplication by a totally
nonnegative matrix does not increase the number of sign changes. -/
theorem signVariations_mulVec_le {l n : ℕ} {A : Matrix (Fin l) (Fin n) ℝ}
    (hA : A.IsTotallyNonnegRect) (c : Fin n → ℝ) :
    Fin.signVariations (A *ᵥ c) ≤ Fin.signVariations c :=
  hA.signVariations_mulVec_le c

/-- **Cryer's criterion**: a nonsingular lower-triangular real matrix whose
minors on arbitrary rows and initial columns are nonnegative is totally
nonnegative. -/
theorem isTotallyNonneg_of_initialColumnMinors {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.HasNonnegInitialColumnMinors) (hupper : ∀ i j, i < j → A i j = 0)
    (hdet : A.det ≠ 0) :
    A.IsTotallyNonneg :=
  HasNonnegInitialColumnMinors.isTotallyNonneg_of_upper_zero_of_det_ne_zero A hA hupper
    hdet

end TotallyNonnegativeMatrices
end Challenges
end RealRooted
