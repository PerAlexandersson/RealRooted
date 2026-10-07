import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
import RealRooted.Mathlib.LinearAlgebra.Matrix.Gaussian
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Cryer.Closure
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Spectrum
import RealRooted.MatrixInterlacing.TotallyNonnegative
import RealRooted.OscillatoryInterlacing
import RealRooted.TotallyNonnegInterlacing

/-!
# Totally nonnegative matrices challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "totally-nonnegative-matrices"
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

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.exists_charpoly_eq_prod_nonneg"
label = "A totally nonnegative matrix has real nonnegative eigenvalues"
headline = true

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.leading_charpoly_interlaces"
label = "Leading principal submatrices interlace"
headline = true

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.isInterlacingSeq_filter_mulVec"
label = "Totally nonnegative matrices mix interlacing sequences"
headline = true

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
label = "Strict principal interlacing for oscillatory matrices"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.isTotallyNonnegRect_mul"
label = "Products of totally nonnegative matrices"

[[theorems]]
name = "RealRooted.Challenges.TotallyNonnegativeMatrices.signVariations_mulVec_le"
label = "Variation-diminishing property"

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
name = "Matrix.det_gaussianMatrix_submatrix_pos"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.Gaussian"
label = "Karlin: Gaussian matrices are strictly totally positive"
-->

<!-- realrooted-catalog-content -->
# Totally nonnegative matrices

A real matrix is **totally nonnegative** (TNN) if every square minor is
nonnegative. By the Cauchy–Binet formula, products of TNN matrices are TNN.

**Theorem** (Gantmacher–Krein). Let $A$ be a TNN $n \times n$ matrix. Then
$$
\det(xI - A) = \prod_{i=1}^{n} (x - \mu_i)
$$
with $\mu_1, \dotsc, \mu_n \geq 0$. Equivalently, every complex eigenvalue of
$A$ is a nonnegative real number. If moreover all compound matrices of some
power $A^k$, $k \geq 1$, have positive entries, then all $\mu_i$ are positive.

**Theorem** (principal interlacing). Let $A$ be a TNN
$(N+1) \times (N+1)$ matrix, and let $A'$ and $A''$ be the submatrices
obtained by deleting the last, respectively the first, row and column. Then
the characteristic polynomials of $A'$ and of $A''$ both interlace that of
$A$. If in addition $A$ is nonsingular and its super- and subdiagonal entries
are positive (the oscillatory case), then both characteristic polynomials of
$A$ and $A'$ have simple roots, they have no common root, the interlacing is
strict, and all eigenvalues of $A$ are positive.

**Theorem** (TNN mixing, Fisk). Let $f_1, \dotsc, f_n$ be real-rooted
polynomials with positive leading coefficients that form an interlacing
sequence, so $f_i \ll f_j$ for $i < j$, and let $A$ be a TNN $m \times n$
matrix. Then the nonzero entries of $A (f_1, \dotsc, f_n)^{\mathsf T}$ are
real-rooted with positive leading coefficients and form an interlacing
sequence in row order.

**Theorem** (variation diminishing). If $A$ is a TNN $m \times n$ matrix and
$c \in \mathbb{R}^n$, then $\operatorname{var}(Ac) \leq \operatorname{var}(c)$,
where $\operatorname{var}$ counts sign changes after deleting zero entries.

**Theorem** (Cryer). A nonsingular lower-triangular real matrix is TNN as soon
as every minor formed from arbitrary rows and an initial segment of the
columns is nonnegative.

**Theorem** (Gantmacher–Krein). If every compound matrix of a real square
matrix $A$ is primitive, then the eigenvalues of $A$ are real, positive and
simple. Karlin's Gaussian matrices $\bigl(e^{-a(i-j)^2}\bigr)$ with $a > 0$ are
strictly totally positive: every minor with strictly increasing rows and
columns is positive.

## Proof idea

For the spectrum, the eigenvalues of the $q$-th compound matrix are the
$q$-fold products of eigenvalues of $A$. When all compounds are primitive,
Perron–Frobenius theory makes each top product real and positive, which
forces every eigenvalue to be real and positive. A general TNN matrix is a
limit of nonsingular TNN matrices with this property (Whitney density), and
real nonnegative roots survive the limit.

For principal interlacing, Whitney reduction and a diagonal similarity turn a
nonsingular TNN matrix into a symmetric matrix with the same characteristic
polynomial and the same principal sections, so Cauchy interlacing applies.
The singular case follows by approximation. Strictness in the oscillatory
case comes from simplicity of the spectrum of every principal section.

Mixing reduces to the matrix criterion for interlacing preservers: after a
common translation all inputs have nonnegative coefficients, and the
$2 \times 2$ minors of a TNN matrix satisfy the affine interlacing condition.
The variation-diminishing property holds for sign-regular matrices, and Cryer's
criterion follows by strictifying consecutive minors with a Gaussian kernel
and passing to the limit.

## References

F. R. Gantmacher and M. G. Krein, *Oscillation Matrices and Kernels and Small
Vibrations of Mechanical Systems*, 1937; revised English edition, AMS Chelsea,
2002. S. Karlin, *Total Positivity*, Vol. I, Stanford University Press, 1968.
C. W. Cryer, “Some properties of totally positive matrices,” *Linear Algebra
Appl.* 15 (1976), 1–25. S. M. Fallat and C. R. Johnson, *Totally Nonnegative
Matrices*, Princeton University Press, 2011. S. Fisk, [*Polynomials, roots,
and interlacing*](https://arxiv.org/abs/math/0612833), arXiv:math/0612833
(2006), Theorem 3.7. See the
[TNN matrices](https://www.symmetricfunctions.com/polyaFrequency.htm#totallyNonnegativeMatrix),
[variation-diminishing property](https://www.symmetricfunctions.com/polyaFrequency.htm#variationDiminishingProperty)
and [TNN mixing](https://www.symmetricfunctions.com/realRootedInterlacing.htm#tnnMixingInterlacing)
entries on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module exposes the spectral, interlacing, mixing, sign-variation and
Cryer theorems for totally nonnegative matrices.  The matrix theory lives in
`RealRooted.Mathlib.LinearAlgebra.Matrix`; principal interlacing lives in
`RealRooted.TotallyNonnegInterlacing` and `RealRooted.OscillatoryInterlacing`,
and mixing in `RealRooted.MatrixInterlacing.TotallyNonnegative`.
-/

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

/-- **TNN mixing** (Fisk, Thm. 3.7): a totally nonnegative matrix maps an
interlacing sequence of real-rooted polynomials with positive leading
coefficients to a sequence whose nonzero entries are again real-rooted with
positive leading coefficients and interlacing in row order. -/
theorem isInterlacingSeq_filter_mulVec {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : A.IsTotallyNonnegRect) (f : Fin n → ℝ[X])
    (hf_real : ∀ j, HasPosLeadingCoeff (f j) ∧ (f j).Splits)
    (hf : IsInterlacingSeq (List.ofFn f)) :
    IsInterlacingSeq ((List.ofFn fun i => ∑ j, A i j • f j).filter (· ≠ 0)) ∧
      ∀ i, ∑ j, A i j • f j ≠ 0 →
        HasPosLeadingCoeff (∑ j, A i j • f j) ∧ (∑ j, A i j • f j).Splits := by
  have hrow : tnnMatrixAction A (List.ofFn f) = List.ofFn fun i => ∑ j, A i j • f j := by
    apply List.ext_get
    · simp
    · intro k _ hk
      have hzip : ((List.ofFn fun j => C (A ⟨k, by simpa using hk⟩ j)).zipWith (· * ·)
          (List.ofFn f)) = List.ofFn fun j => A ⟨k, by simpa using hk⟩ j • f j := by
        apply List.ext_get
        · simp
        · intro l _ _
          simp [Polynomial.smul_eq_C_mul]
      simp [tnnMatrixAction, matPolyAction, constantPolynomialMatrix, hzip, List.sum_ofFn]
  obtain ⟨hseq, hreal⟩ := hA.map_interlacingSeq_of_posLeadingCoeff (List.ofFn f) (by simp)
    (by simpa using hf_real) hf
  rw [hrow] at hseq hreal
  exact ⟨hseq, fun i hi ↦ hreal _ (List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i, rfl⟩,
    by simpa using hi⟩)⟩

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
