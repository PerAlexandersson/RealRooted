import RealRooted.MatrixInterlacing

/-!
# Small matrices preserving interlacing sequences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "small-interlacing-matrices"
authors = ["Fisk", "Brändén"]
years = [2006, 2015]

[[definitions]]
name = "RealRooted.Atomic2x2Matrix"
module = "RealRooted.MatrixInterlacing"
label = "A 2 × 2 matrix with entries in {0, 1, x}"

[[definitions]]
name = "RealRooted.Atomic2x2Matrix.PreservesInterlacing"
module = "RealRooted.MatrixInterlacing"
label = "The matrix preserves interlacing pairs"

[[definitions]]
name = "RealRooted.Atomic2x2Matrix.IsNondegenerate"
module = "RealRooted.MatrixInterlacing"
label = "No zero row and two distinct rows"

[[definitions]]
name = "RealRooted.Atomic2x2Matrix.symCatPreserving"
module = "RealRooted.MatrixInterlacing"
label = "The 18 listed matrices"

[[theorems]]
name = "RealRooted.Challenges.SmallInterlacingMatrices.nondegenerate_preservesInterlacing_iff"
label = "A nondegenerate matrix preserves interlacing exactly when it is one of the 18"
headline = true

[[theorems]]
name = "RealRooted.Challenges.SmallInterlacingMatrices.ncard_nondegenerate_preservesInterlacing"
label = "Exactly 18 nondegenerate matrices preserve interlacing"
headline = true

[[theorems]]
name = "RealRooted.Challenges.SmallInterlacingMatrices.card_atomic2x2Matrix"
label = "There are 81 matrices"

[[theorems]]
name = "RealRooted.Challenges.SmallInterlacingMatrices.ncard_nondegenerate"
label = "56 of them are nondegenerate"

[[theorems]]
name = "RealRooted.Challenges.SmallInterlacingMatrices.ncard_preservesInterlacing"
label = "40 of them preserve interlacing"
-->

<!-- realrooted-catalog-content -->
# Small matrices preserving interlacing sequences

There are $3^4 = 81$ matrices $M = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$
with entries in $\{0, 1, x\}$. Such a matrix acts on a pair of polynomials by
$$
M \cdot (f_1, f_2) = (a f_1 + b f_2,\ c f_1 + d f_2).
$$
We say that $M$ **preserves interlacing** if, whenever $f_1, f_2$ have
nonnegative coefficients, every nonzero one of them is real-rooted, and
$f_1 \ll f_2$, the image pair has the same three properties. Here $\ll$ is weak
interlacing, in which either polynomial may be zero.

We call $M$ **nondegenerate** if neither row is $(0, 0)$ and the two rows are
distinct. Exactly 56 of the 81 matrices are nondegenerate.

**Theorem.** Exactly 40 of the 81 matrices preserve interlacing. A
nondegenerate matrix preserves interlacing if and only if it is one of the
following 18 matrices, written as lists of rows:
$$
\begin{gathered}
[[0, 1], [0, x]],\ [[0, 1], [x, 0]],\ [[1, 0], [0, 1]],\ [[1, 0], [x, 0]],\
[[x, 0], [0, x]],\ [[0, 1], [x, 1]], \\
[[0, 1], [x, x]],\ [[1, 0], [1, 1]],\ [[1, 0], [x, 1]],\ [[1, 1], [0, 1]],\
[[1, 1], [x, 0]],\ [[x, 0], [x, x]], \\
[[x, 1], [0, x]],\ [[x, 1], [x, 0]],\ [[x, x], [0, x]],\ [[1, 1], [x, 1]],\
[[1, 1], [x, x]],\ [[x, 1], [x, x]].
\end{gathered}
$$
In particular, exactly 18 nondegenerate matrices preserve interlacing.

## Proof idea

By the matrix criterion of Brändén (Theorem 7.8.5), a nonnegative polynomial
matrix preserves interlacing sequences exactly when each ordered
$2 \times 2$ submatrix, repeated indices allowed, satisfies an affine
interlacing condition. For entries in $\{0, 1, x\}$ we check these nine
conditions by hand and obtain a finite table. A matrix in the table preserves
interlacing by the forward criterion. For a matrix outside it, an explicit
sparse test pair is mapped to a pair that does not interlace. The counts then follow by deciding the finite table.

## References

S. Fisk, *Polynomials, roots, and interlacing*, arXiv:math/0612833, Chapter 3;
P. Brändén, “Unimodality, log-concavity, real-rootedness and beyond,”
*Handbook of Enumerative Combinatorics*, CRC Press, 2015, Theorem 7.8.5.
See the
[table on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#smallInterlacingMatrices).
<!-- /realrooted-catalog-content -->

This module exposes the checked classification of the atomic `2 × 2`
matrices. The affine certificates, the sparse obstruction families and the
decided tables live in `RealRooted.MatrixInterlacing`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace SmallInterlacingMatrices

open Atomic2x2Matrix

/-- There are `3 ^ 4 = 81` matrices with entries in `{0, 1, x}`. -/
theorem card_atomic2x2Matrix : Fintype.card Atomic2x2Matrix = 81 := by
  rw [← Finset.card_univ]
  exact card_all

/-- Exactly 56 of the 81 matrices have no zero row and two distinct rows. -/
theorem ncard_nondegenerate : {M : Atomic2x2Matrix | M.IsNondegenerate}.ncard = 56 := by
  rw [← card_nondegenerate, ← Set.ncard_coe_finset]
  congr 1
  ext M
  simp [nondegenerate, all, IsNondegenerate]

/-- Exactly 40 of the 81 matrices preserve interlacing. -/
theorem ncard_preservesInterlacing :
    {M : Atomic2x2Matrix | M.PreservesInterlacing}.ncard = 40 := by
  rw [← card_preserving, ← Set.ncard_coe_finset]
  congr 1
  ext M
  simp [preservesInterlacing_iff_mem_preserving]

/-- **The 18 small preservers.** A nondegenerate matrix with entries in
`{0, 1, x}` preserves interlacing if and only if it is one of the 18 matrices
of `symCatPreserving`. -/
theorem nondegenerate_preservesInterlacing_iff (M : Atomic2x2Matrix) :
    M.IsNondegenerate ∧ M.PreservesInterlacing ↔ M ∈ symCatPreserving :=
  (mem_symCatPreserving_iff M).symm

/-- Exactly 18 nondegenerate matrices with entries in `{0, 1, x}` preserve
interlacing. -/
theorem ncard_nondegenerate_preservesInterlacing :
    {M : Atomic2x2Matrix | M.IsNondegenerate ∧ M.PreservesInterlacing}.ncard = 18 := by
  rw [← card_nondegeneratePreserving, nondegeneratePreserving_eq_symCatPreserving,
    ← Set.ncard_coe_finset]
  congr 1
  ext M
  simp [nondegenerate_preservesInterlacing_iff]

end SmallInterlacingMatrices
end Challenges
end RealRooted
