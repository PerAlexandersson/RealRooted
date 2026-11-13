module

public import RealRooted.MatrixInterlacing

/-!
# Small matrices preserving interlacing sequences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "small-interlacing-matrices"
formalized = "2026-10-06"
tags = []
references = [
  "Fisk2006x",
  "Branden2015",
]
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
name = "RealRooted.Atomic2x2Matrix.nondegeneratePreservingMatrices"
module = "RealRooted.MatrixInterlacing"
label = "The 18 listed matrices"

[[theorems]]
name = "RealRooted.Atomic2x2Matrix.isNondegenerate_and_interlacing_iff_mem"
module = "RealRooted.MatrixInterlacing"
label = "A nondegenerate matrix preserves interlacing exactly when it is one of the 18"
headline = true
symcat = "smallInterlacingMatrices"

[[theorems]]
name = "RealRooted.Atomic2x2Matrix.ncard_isNondegenerate_and_preservesInterlacing"
module = "RealRooted.MatrixInterlacing"
label = "Exactly 18 nondegenerate matrices preserve interlacing"

[[theorems]]
name = "RealRooted.Atomic2x2Matrix.card"
module = "RealRooted.MatrixInterlacing"
label = "There are 81 matrices"

[[theorems]]
name = "RealRooted.Atomic2x2Matrix.ncard_isNondegenerate"
module = "RealRooted.MatrixInterlacing"
label = "56 of them are nondegenerate"

[[theorems]]
name = "RealRooted.Atomic2x2Matrix.ncard_preservesInterlacing"
module = "RealRooted.MatrixInterlacing"
label = "40 of them preserve interlacing"
-->

<!-- realrooted-catalog-content -->
# Small matrices preserving interlacing sequences

Of the $3^4=81$ matrices with entries in $\{0,1,x\}$, exactly 18 nondegenerate ones preserve
interlacing of pairs.

## Results

A matrix $M=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ with entries in $\{0,1,x\}$ acts on pairs by
$$
M\cdot(f_1,f_2)=(af_1+bf_2,\ cf_1+df_2).
$$
We say $M$ **preserves interlacing** if, whenever $f_1,f_2$ have nonnegative coefficients, every
nonzero one of them is real-rooted, and $f_1\ll f_2$ (either polynomial may be zero), the image
pair has the same three properties. We call $M$ **nondegenerate** if neither row is $(0,0)$ and
the two rows are distinct. Exactly 56 of the 81 matrices are nondegenerate.

**Theorem.** Exactly 40 of the 81 matrices preserve interlacing. A nondegenerate matrix
preserves interlacing if and only if it is one of the following 18 matrices, written as lists of
rows:
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

## Proof

By the matrix criterion of Brändén [@Branden2015, Thm. 7.8.5], a nonnegative polynomial matrix
preserves interlacing sequences exactly when each ordered $2\times2$ submatrix, repeated indices
allowed, satisfies an affine interlacing condition. For entries in $\{0,1,x\}$ this leaves a
finite table of admissible matrices. For a matrix outside it, an explicit sparse pair is mapped
to a pair that does not interlace.

## References

[@Fisk2006x, Ch. 3]; [@Branden2015, Thm. 7.8.5]. See the
[table on symmetricfunctions.com](sf:smallInterlacingMatrices).
<!-- /realrooted-catalog-content -->

This module exposes the checked classification of the atomic `2 × 2`
matrices. The affine certificates, the sparse obstruction families and the
decided tables live in `RealRooted.MatrixInterlacing`.
-/
