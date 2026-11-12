module

import RealRooted.MatrixInterlacing.SeparatedCharacteristic
import RealRooted.MatrixInterlacing.SeparatedCharacteristicRows
import RealRooted.MatrixInterlacing.SeparatedCharacteristicRecurrence
import RealRooted.MatrixInterlacing.SeparatedCharacteristicDeterminant

/-!
# Separated-characteristic recurrences and interlacing matrices

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "separated-characteristic-recurrence"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.separatedCharacteristicFinMatrix"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristic"
label = "The companion-type polynomial matrix of a separated-characteristic recurrence"

[[definitions]]
name = "RealRooted.separatedCharacteristicRows"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristicRows"
label = "Iterated rows of the matrix from a seed vector"

[[theorems]]
name = "RealRooted.separatedCharacteristicMatrix_preservesInterlacingSeq0"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristic"
label = "The matrix preserves interlacing sequences when a_i ≥ 0 and b_j ≤ 0"

[[theorems]]
name = "RealRooted.separatedCharacteristicMatrix_preservesInterlacingSeq0_shift"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristic"
label = "The shifted form: a_i ≥ ρ and b_j ≤ ρ"

[[theorems]]
name = "RealRooted.separatedCharacteristicRows_isPFPolynomial"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristicRows"
label = "Every coordinate of every iterate of an ordered PF seed is a PF polynomial"

[[theorems]]
name = "RealRooted.separatedCharacteristicRows_interl_succ"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristicRows"
label = "Each coordinate interlaces the same coordinate after one step"
headline = true

[[theorems]]
name = "RealRooted.separatedCharacteristicRows_interlacing"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristicRows"
label = "Iterates of an interlacing seed remain interlacing sequences"

[[theorems]]
name = "RealRooted.separatedCharacteristicFinMatrix_charpoly"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristicDeterminant"
label = "The characteristic polynomial is ∏(T - a_i) - X ∏(T - b_j)"

[[theorems]]
name = "RealRooted.eq_separatedCharacteristicRows_coordinate_from"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristicRecurrence"
label = "A scalar solution with matching initial rows is a coordinate of the matrix orbit"
-->

<!-- realrooted-catalog-content -->
# Separated-characteristic recurrences and interlacing matrices

We consider polynomial sequences $(P_n)$ satisfying a linear recurrence with
polynomial coefficient
$$
\prod_{i=1}^{h+m}(S-a_i)\,P\;=\;x\prod_{j=1}^{m}(S-b_j)\,P,
$$
where $S$ is the shift $(SP)_n=P_{n+1}$, $h\ge1$ and $m\ge0$. The two families of
characteristic parameters $a$ and $b$ are *separated* when all $a_i\ge0$ and all
$b_j\le0$ (or, after a common shift by $\rho$, when $a_i\ge\rho\ge b_j$).

We attach to the recurrence a square polynomial matrix of size $h+m$ whose first
$h-1$ rows are bidiagonal and whose remaining rows have a common entry $x$ in
column zero, the diagonal parameters $a_i$ and constant entries above the
diagonal. Its characteristic polynomial in a variable $T$ is
$$
\prod_i(T-a_i)-x\prod_j(T-b_j),
$$
so by the Cayley–Hamilton theorem every coordinate of its orbit solves the
recurrence, and a scalar sequence solving the recurrence from some starting
index and agreeing with a coordinate on the first $h+m$ rows from that index
coincides with that coordinate from there on. This permits finitely many
exceptional initial rows.

## Interlacing

In the separated case the matrix has nonnegative polynomial coefficients and
preserves interlacing sequences of nonnegative real-rooted polynomials (zero terms allowed),
by the criterion of Brändén on matrices preserving interlacing sequences (see the
[matrix interlacing page](/RealRooted/theorems/matrix-interlacing/)). Consequently, if the seed
is an ordered vector of PF polynomials, so is every iterate, every
coordinate of every iterate is a PF polynomial, and each coordinate interlaces the
same coordinate one step later.

## What is new

The matrix, its iteration and the characteristic-polynomial computation were
developed in this library; no published source is cited for them, and we
attribute none.

## References

No published source is cited for these results in the formalization. For the
criterion on matrices preserving interlacing sequences, see the
[matrix interlacing page](/RealRooted/theorems/matrix-interlacing/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the
`RealRooted.MatrixInterlacing.SeparatedCharacteristic*` modules.
-/
