module

import RealRooted.MatrixInterlacing.SeparatedCharacteristic
import RealRooted.MatrixInterlacing.SeparatedCharacteristicRows
import RealRooted.MatrixInterlacing.SeparatedCharacteristicRecurrence
import RealRooted.MatrixInterlacing.SeparatedCharacteristicDeterminant

/-!
# Recurrences with separated characteristic parameters

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
name = "RealRooted.PreservesInterlacingSeq0.separatedCharacteristicMatrix"
module = "RealRooted.MatrixInterlacing.SeparatedCharacteristic"
label = "The matrix preserves interlacing sequences when a_i ≥ 0 and b_j ≤ 0"

[[theorems]]
name = "RealRooted.PreservesInterlacingSeq0.separatedCharacteristicMatrix_shift"
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
# Recurrences with separated characteristic parameters

If a constant-coefficient recurrence has characteristic polynomial
$\prod_i(T-a_i)-x\prod_j(T-b_j)$ with $a_i\ge0\ge b_j$, then its solutions from suitable
initial rows are Pólya frequency polynomials and consecutive terms interlace. The criterion can
be read off from the recurrence alone.

## Results

Let $h\ge1$, $m\ge0$, $a\in\mathbb R^{h+m}$, $b\in\mathbb R^m$, and let $S$ be the shift
$(SP)_n=P_{n+1}$. Consider the recurrence
$$
\prod_{i=1}^{h+m}(S-a_i)\,P\;=\;x\prod_{j=1}^{m}(S-b_j)\,P.
$$
Let $M=M(a,b)$ be the $(h+m)\times(h+m)$ matrix over $\mathbb R[x]$ whose first $h-1$ rows are
bidiagonal (diagonal entry $a_i$, entry $1$ above it), and whose remaining rows have $x$ in
column $0$, diagonal entry $a_i$, and entry $a_j-b_{j-h}$ in each column $j>i$, with $b_{j-h}$
read as $0$ for $j<h$. Then
$$
\det(T-M)=\prod_i(T-a_i)-x\prod_j(T-b_j),
$$
so every coordinate of $M^nv$ solves the recurrence. Conversely, if $(P_{s+n})_{n\ge0}$ solves
it and $P_{s+r}=(M^rv)_i$ for $0\le r<h+m$, then $P_{s+n}=(M^nv)_i$ for all $n\ge0$.

**Theorem.** Assume $a_i\ge0\ge b_j$ for all $i,j$, or $a_i\ge\rho\ge b_j$ with $M$ built from
$a_i-\rho$ and $b_j-\rho$. Then $M$ maps interlacing sequences of nonnegative real-rooted
polynomials, zero entries allowed, to such sequences. If the seed $v$ is such a sequence, then
every coordinate of every $M^nv$ is a Pólya frequency polynomial or zero, and
$$
(M^nv)_i\ll(M^{n+1}v)_i\qquad\text{for all }n\ge0\text{ and all }i.
$$

## Proof

The determinant formula and the Cayley–Hamilton theorem give the recurrence. Under the sign
conditions, $M$ has nonnegative polynomial coefficients and satisfies Brändén's criterion on the
[matrix interlacing](rr:matrix-interlacing) page.

## References

The preservation criterion is [@Branden2015, Thm. 7.8.5]; see the
[matrix interlacing](rr:matrix-interlacing) page.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in the
`RealRooted.MatrixInterlacing.SeparatedCharacteristic*` modules.
-/
