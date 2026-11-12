module

import RealRooted.GustafssonSolus
import RealRooted.RowThreshold
import RealRooted.ThresholdMatrix.HaglundZhang

/-!
# Threshold matrices challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "threshold-matrices"
formalized = "2026-10-06"
tags = []
references = [
  "Branden2015",
  "HaglundZhang2019",
  "GustafssonSolus2020",
  "MaMaYeh2017x",
]
authors = ["Haglund", "Zhang", "Gustafsson", "Solus"]
years = [2019, 2020]

[[definitions]]
name = "RealRooted.thresholdEntry"
module = "RealRooted.ThresholdMatrix.Basic"
label = "Threshold entry: x before the threshold, a marker at it, 1 after it"

[[definitions]]
name = "RealRooted.HaglundZhang.binomialEulerianPolynomial"
module = "RealRooted.ThresholdMatrix.HaglundZhang"
label = "Binomial Eulerian polynomial, via the Haglund–Zhang recursion"

[[definitions]]
name = "RealRooted.HasRowThresholdLinearStructure"
module = "RealRooted.RowThreshold"
label = "Row-threshold matrix of nonnegative linear forms"

[[theorems]]
name = "RealRooted.HaglundZhang.isInterlacingSeq0Nonneg_matPolyAction"
module = "RealRooted.ThresholdMatrix.HaglundZhang"
label = "Haglund–Zhang threshold matrices preserve interlacing sequences"

[[theorems]]
name = "RealRooted.HaglundZhang.binomialEulerianPolynomial_splits"
module = "RealRooted.ThresholdMatrix.HaglundZhang"
label = "Haglund–Zhang: binomial Eulerian polynomials are real-rooted"

[[theorems]]
name = "RealRooted.HaglundZhang.binomialRefined_interlaces"
module = "RealRooted.ThresholdMatrix.HaglundZhang"
label = "The refined binomial Eulerian vectors form interlacing sequences"

[[theorems]]
name = "RealRooted.rowThreshold_matrix_preserves_interlacing_seq_of_2x2"
module = "RealRooted.RowThreshold"
label = "Brändén: row-threshold matrices of linear forms preserve interlacing sequences"

[[theorems]]
name = "RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_of_2x2"
module = "RealRooted.RowThreshold"
label = "Zero-aware row-threshold preservation of interlacing sequences"
headline = true

[[theorems]]
name = "RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2"
module = "RealRooted.RowThreshold"
label = "Row-threshold matrices give a strict interlacing sequence after discarding zeros"

[[theorems]]
name = "RealRooted.isInterlacingSeq0Nonneg_gustafssonSolusAction"
module = "RealRooted.GustafssonSolus"
label = "Gustafsson–Solus Lemma 3.4: row-threshold matrices preserve interlacing"
-->

<!-- realrooted-catalog-content -->
# Threshold matrices

A *threshold row* with threshold $t$ has entry $x$ in the columns before $t$,
a marker entry at column $t$, and $1$ after it. Applied to a sequence
$(f_j)$ of polynomials, it gives $x \sum_{j<t} f_j + \alpha f_t + \sum_{j>t} f_j$.
A matrix of such rows with weakly increasing thresholds maps interlacing
sequences of polynomials with nonnegative coefficients to interlacing
sequences, provided the rows satisfy a compatibility condition on rows with
equal thresholds. This condition on $2 \times 2$ minors is made explicit in
the two theorems below.

**Theorem** (row-threshold matrices). Let $G$ be an $m \times n$ matrix whose
entries are linear forms $a + bX$ with $a, b \geq 0$, and such that row $i$ has
a threshold $p_i$: the coefficient of $X$ is positive only in columns before
$p_i$, and the constant coefficient is positive only from column $p_i$ on.
Assume that the thresholds $p_1 \leq \dotsb \leq p_m$ weakly increase down the
rows, and that Brändén's $2 \times 2$ affine-minor condition holds: for rows
$i_1 \leq i_2$ and columns $j_1 \leq j_2$, with entries $a = G_{i_1 j_1}$,
$b = G_{i_1 j_2}$, $c = G_{i_2 j_1}$, $d = G_{i_2 j_2}$, the polynomial
$(sX + t) b + d$ interlaces $(sX + t) a + c$ for all $s, t > 0$. Then $G$ maps
an interlacing sequence of real-rooted polynomials with nonnegative
coefficients to an interlacing sequence. If the weaker condition with zero
polynomials allowed holds, the image is an interlacing sequence in which some
polynomials may vanish; discarding the zero polynomials leaves a strict
interlacing sequence. This is the specialization of the general matrix
criterion [@Branden2015, Thm. 7.8.5], see the
[matrix interlacing page](/RealRooted/theorems/matrix-interlacing/), to
matrices of linear forms with a threshold structure.

**Theorem** (Haglund–Zhang). [@HaglundZhang2019] Threshold matrices whose
markers are $1$ or $1+x$, whose thresholds weakly increase down the rows, and
in which, among rows with the same threshold, a marker $1+x$ is never followed
by a marker $1$, map interlacing sequences of polynomials with nonnegative
coefficients to interlacing sequences; zero polynomials may occur in the
output. As a consequence, the binomial Eulerian polynomials are real-rooted,
confirming a conjecture of Ma, Ma and Yeh [@MaMaYeh2017x].

Here the binomial Eulerian polynomials are defined by the Haglund–Zhang
recursion on refined vectors, with marker $1 + x$ at threshold zero and $1$ at
every later threshold. Prepending the row $1$ gives the row polynomials
$\sum_k T(n,k)\,x^k$ of [OEIS A046802](https://oeis.org/A046802), the
$h$-polynomials of the stellohedra; the first four rows are checked in Lean,
but the identification with the closed formula for all $n$ is not formalized.

**Theorem** (Gustafsson–Solus, Lemma 3.4). [@GustafssonSolus2020, Lemma 3.4]
Row-threshold matrices, in which
some rows drop their pivot entry, preserve interlacing sequences when the
thresholds increase weakly and no switch follows a dropped pivot.
Gustafsson and Solus use this to prove that the box polynomials of
$s$-lecture hall simplices, which generalize the derangement polynomials, are
real-rooted.

## Relation to SymCat

We formalize the [binomial Eulerian real-rootedness assertion](sf:binomialEulerianPolynomial)
as an application. The headline is the general row-threshold preservation theorem;
the selected application does not assert consecutive binomial Eulerian interlacing.

## References

See [@Branden2015, Thm. 7.8.5; @HaglundZhang2019; @GustafssonSolus2020;
@MaMaYeh2017x]. See also the
[binomial Eulerian polynomial on symmetricfunctions.com](sf:binomialEulerianPolynomial).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.ThresholdMatrix` and `RealRooted.GustafssonSolus`.
-/
