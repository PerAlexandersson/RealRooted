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
name = "RealRooted.IsInterlacingSeqNonneg.matPolyAction_of_rowThreshold"
module = "RealRooted.RowThreshold"
label = "Brändén: row-threshold matrices of linear forms preserve interlacing sequences"

[[theorems]]
name = "RealRooted.IsInterlacingSeq0Nonneg.matPolyAction_of_rowThreshold"
module = "RealRooted.RowThreshold"
label = "Zero-aware row-threshold preservation of interlacing sequences"
headline = true

[[theorems]]
name = "RealRooted.rowThreshold_interlacingSeq_filter_ne_zero_of_2x2"
module = "RealRooted.RowThreshold"
label = "Row-threshold matrices give a strict interlacing sequence after discarding zeros"

[[theorems]]
name = "RealRooted.isInterlacingSeq0Nonneg_gustafssonSolusAction"
module = "RealRooted.GustafssonSolus"
label = "Gustafsson–Solus Lemma 3.4: row-threshold matrices preserve interlacing"
-->

<!-- realrooted-catalog-content -->
# Threshold matrices

Matrices whose rows have entries $x$ before a threshold and $1$ after it, with weakly increasing
thresholds and a compatibility condition on the markers, preserve interlacing sequences.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
An *interlacing sequence* is a list of nonzero real-rooted polynomials with nonnegative
coefficients in which each polynomial interlaces every later one. In a *weak* interlacing
sequence zero polynomials are allowed.

A *threshold row* with threshold $t$ and marker $\alpha$ has entry $x$ in the columns before $t$,
the marker $\alpha$ in column $t$, and $1$ after it. Applied to $(f_j)$ it gives
$x\sum_{j<t}f_j+\alpha f_t+\sum_{j>t}f_j$.

**Theorem (row-threshold matrices).** Let $G$ be an $m\times n$ matrix whose entries are linear
forms $a+bx$ with $a,b\ge0$. Assume that row $i$ has a threshold $p_i$: the coefficient of $x$ is
positive only in columns before $p_i$, and the constant coefficient is positive only from column
$p_i$ on. Assume $p_1\le\dots\le p_m$, and that for rows $i_1\le i_2$ and columns $j_1\le j_2$,
with $a=G_{i_1j_1}$, $b=G_{i_1j_2}$, $c=G_{i_2j_1}$, $d=G_{i_2j_2}$, the polynomial
$(sx+t)b+d$ interlaces $(sx+t)a+c$ for all $s,t>0$. Then $G$ maps an interlacing sequence of
length $n$ to an interlacing sequence. If this condition holds with zero polynomials allowed,
$G$ maps an interlacing sequence to a weak interlacing sequence of nonnegative polynomials, and
discarding the zero polynomials leaves an interlacing sequence. This specializes the matrix
criterion [@Branden2015, Thm. 7.8.5] of the
[matrix interlacing page](/RealRooted/theorems/matrix-interlacing/).

**Theorem (Haglund–Zhang).** [@HaglundZhang2019] Let $G$ be a threshold matrix whose markers
are $1$ or $1+x$, whose thresholds weakly increase down the rows, and in which, among rows with
equal threshold, a marker $1+x$ is never followed by the marker $1$. Then $G$ maps an interlacing
sequence to a weak interlacing sequence of nonnegative polynomials. Consequently the binomial
Eulerian polynomials, defined by the Haglund–Zhang recursion on refined vectors (marker $1+x$ at
threshold $0$ and $1$ at every later threshold), are real-rooted, which confirms a conjecture of
Ma, Ma and Yeh [@MaMaYeh2017x].

**Theorem (Gustafsson–Solus, Lemma 3.4).** [@GustafssonSolus2020, Lemma 3.4] Let each row have
entries $x$ before its threshold $\varphi_i$, entry $1$ or $0$ in column $\varphi_i$ (a dropped
pivot), and $1$ after it. If the thresholds weakly increase and, among rows with equal
threshold, a dropped pivot is never followed by a row with an undropped pivot, then the matrix
maps an interlacing sequence to a weak interlacing sequence of nonnegative polynomials.

## Use

Gustafsson and Solus use the last theorem to prove that the box polynomials of $s$-lecture hall
simplices, which generalize the derangement polynomials, are real-rooted. The binomial Eulerian
polynomials, with the row $1$ prepended, are the rows of
[OEIS A046802](https://oeis.org/A046802), the $h$-polynomials of the stellohedra. The
[binomial Eulerian real-rootedness assertion](sf:binomialEulerianPolynomial) on
symmetricfunctions.com is an application of the Haglund–Zhang theorem.

## References

[@Branden2015, Thm. 7.8.5]; [@HaglundZhang2019]; [@GustafssonSolus2020]; [@MaMaYeh2017x].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.ThresholdMatrix` and `RealRooted.GustafssonSolus`.
-/
