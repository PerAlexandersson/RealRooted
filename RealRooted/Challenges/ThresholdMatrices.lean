import RealRooted.GustafssonSolus
import RealRooted.ThresholdMatrix.HaglundZhang

/-!
# Threshold matrices challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "threshold-matrices"
formalized = "2026-10-06"
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

[[theorems]]
name = "RealRooted.HaglundZhang.isInterlacingSeq0Nonneg_matPolyAction"
module = "RealRooted.ThresholdMatrix.HaglundZhang"
label = "Haglund–Zhang threshold matrices preserve interlacing sequences"

[[theorems]]
name = "RealRooted.HaglundZhang.binomialEulerianPolynomial_splits"
module = "RealRooted.ThresholdMatrix.HaglundZhang"
label = "Haglund–Zhang: binomial Eulerian polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.HaglundZhang.binomialRefined_interlaces"
module = "RealRooted.ThresholdMatrix.HaglundZhang"
label = "The refined binomial Eulerian vectors form interlacing sequences"

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
sequences, as long as finitely many $2 \times 2$ compatibility checks hold.

**Theorem** (Haglund–Zhang). Threshold matrices whose markers are $1$ or
$1 + x$ preserve interlacing sequences. As a consequence, the binomial
Eulerian polynomials are real-rooted, confirming a conjecture of Ma, Ma and
Yeh.

Here the binomial Eulerian polynomials are defined by the Haglund–Zhang
recursion on refined vectors, with marker $1 + x$ at threshold zero and $1$ at
every later threshold. Prepending the row $1$ gives the row polynomials
$\sum_k T(n,k)\,x^k$ of [OEIS A046802](https://oeis.org/A046802), the
$h$-polynomials of the stellohedra; the first four rows are checked in Lean,
but the identification with the closed formula for all $n$ is not formalized.

**Theorem** (Gustafsson–Solus, Lemma 3.4). Row-threshold matrices, in which
some rows drop their pivot entry, preserve interlacing sequences when the
thresholds increase weakly and no switch follows a dropped pivot.
Gustafsson and Solus use this to prove that the box polynomials of
$s$-lecture hall simplices, which generalize the derangement polynomials, are
real-rooted.

## References

J. Haglund and P. B. Zhang, [“Real-rootedness of variations of Eulerian
polynomials,”](https://doi.org/10.1016/j.aam.2019.05.001) *Advances in Applied
Mathematics* 109 (2019), 38–54,
[arXiv:1902.01278](https://arxiv.org/abs/1902.01278). N. Gustafsson and
L. Solus, [“Derangements, Ehrhart theory, and local
$h$-polynomials,”](https://doi.org/10.1016/j.aim.2020.107169) *Advances in
Mathematics* 369 (2020), 107169. J. Ma, S.-M. Ma and Y.-N. Yeh, “Recurrence
relations for binomial-Eulerian polynomials,”
[arXiv:1711.09016](https://arxiv.org/abs/1711.09016) (2017). See also the
[binomial Eulerian polynomial on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedWords.htm#binomialEulerianPolynomial).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.ThresholdMatrix` and `RealRooted.GustafssonSolus`.
-/
