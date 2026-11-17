module

public import RealRooted.GustafssonSolus
public import RealRooted.MatrixInterlacing
public import RealRooted.MatrixInterlacing.Composition
public import RealRooted.MatrixInterlacing.Converse
public import RealRooted.MatrixInterlacing.Preservation
public import RealRooted.ProductFamily
public import RealRooted.RowThreshold
public import RealRooted.ThresholdMatrix.HaglundZhang

/-!
# Matrices preserving interlacing sequences

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "matrix-interlacing"
formalized = "2026-10-06"
references = [
  "Fisk2006x",
  "Branden2015",
  "HaglundZhang2019",
  "GustafssonSolus2020",
  "MaMaYeh2017x",
]
authors = ["Fisk", "Brändén", "Haglund", "Zhang", "Gustafsson", "Solus"]
years = [2006, 2015, 2019, 2020]

[[definitions]]
name = "RealRooted.PreservesInterlacingSeq0"
module = "RealRooted.MatrixInterlacing.Converse"
label = "The matrix preserves zero-aware interlacing sequences"

[[theorems]]
name = "RealRooted.PreservesInterlacingSeq0.iff_nonneg_and_2x2"
module = "RealRooted.MatrixInterlacing.Converse"
label = "A matrix preserves interlacing sequences exactly when its 2 × 2 submatrices do"
headline = true
symcat = "matrixPreservesInterlacingSequences"

[[theorems]]
name = "RealRooted.IsInterlacingSeqNonneg.matPolyAction_of_2x2"
module = "RealRooted.MatrixInterlacing.Preservation"
label = "Strict form: the strict condition preserves strict interlacing sequences"

[[theorems]]
name = "RealRooted.PreservesInterlacingSeq0.matPolyMul"
module = "RealRooted.MatrixInterlacing.Composition"
label = "Products of interlacing-preserving matrices preserve interlacing"

[[theorems]]
name = "RealRooted.isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeqNonneg"
module = "RealRooted.ProductFamily"
label = "The reversed product-sum of two interlacing nonnegative sequences is real-rooted"

[[theorems]]
name = "RealRooted.Atomic2x2Matrix.isNondegenerate_and_interlacing_iff_mem"
module = "RealRooted.MatrixInterlacing"
label = "Exactly 18 nondegenerate 2 × 2 matrices over {0, 1, x} preserve interlacing"
symcat = "smallInterlacingMatrices"

[[theorems]]
name = "RealRooted.Atomic2x2Matrix.ncard_preservesInterlacing"
module = "RealRooted.MatrixInterlacing"
label = "40 of the 81 matrices over {0, 1, x} preserve interlacing"

[[theorems]]
name = "RealRooted.IsInterlacingSeq0Nonneg.matPolyAction_of_rowThreshold"
module = "RealRooted.RowThreshold"
label = "Brändén: row-threshold matrices of linear forms preserve interlacing sequences"

[[theorems]]
name = "RealRooted.HaglundZhang.isInterlacingSeq0Nonneg_matPolyAction"
module = "RealRooted.ThresholdMatrix.HaglundZhang"
label = "Haglund–Zhang threshold matrices preserve interlacing sequences"

[[theorems]]
objects = ["Binomial Eulerian polynomials"]
name = "RealRooted.HaglundZhang.binomialEulerianPolynomial_splits"
module = "RealRooted.ThresholdMatrix.HaglundZhang"
label = "Haglund–Zhang: binomial Eulerian polynomials are real-rooted"

[[theorems]]
name = "RealRooted.isInterlacingSeq0Nonneg_gustafssonSolusAction"
module = "RealRooted.GustafssonSolus"
label = "Gustafsson–Solus Lemma 3.4: threshold matrices with dropped pivots preserve interlacing"
-->

<!-- realrooted-catalog-content -->
# Matrices preserving interlacing sequences

A matrix of polynomials with nonnegative coefficients maps interlacing sequences to interlacing
sequences if and only if every ordered $2\times2$ submatrix satisfies an affine interlacing
condition. Threshold matrices, which have entries $x$ before a threshold and $1$ after it, are
the main examples; they prove that the binomial Eulerian polynomials are real-rooted.

## Results

Let $G=(G_{ij})$ be an $m\times n$ matrix of real polynomials, acting on sequences by
$(GF)_i=\sum_jG_{ij}f_j$. Here $f\ll g$ holds if $f$ or $g$ is zero, as in the zero-aware
convention of [Conventions](rr:about). Let $\mathcal F_n^{0}$ be the set of sequences
$(f_1,\dots,f_n)$ of polynomials with nonnegative coefficients such that every nonzero $f_i$ is
real-rooted and $f_i\ll f_j$ whenever $i<j$.

**Theorem (Brändén).** [@Branden2015, Thm. 7.8.5] The matrix $G$ maps $\mathcal F_n^{0}$ into
$\mathcal F_m^{0}$ if and only if

1. every entry $G_{ij}$ has nonnegative coefficients, and
2. for all rows $i_1\le i_2$ and columns $j_1\le j_2$, the submatrix
   $\begin{pmatrix}a&b\\c&d\end{pmatrix}=
   \begin{pmatrix}G_{i_1j_1}&G_{i_1j_2}\\G_{i_2j_1}&G_{i_2j_2}\end{pmatrix}$ satisfies
   $$
   (sx+t)\,b+d\ \ll\ (sx+t)\,a+c\qquad\text{for all }s,t>0.
   $$

If condition 2 holds with both sides of $\ll$ nonzero, $G$ maps sequences of nonzero
polynomials to such sequences. Products of matrices with this property have it too.

**Theorem (product-sum).** [@Branden2015, §7.8] If $(f_1,\dots,f_n)$ and $(g_1,\dots,g_n)$ are
interlacing sequences of nonzero real-rooted polynomials with nonnegative coefficients, then
$\sum_if_i\,g_{n+1-i}$ is real-rooted.

**Corollary (small matrices).** Of the 81 matrices
$\begin{pmatrix}a&b\\c&d\end{pmatrix}$ with entries in $\{0,1,x\}$, exactly 40 preserve
interlacing pairs. Exactly 18 of them have no zero row and two distinct rows; these are listed
on [symmetricfunctions.com](sf:smallInterlacingMatrices).

**Corollary (threshold matrices).** Let the entries of $G$ be linear forms $a+bx$ with
$a,b\ge0$, and let row $i$ have a threshold $p_i$: the coefficient of $x$ is positive only
before column $p_i$, and the constant term only from column $p_i$ on. If
$p_1\le\dots\le p_m$ and condition 2 holds, then $G$ maps $\mathcal F_n^0$ into
$\mathcal F_m^0$.

**Theorem (Haglund–Zhang).** [@HaglundZhang2019] A threshold matrix with entries $x$ before the
threshold, marker $1$ or $1+x$ at it and $1$ after it preserves interlacing sequences if the
thresholds weakly increase and, among rows with equal threshold, a marker $1+x$ is never
followed by a marker $1$. Consequently the binomial Eulerian polynomials are real-rooted, as
conjectured by Ma, Ma and Yeh [@MaMaYeh2017x].

**Theorem (Gustafsson–Solus).** [@GustafssonSolus2020, Lemma 3.4] The same holds for markers
$1$ and $0$, if among rows with equal threshold a marker $0$ is never followed by a marker $1$.

## Use

Many interlacing proofs for families defined by a vector recurrence apply this criterion. The
binomial Eulerian polynomials are the $h$-polynomials of the stellohedra
([OEIS A046802](https://oeis.org/A046802)), and Gustafsson and Solus use their lemma for the
box polynomials of $s$-lecture hall simplices. Matrices of differential operators are treated
on the [matrix recurrences page](rr:interlacing-matrix-recurrences).

## Proof

For entries in $\{0,1,x\}$ the criterion leaves a finite table, and every matrix outside it maps
an explicit sparse pair to a pair that does not interlace. For the product-sum theorem, the
products $f_ig_{n+1-i}$ have pairwise common interleavers, and by the Chudnovsky–Seymour theorem
on [common interleavers](rr:common-interleavers) the whole family has one.

## References

[@Fisk2006x, Ch. 3]; [@Branden2015, Thm. 7.8.5]; [@HaglundZhang2019];
[@GustafssonSolus2020, Lemma 3.4]; [@MaMaYeh2017x]. See also the
[matrix criterion](sf:matrixPreservesInterlacingSequences) and the
[binomial Eulerian polynomials](sf:binomialEulerianPolynomial) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
