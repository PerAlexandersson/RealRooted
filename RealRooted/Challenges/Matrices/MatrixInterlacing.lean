module

public import RealRooted.AffineFamily.Basic
public import RealRooted.InterlacingSequenceBasic
public import RealRooted.MatrixInterlacing
public import RealRooted.MatrixInterlacing.Action
public import RealRooted.MatrixInterlacing.Composition
public import RealRooted.MatrixInterlacing.Converse
public import RealRooted.MatrixInterlacing.Preservation
public import RealRooted.ProductFamily

/-!
# Matrices preserving interlacing sequences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "matrix-interlacing"
formalized = "2026-10-06"
tags = []
references = [
  "Fisk2006x",
  "Branden2015",
]
authors = ["Fisk", "Brändén"]
years = [2006, 2015]

[[definitions]]
name = "RealRooted.matPolyAction"
module = "RealRooted.MatrixInterlacing.Action"
label = "A polynomial matrix acting on a sequence"

[[definitions]]
name = "RealRooted.IsInterlacingSeq0NonnegRealRooted"
module = "RealRooted.InterlacingSequenceBasic"
label = "Zero-aware nonnegative real-rooted interlacing sequence"

[[definitions]]
name = "RealRooted.PreservesInterlacingSeq0"
module = "RealRooted.MatrixInterlacing.Converse"
label = "The matrix preserves zero-aware interlacing sequences"

[[definitions]]
name = "RealRooted.Has2x2InterlacingProperty0"
module = "RealRooted.AffineFamily.Basic"
label = "2 × 2 interlacing condition, allowing zeros"

[[definitions]]
name = "RealRooted.Has2x2InterlacingProperty"
module = "RealRooted.AffineFamily.Basic"
label = "2 × 2 interlacing condition"

[[definitions]]
name = "RealRooted.IsInterlacingSeqNonneg"
module = "RealRooted.InterlacingSequenceBasic"
label = "Interlacing sequence of real-rooted polynomials with nonnegative coefficients"

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
name = "RealRooted.IsInterlacingSeq0Nonneg.matPolyAction_of_2x2"
module = "RealRooted.MatrixInterlacing.Preservation"
label = "Strict input, zero-aware output"

[[theorems]]
name = "RealRooted.PreservesInterlacingSeq0.matPolyMul"
module = "RealRooted.MatrixInterlacing.Composition"
label = "Products of interlacing-preserving matrices preserve interlacing"

[[theorems]]
name = "RealRooted.isInterlacingSeq_iff_pairwise"
module = "RealRooted.InterlacingSequenceBasic"
label = "A sequence is interlacing exactly when it is pairwise interlacing"

[[theorems]]
name = "RealRooted.isInterlacingSeq0_iff_pairwise"
module = "RealRooted.InterlacingSequenceBasic"
label = "The zero-aware version is pairwise weak interlacing"

[[theorems]]
name = "RealRooted.isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeqNonneg"
module = "RealRooted.ProductFamily"
label = "The reversed product-sum of two interlacing nonnegative sequences is real-rooted"

[[theorems]]
name = "RealRooted.zipWith_mul_sum_reverse_isRealRooted"
module = "RealRooted.ProductFamily"
label = "The reversed product-sum theorem allowing zero terms in both sequences"
-->

<!-- realrooted-catalog-content -->
# Matrices preserving interlacing sequences

A matrix of polynomials with nonnegative coefficients maps interlacing sequences to interlacing
sequences if and only if every ordered $2\times2$ submatrix satisfies an affine interlacing
condition.

## Results

Let $G=(G_{ij})$ be an $m\times n$ matrix of real polynomials. It acts on a sequence
$F=(f_1,\dots,f_n)$ by $(GF)_i=\sum_jG_{ij}f_j$. For polynomials $f,g$ we write $f\ll g$ if
either one of them is zero, or both are nonzero, real-rooted and interlace weakly, as in the
zero-aware convention of [Conventions](rr:about). Let $\mathcal F_n^{0}$ be the set
of sequences $(f_1,\dots,f_n)$ of polynomials with nonnegative coefficients such that every
nonzero $f_i$ is real-rooted and $f_i\ll f_j$ whenever $i<j$.

**Theorem (matrix criterion).** The matrix $G$ maps $\mathcal F_n^{0}$ into $\mathcal F_m^{0}$ if
and only if

1. every entry $G_{ij}$ has nonnegative coefficients, and
2. for all rows $i_1\le i_2$ and columns $j_1\le j_2$, the submatrix
   $\begin{pmatrix}a&b\\c&d\end{pmatrix}=
   \begin{pmatrix}G_{i_1j_1}&G_{i_1j_2}\\G_{i_2j_1}&G_{i_2j_2}\end{pmatrix}$ satisfies
   $$
   (sx+t)\,b+d\ \ll\ (sx+t)\,a+c\qquad\text{for all }s,t>0.
   $$

Repeated indices $i_1=i_2$ or $j_1=j_2$ are allowed in condition 2.

**Theorem (strict input).** Call $(f_1,\dots,f_n)$ *strict* if every $f_i$ is nonzero and
real-rooted with nonnegative coefficients, and $f_i\ll f_j$ for $i<j$. Let $n\ge1$ and let $G$
satisfy condition 1.

- If condition 2 holds with both sides of $\ll$ nonzero, then $G$ maps strict sequences to strict
  sequences.
- Under condition 2 as stated, $G$ maps a strict sequence to a sequence $(g_1,\dots,g_m)$ of
  polynomials with nonnegative coefficients and $g_i\ll g_j$ for $i<j$, where some $g_i$ may
  vanish.

**Proposition (products).** If an $m\times k$ matrix $H$ and a $k\times n$ matrix $G$ both map
$\mathcal F^0$ into itself, so does $HG$.

**Theorem (product-sum).** [@Branden2015, §7.8] Let $(f_1,\dots,f_n)$ and $(g_1,\dots,g_n)$,
$n\ge1$, be interlacing sequences of real-rooted polynomials with nonnegative coefficients. Then
$$
\sum_{i=1}^nf_i\,g_{n+1-i}
$$
is nonzero and real-rooted. If instead the terms of each sequence interlace weakly, every
nonzero term is real-rooted and the sum is nonzero, then the sum is real-rooted.

## Proof

For the product-sum theorem, the products $f_ig_{n+1-i}$ have pairwise common interleavers, and
by the Chudnovsky–Seymour theorem on [common interleavers](rr:common-interleavers) this gives a
common interleaver of the whole family.

## References

Matrices preserving interlacing are treated in [@Fisk2006x, Ch. 3]. The exact nonnegative
polynomial characterization is [@Branden2015, Thm. 7.8.5]. See the
[matrix criterion on symmetricfunctions.com](sf:matrixPreservesInterlacingSequences).
<!-- /realrooted-catalog-content -->

Human statement:
sf:matrixPreservesInterlacingSequences

References: S. Fisk, *Polynomials, roots, and interlacing* (2006), Chapter 3;
P. Branden, *Unimodality, log-concavity, real-rootedness and beyond*,
Handbook of Enumerative Combinatorics (2015), Theorem 7.8.5.

This module exposes the checked exact characterization for the zero-aware
family, together with the strict forward theorem and its zero-aware-output
variant.  The sparse test families and the 2-by-2 reduction machinery live in
`RealRooted.MatrixInterlacing`.
-/
