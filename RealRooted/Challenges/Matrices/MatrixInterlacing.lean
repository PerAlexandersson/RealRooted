module

public import RealRooted.MatrixInterlacing
public import RealRooted.MatrixInterlacing.Composition
public import RealRooted.MatrixInterlacing.Converse
import RealRooted.MatrixInterlacing.Preservation

/-!
# Matrix interlacing challenge entry point

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
name = "RealRooted.Challenges.MatrixInterlacing.preservesInterlacingSeq0_iff"
label = "A matrix preserves interlacing sequences exactly when its 2 × 2 submatrices do"
headline = true
symcat = "matrixPreservesInterlacingSequences"

[[theorems]]
name = "RealRooted.Challenges.MatrixInterlacing.preserves_interlacing_sequences"
label = "Strict form: the strict condition preserves strict interlacing sequences"

[[theorems]]
name = "RealRooted.Challenges.MatrixInterlacing.preserves_interlacing_sequences_zeroAware"
label = "Strict input, zero-aware output"

[[theorems]]
name = "RealRooted.matPolyMul_preservesInterlacingSeq0"
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
either one of them is zero, or both are nonzero, real-rooted and interlace weakly. Thus, unlike
elsewhere in the catalog, either side of $f\ll g$ may be zero. Let $\mathcal F_n^{0}$ be the set
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
is nonzero and real-rooted. The products $f_ig_{n+1-i}$ have pairwise common interleavers, which
by the Chudnovsky–Seymour theorem gives a common interleaver of the whole family. If instead
the terms of each sequence interlace weakly, every nonzero term is real-rooted and the sum is
nonzero, then the sum is real-rooted.

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

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace MatrixInterlacing

/-- **The matrix criterion** (Brändén, Theorem 7.8.5, zero-aware form).  A
polynomial matrix `G` with `n` columns maps the zero-aware nonnegative
real-rooted interlacing family into itself if and only if its entries have
nonnegative coefficients and every ordered 2-by-2 submatrix, repeated indices
allowed, satisfies the weak affine condition. -/
theorem preservesInterlacingSeq0_iff {n : ℕ} (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n) :
    PreservesInterlacingSeq0 n G ↔
      (∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p) ∧
      ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n), i₁ ≤ i₂ → j₁ ≤ j₂ →
        Has2x2InterlacingProperty0
          ((G.get i₁).get ⟨j₁, by simp_all⟩)
          ((G.get i₁).get ⟨j₂, by simp_all⟩)
          ((G.get i₂).get ⟨j₁, by simp_all⟩)
          ((G.get i₂).get ⟨j₂, by simp_all⟩) :=
  RealRooted.preservesInterlacingSeq0_iff G hG_rect

/-- The matrix criterion, strict forward direction: the affine 2-by-2
conditions imply preservation of nonnegative interlacing sequences. -/
theorem preserves_interlacing_sequences {n : ℕ} (hn : n ≠ 0) (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n) (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg (matPolyAction G fs) :=
  RealRooted.matrix_preserves_interlacing_seq (Nat.pos_of_ne_zero hn) G hG_rect hG_nonneg
    hG_affine fs hfs_len hfs

/-- Forward direction with strict input and zero-aware output: the weak affine
2-by-2 conditions map strict nonnegative interlacing sequences into the
zero-aware family, so some output rows may vanish. -/
theorem preserves_interlacing_sequences_zeroAware {n : ℕ} (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n) (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) :=
  RealRooted.matrix_preserves_interlacing_seq0_of_2x2 G hG_rect hG_nonneg hG_affine fs
    hfs_len hfs

end MatrixInterlacing
end Challenges
end RealRooted
