import RealRooted.MatrixInterlacing

/-!
# Matrix interlacing challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "matrix-interlacing"
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

[[theorems]]
name = "RealRooted.Challenges.MatrixInterlacing.preservesInterlacingSeq0_iff"
label = "A matrix preserves interlacing sequences exactly when its 2 × 2 submatrices do"
headline = true

[[theorems]]
name = "RealRooted.Challenges.MatrixInterlacing.preserves_interlacing_sequences"
label = "Strict form: the strict condition preserves strict interlacing sequences"

[[theorems]]
name = "RealRooted.Challenges.MatrixInterlacing.preserves_interlacing_sequences_zeroAware"
label = "Strict input, zero-aware output"
-->

<!-- realrooted-catalog-content -->
# Matrices preserving interlacing sequences

Let $G = (G_{ij})$ be an $m \times n$ matrix of real polynomials. It acts on a
sequence $F = (f_1, \dots, f_n)$ by $(G F)_i = \sum_j G_{ij} f_j$. For
polynomials $f, g$ we write $f \ll g$ when $f$ and $g$ interlace weakly: either
one of them is zero, or both are nonzero, real-rooted and interlacing. Let
$\mathcal{F}_n^{0}$ be the set of sequences $(f_1, \dots, f_n)$ of polynomials
with nonnegative coefficients such that every nonzero $f_i$ is real-rooted and
$f_i \ll f_j$ whenever $i < j$.

**Theorem.** The matrix $G$ maps $\mathcal{F}_n^{0}$ into $\mathcal{F}_m^{0}$
if and only if

1. every entry $G_{ij}$ has nonnegative coefficients, and
2. for all rows $i_1 \le i_2$ and columns $j_1 \le j_2$, the submatrix
   $\begin{pmatrix} a & b \\ c & d \end{pmatrix} =
   \begin{pmatrix} G_{i_1 j_1} & G_{i_1 j_2} \\ G_{i_2 j_1} & G_{i_2 j_2}
   \end{pmatrix}$ satisfies
   $$
   (s x + t)\, b + d \ \ll\ (s x + t)\, a + c
   \qquad \text{for all } s, t > 0.
   $$

Repeated indices $i_1 = i_2$ or $j_1 = j_2$ are allowed in condition 2.

The page also records two forward statements for strict input. Call
$(f_1, \dots, f_n)$ strict if every $f_i$ is nonzero and real-rooted with
nonnegative coefficients, and $f_i \ll f_j$ whenever $i < j$. Suppose that $G$
satisfies condition 1, that $n \ge 1$, and that condition 2 holds with both
sides of $\ll$ required to be nonzero. Then $G$ maps strict sequences to strict
sequences. Under conditions 1 and 2 as stated, $G$ maps a strict sequence to a
sequence $(g_1, \dots, g_m)$ of polynomials with nonnegative coefficients and
$g_i \ll g_j$ whenever $i < j$, where some $g_i$ may vanish.

## Proof idea

Sufficiency is Brändén's argument: for rows $i_1 \le i_2$, condition 2 makes
the columns of the affine combinations $(s x + t) G_{i_1 j} + G_{i_2 j}$
interlace, and so the image rows interlace. For necessity, apply $G$ to sparse
test sequences. The sequence with $1$ in position $j$ and zeros elsewhere
gives condition 1 and the case $j_1 = j_2$. The sequence with $1$ in position
$j_1$, $s' x + t'$ in position $j_2$ and zeros elsewhere gives
$a + (s' x + t') b \ll c + (s' x + t') d$. Hence
$(s' x + t')\bigl((s x + t) b + d\bigr) + (s x + t) a + c$ is real-rooted for
all $s', t' > 0$, and the affine-family criterion (Brändén, Lemma 7.8.4)
turns this into condition 2.

## References

S. Fisk, *Polynomials, roots, and interlacing*, 2006, Chapter 3, develops
matrices preserving interlacing. P. Brändén gives the exact nonnegative
polynomial characterization in “Unimodality, log-concavity, real-rootedness
and beyond,” *Handbook of Enumerative Combinatorics*, 2015, Theorem 7.8.5. See the
[matrix criterion on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#matrixPreservesInterlacingSequences).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#matrixPreservesInterlacingSequences

References: S. Fisk, *Polynomials, roots, and interlacing* (2006), Chapter 3;
P. Branden, *Unimodality, log-concavity, real-rootedness and beyond*,
Handbook of Enumerative Combinatorics (2015), Theorem 7.8.5.

This module exposes the checked exact characterization for the zero-aware
family, together with the strict forward theorem and its zero-aware-output
variant.  The sparse test families and the 2-by-2 reduction machinery live in
`RealRooted.MatrixInterlacing`.
-/

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
