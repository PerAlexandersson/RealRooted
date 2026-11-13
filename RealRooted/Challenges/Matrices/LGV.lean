module

import RealRooted.LGV.PathMatrix
import RealRooted.LGV.PolyaFrequency
import RealRooted.LGV.RepeatedChip
import RealRooted.LGV.TotallyNonnegative

/-!
# Lindström–Gessel–Viennot lemma and total positivity

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "lindstrom-gessel-viennot"
formalized = "2026-09-17"
tags = []
references = [
  "Lindstrom1973",
  "GesselViennot1985",
]
authors = ["Lindström", "Gessel", "Viennot"]
years = [1973, 1985]

[[definitions]]
name = "RealRooted.StrictToeplitzMinorIndex"
module = "RealRooted.LGV.Toeplitz"
label = "Index set of a Toeplitz minor"

[[definitions]]
name = "RealRooted.LGV.ChipNetwork.Chip"
module = "RealRooted.LGV.ChipNetwork.Word"
label = "Lower-bidiagonal chip"

[[definitions]]
name = "RealRooted.LGV.ChipNetwork.wordMatrix"
module = "RealRooted.LGV.ChipNetwork.Word"
label = "Matrix of a word of chips"

[[definitions]]
name = "RealRooted.LGV.RepeatedChip.kernelSequence"
module = "RealRooted.LGV.RepeatedChip"
label = "Repeated-chip kernel sequence"

[[theorems]]
name = "LGV.FinitePathNetwork.matrix_isTotallyNonneg_of_orderedCertificates"
module = "RealRooted.LGV.TotallyNonnegative"
label = "Path networks give totally nonnegative matrices"
headline = true

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_of_minorOrderedCertificates"
module = "RealRooted.LGV.PolyaFrequency"
label = "Path networks give Pólya frequency sequences"

[[theorems]]
name = "RealRooted.LGV.RepeatedChip.kernelSequence_isPolyaFreqSeq"
module = "RealRooted.LGV.RepeatedChip"
label = "Repeated-chip kernel sequences are PF"

[[theorems]]
name = "RealRooted.LGV.RepeatedChip.kernelRow_isPFPolynomial"
module = "RealRooted.LGV.RepeatedChip"
label = "Repeated-chip kernel rows are PF polynomials"

[[theorems]]
name = "Quiver.Path.sum_weight_exactLength_eq_edgeSumMatrix_pow"
module = "RealRooted.LGV.PathMatrix"
label = "Paths of length n and powers of the edge matrix"
-->

<!-- realrooted-catalog-content -->
# Lindström–Gessel–Viennot lemma and total positivity

Path matrices of networks with nonnegative weights are totally nonnegative whenever the
Lindström–Gessel–Viennot cancellation works with sources and sinks in order. Applied to
Toeplitz minors, this gives Pólya frequency sequences, for instance from networks of
lower-bidiagonal chips.

## Results

The *path matrix* of a finite network with weighted paths has as $(s,t)$ entry the total weight
of the paths from $s$ to $t$. The [Lindström–Gessel–Viennot lemma](sf:lindstromGesselViennotLemma)
writes a minor of the path matrix, with sources $s_1<\dots<s_n$ and sinks $t_1<\dots<t_n$, as a
signed sum over path families. We say the minor *cancels in order* if there is a notion of
disjointness for pairs of paths such that two paths from $s_i$ to $t_k$ and from $s_j$ to $t_l$
with $s_i<s_j$ and $t_l<t_k$ are never disjoint, together with a weight-negating involution on
the signed path families that are not pairwise disjoint, fixing only families of weight zero.
Vertex-disjointness in a planar network with sources and sinks in order along the boundary is
the classical example.

**Theorem (total nonnegativity).** Let $N$ be a finite path network over an ordered ring with
nonnegative path weights. If every minor with strictly increasing row and column selections
cancels in order, then the path matrix of $N$ is totally nonnegative.

**Theorem (Pólya frequency sequences).** Let $a=(a_k)$ be a real sequence. If each Toeplitz
submatrix of $a$ with strictly increasing rows and columns is the path matrix of a network with
nonnegative weights whose determinant cancels in order, then $a$ is a Pólya frequency sequence.

**Theorem (chip networks).** A *chip* is a lower-bidiagonal matrix on levels $0,\dots,N$. Let
$G,K$ be words of chips with nonnegative weights such that the product matrix of $K$ is
strictly lower triangular. Then the repeated-chip kernel sequence of $(G,K)$ is a Pólya frequency
sequence, and the kernel row of [Brändén and Saud Leite](rr:branden-leite) at the last level is
a PF polynomial.

For a weighted quiver with finitely many vertices, the total weight of the paths of length $n$
from $a$ to $b$ is the $(a,b)$ entry of the $n$-th power of the edge-sum matrix.

## Proof

The involution cancels the families that are not pairwise disjoint. A pairwise disjoint family
cannot contain two paths in opposite order, so it connects $s_i$ to $t_i$ for every $i$ and
contributes its nonnegative weight with sign $+1$.

## References

[@Lindstrom1973; @GesselViennot1985].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The path-cancellation argument lives in
the LeanLGV dependency; the adapters live in `RealRooted.LGV`.
-/
