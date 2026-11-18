module

import RealRooted.LGV.ChipNetwork.Word
import RealRooted.LGV.PathMatrix
import RealRooted.LGV.PolyaFrequency
import RealRooted.LGV.RepeatedChip
import RealRooted.LGV.Toeplitz
import RealRooted.LGV.TotallyNonnegative

/-!
# Lindström–Gessel–Viennot lemma and total positivity

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "lindstrom-gessel-viennot"
formalized = "2026-09-17"
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
label = "LGV: path matrices with nonnegative weights and ordered cancellation are TNN"
headline = true

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_of_minorOrderedCertificates"
module = "RealRooted.LGV.PolyaFrequency"
label = "Toeplitz minors realized by such networks make a Pólya frequency sequence"

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

The Lindström–Gessel–Viennot lemma writes a minor of the path matrix of a network as a signed
sum over families of paths. When the non-disjoint families cancel and the sources and sinks are
in order, every minor is nonnegative, so the path matrix is totally nonnegative.

## Results

The *path matrix* of a finite network has as $(s,t)$ entry the total weight of the paths from
$s$ to $t$. A minor with sources $s_1<\dots<s_n$ and sinks $t_1<\dots<t_n$ *cancels in order*
if there is a disjointness relation on pairs of paths such that paths in opposite order are
never disjoint, and a weight-negating involution on the non-disjoint path families. The
classical example is vertex-disjointness in a planar network with sources and sinks in order
along the boundary.

**Theorem (Lindström, Gessel–Viennot).** [@Lindstrom1973; @GesselViennot1985] If a finite
network has nonnegative path weights and every minor cancels in order, then its path matrix is
totally nonnegative.

**Corollary (Pólya frequency sequences).** If every Toeplitz minor of a real sequence $a$ is
the path matrix of such a network, then $a$ is a Pólya frequency sequence.

**Corollary (chip networks).** A *chip* is a lower-bidiagonal matrix. Let $G,K$ be words of
chips with nonnegative weights such that the product of $K$ is strictly lower triangular. Then
the repeated-chip kernel sequence of $(G,K)$ is a Pólya frequency sequence, and its kernel row
at the last level is a PF polynomial.

In a weighted quiver, the total weight of the paths of length $n$ from $a$ to $b$ is the
$(a,b)$ entry of the $n$-th power of the edge-sum matrix.

## Use

The lemma is the main source of [totally nonnegative matrices](rr:totally-nonnegative-matrices)
and Pólya frequency sequences in combinatorics. The chip networks give the kernel rows used by
[Brändén and Saud Maia Leite](rr:branden-leite).

## Proof

The involution cancels the families that are not pairwise disjoint. A pairwise disjoint family
cannot contain two paths in opposite order, so it connects $s_i$ to $t_i$ for every $i$ and
contributes its nonnegative weight with sign $+1$.

## References

[@Lindstrom1973]; [@GesselViennot1985]. See also the
[Lindström–Gessel–Viennot lemma](sf:lindstromGesselViennotLemma) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
