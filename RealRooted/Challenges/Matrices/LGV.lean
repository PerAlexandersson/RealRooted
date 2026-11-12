module

import RealRooted.LGV.PathMatrix
import RealRooted.LGV.PolyaFrequency
import RealRooted.LGV.RepeatedChip
import RealRooted.LGV.TotallyNonnegative

/-!
# Lindström–Gessel–Viennot challenge entry point

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
# Lindström–Gessel–Viennot and total positivity

Path networks with nonnegative weights and ordered cancellation certificates give totally
nonnegative matrices and Pólya frequency sequences.

## Results

The [Lindström–Gessel–Viennot lemma](sf:lindstromGesselViennotLemma) expresses a minor of a
path matrix as a signed sum over vertex-disjoint path families. Here the surviving terms are
shown to have nonnegative weights using ordered cancellation certificates, building on the
path-cancellation proof in the LeanLGV library.

**Theorem (total nonnegativity).** Let $N$ be a finite path network over an ordered ring with
nonnegative path weights. If every minor with strictly increasing row and column selections has
an ordered cancellation certificate, then the path matrix of $N$ is totally nonnegative.

**Theorem (Pólya frequency sequences).** Let $a=(a_k)$ be a real sequence. If every strictly
increasing Toeplitz minor of $a$ is the path matrix of a network with nonnegative weights and an
ordered cancellation certificate, then $a$ is a Pólya frequency sequence.

**Theorem (chip networks).** A *chip* is a lower-bidiagonal matrix on levels $0,\dots,N$. Let
$G,K$ be words of chips with nonnegative weights such that the product matrix of $K$ is
strictly lower triangular. Then the repeated-chip kernel sequence of $(G,K)$ is a Pólya frequency
sequence, and the kernel row of Brändén and Saud Leite at the last level is a PF polynomial.

**Proposition (path counting).** For a weighted quiver with finitely many vertices, the sum of
the weights of the paths of length $n$ from $a$ to $b$ is the $(a,b)$ entry of the $n$-th power
of the edge-sum matrix.

## References

See [@Lindstrom1973; @GesselViennot1985]. The kernel rows connect to the
[Brändén–Saud Leite page](/RealRooted/theorems/branden-leite/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The path-cancellation argument lives in
the LeanLGV dependency; the adapters live in `RealRooted.LGV`.
-/
