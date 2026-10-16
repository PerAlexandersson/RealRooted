module

public import RealRooted.LGV.PathMatrix
public import RealRooted.LGV.PolyaFrequency
public import RealRooted.LGV.RepeatedChip
public import RealRooted.LGV.TotallyNonnegative

/-!
# Lindström–Gessel–Viennot challenge entry point

<!-- realrooted-catalog
version = 1
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
label = "Path networks give totally nonnegative matrices"
headline = true

[[theorems]]
name = "RealRooted.isPolyaFreqSeq_of_minorOrderedCertificates"
module = "RealRooted.LGV.PolyaFrequency"
label = "Path networks give Pólya frequency sequences"
headline = true

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

The [Lindström–Gessel–Viennot lemma](sf:lindstromGesselViennotLemma)
expresses a path-matrix minor as a signed sum over vertex-disjoint path
families. The formalization uses ordered cancellation certificates to show
that the surviving terms have nonnegative weights.

Building on the path-cancellation proof in the LeanLGV library:

- **Total nonnegativity:** a finite path network with nonnegative weights
  and ordered cancellation certificates for every pair of increasing row and
  column selections has a totally nonnegative matrix.
- **Pólya frequency sequences:** if every strictly increasing Toeplitz minor
  of a sequence is realized by such a network, then the sequence is a Pólya
  frequency sequence.
- **Chip networks:** for words of nonnegative lower-bidiagonal chips $G$ and
  $K$, with $K$ strictly lower triangular, the repeated-chip kernel sequence
  is a Pólya frequency sequence. The associated kernel row, in the sense of
  Brändén and Saud Leite, is a PF polynomial.
- **Path counting:** weighted paths of exact length $n$ are counted by the
  $n$-th power of the edge-sum matrix.

## References

See [@Lindstrom1973; @GesselViennot1985]. The kernel rows connect to the
[Brändén–Saud Leite page](/RealRooted/theorems/branden-leite/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The path-cancellation argument lives in
the LeanLGV dependency; the adapters live in `RealRooted.LGV`.
-/
