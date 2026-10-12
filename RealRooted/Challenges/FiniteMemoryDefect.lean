import RealRooted.FiniteMemory.Defect

/-!
# Finite-memory degree-defect bridges

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "finite-memory-defect-bridges"

[[theorems]]
name = "RealRooted.HasNonnegCoeffs.natDegree_add_eq_max"
module = "RealRooted.FiniteMemory.Defect"
label = "Nonnegative sums have maximal degree"

[[theorems]]
name = "RealRooted.HasNonnegCoeffs.natTrailingDegree_add_eq_min"
module = "RealRooted.FiniteMemory.Defect"
label = "Nonnegative sums have minimal trailing degree"

[[theorems]]
name = "RealRooted.FiniteMemory.symbolSeries_mul_one_sub_lagSeries"
module = "RealRooted.FiniteMemory.Defect"
label = "Fundamental symbol-series identity"

[[theorems]]
name = "RealRooted.FiniteMemory.symbolRow_eq_sum_mul_coeff_lagSeries"
module = "RealRooted.FiniteMemory.Defect"
label = "Fundamental-row convolution recurrence"

[[theorems]]
name = "RealRooted.FiniteMemory.symbolRow_hasNonnegCoeffs"
module = "RealRooted.FiniteMemory.Defect"
label = "Fundamental rows have nonnegative coefficients"

[[theorems]]
name = "RealRooted.FiniteMemory.SharpDefectBridges.exists_exact_minimizer"
module = "RealRooted.FiniteMemory.Defect"
label = "Sharp bridges give eventual minimum-cost words"

[[theorems]]
name = "RealRooted.FiniteMemory.SharpDefectBridges.exists_upper_degree_word"
module = "RealRooted.FiniteMemory.Defect"
label = "Sharp bridges give scaled upper-degree words"

[[theorems]]
name = "RealRooted.FiniteMemory.SharpDefectBridges.exists_lower_degree_word"
module = "RealRooted.FiniteMemory.Defect"
label = "Sharp bridges give scaled lower-degree words"

[[theorems]]
name = "RealRooted.FiniteMemory.exists_fractional_upper_degree_word"
module = "RealRooted.FiniteMemory.Defect"
label = "The fractional $(2,3)$ upper-degree bridge"
-->

<!-- realrooted-catalog-content -->
# Finite-memory degree-defect bridges

For two nonzero polynomials with nonnegative coefficients, we prove that the
degree of their sum is the maximum of their degrees and its trailing degree is
the minimum of their trailing degrees.  We define the lag and symbol power
series of a finite-memory symbol, prove the inverse identity for the symbol
series, derive its positive convolution recurrence, and show that all
fundamental rows have nonnegative coefficients when the symbol coefficients do.

We next formalize consequences of a `SharpDefectBridges` certificate.  Given
such a certificate, every index $n\geq(r-1)(r-2)$ has an active lag word of
total lag $n$ with the prescribed residue cost, and no active word of that
total lag has smaller cost.  The upper and lower bridge theorems turn the
corresponding pointwise scaled degree identities into exact word identities.

The residue-bridge certificate `SharpDefectBridges` is a hypothesis: its
general construction from an active finite-memory symbol is not formalized in
this module.  We do construct the certificate for active lags $2$ and $3$,
with upper costs $1$ and $0$, respectively; hence every $n\geq2$ has a word
whose scaled upper degree satisfies $3d+K_{n\bmod3}=2n$.

## References

R. Bøgvad and C. Hägg, “A refinement of Pólya's method to construct Voronoi
diagrams for rational functions,” *Journal of Mathematical Analysis and
Applications*, [arXiv:1610.00921](https://arxiv.org/abs/1610.00921).
B. Nyandwi, C. Hägg, C. Kurujyibwami, and L. F. R. Uwimbabazi, “Voronoi limit
measures for iterates of constant-coefficient differential operators on
rational functions with simple poles,”
[arXiv:2604.05189](https://arxiv.org/abs/2604.05189).
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.FiniteMemoryDefect

end RealRooted.Challenges.FiniteMemoryDefect
