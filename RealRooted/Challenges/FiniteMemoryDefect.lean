import RealRooted.FiniteMemory.Defect

/-!
# Finite-memory degree-defect bridges

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "finite-memory-defect-bridges"
formalized = "2026-10-11"

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

We next construct a `SharpDefectBridges` certificate from any bounded positive
active lag set of gcd one and a chosen zero-cost lag.  A finite residue
automaton shortens minimum-cost representatives to simple paths, giving the
uniform threshold $(r-1)(r-2)$.  Thus every index above that threshold has an
active lag word of the prescribed residue cost, and no active word of the same
total lag has smaller cost.  The upper and lower bridge theorems turn the
pointwise scaled degree identities into exact word identities.

For active lags $2$ and $3$, with upper costs $1$ and $0$, respectively, the
general construction specializes to the explicit certificate below.  Hence
every $n\geq2$ has a word whose scaled upper degree satisfies
$3d+K_{n\bmod3}=2n$.

## References

R. Bøgvad and C. Hägg, “A refinement for rational functions of Pólya's method
to construct Voronoi diagrams,” *Journal of Mathematical Analysis and
Applications* 452(1) (2017), 312–334,
[doi:10.1016/j.jmaa.2017.02.071](https://doi.org/10.1016/j.jmaa.2017.02.071);
B. Nyandwi, C. Hägg, C. Kurujyibwami, and L. F. R. Uwimbabazi, “Voronoi limit
measures for iterates of constant-coefficient differential operators on
rational functions with simple poles,”
[arXiv:2604.05189](https://arxiv.org/abs/2604.05189).
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.FiniteMemoryDefect

end RealRooted.Challenges.FiniteMemoryDefect
