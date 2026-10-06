import RealRooted.FactorialCompression.DegreeChanging
import RealRooted.FactorialCompression.Lifting

/-!
# Factorial compression and strict interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "factorial-compression"
authors = ["Zhanhe Zhang"]
years = [2026]

[[definitions]]
name = "RealRooted.FactorialCompression.compression"
module = "RealRooted.FactorialCompression.Definitions"
label = "Factorial-compression operator"

[[definitions]]
name = "RealRooted.FactorialCompression.nextPolynomial"
module = "RealRooted.FactorialCompression.Definitions"
label = "Degree-raising differential step"

[[theorems]]
name = "RealRooted.FactorialCompression.compression_nextPolynomial_geometry_of_roots_neg"
module = "RealRooted.FactorialCompression.Theorems"
label = "Factorial compression gives strict negative-root interlacing"
headline = true

[[theorems]]
name = "RealRooted.FactorialCompression.gammaTransform_succ_geometry_of_strictInterl"
module = "RealRooted.FactorialCompression.Theorems"
label = "Two-branch gamma lifting preserves strict interlacing"
headline = true
-->

<!-- realrooted-catalog-content -->
# Factorial compression and strict interlacing

For integers `N ≥ 1` and `0 ≤ ell ≤ N`, factorial compression rescales the
coefficient of `x^k` by

`(N-k)! / (N+ell-2k)!`

on its natural support.  If a degree-`N` polynomial has positive leading
coefficient and all roots strictly negative, then the compressed polynomial
and the compression of the adjacent differential step have the exact floor
degrees predicted by the parameter `ell`, have simple strictly negative roots,
and are strictly interlacing with no common root.

The proof factors the compression through the canonical Schur--Szegő
composition, identifies the degree-changing kernel, establishes its
negative-root geometry, and transfers strict interlacing through the
composition. A companion theorem records the adjacent-degree gamma lifting
used in applications.

## References

Z. Zhang, *A Factorial Compression Theorem for Strict Interlacing* (2026),
[SSRN preprint](https://ssrn.com/abstract=7510941).
<!-- /realrooted-catalog-content -->
-/
