import RealRooted.FactorialCompression.DegreeChanging
import RealRooted.Hadamard.SchurSzegoStrict

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
module = "RealRooted.FactorialCompression.Basic"
label = "Factorial-compression operator"

[[definitions]]
name = "RealRooted.FactorialCompression.nextPolynomial"
module = "RealRooted.FactorialCompression.Basic"
label = "Degree-raising differential step"

[[definitions]]
name = "RealRooted.FactorialCompression.kernel"
module = "RealRooted.FactorialCompression.Basic"
label = "Degree-changing kernel"

[[theorems]]
name = "RealRooted.FactorialCompression.compression_nextPolynomial_strictInterl"
module = "RealRooted.FactorialCompression.DegreeChanging"
label = "Factorial compression gives strict negative-root interlacing"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_schurSzegoComp_of_roots_neg"
module = "RealRooted.Hadamard.SchurSzegoStrict"
label = "Strict Schur–Szegő endpoint: strict interlacing is preserved"
headline = true

[[theorems]]
name = "RealRooted.FactorialCompression.compression_one_nextPolynomial_strictInterl"
module = "RealRooted.FactorialCompression.DegreeChanging"
label = "The level-one case used for separable permutations"

[[theorems]]
name = "RealRooted.FactorialCompression.compression_eq_schurSzegoComp"
module = "RealRooted.FactorialCompression.Compression"
label = "Compression is a Schur–Szegő composition"

[[theorems]]
name = "RealRooted.FactorialCompression.strictInterl_commonKernel_kernel"
module = "RealRooted.FactorialCompression.Kernel"
label = "The common kernel strictly interlaces the degree-changing kernel"
-->

<!-- realrooted-catalog-content -->
# Factorial compression and strict interlacing

For integers `N ≥ 1` and `0 ≤ ell ≤ N`, factorial compression rescales the
coefficient of `x^k` by

`(N-k)! / (N+ell-2k)!`

on its natural support.  If a degree-`N` polynomial `p` has positive leading
coefficient and all roots strictly negative (repeated roots allowed), then for
`a > 0` the compression of `p` and the compression of the adjacent differential
step `(x + a) p + x p'` have the exact floor degrees `⌊(N+ell)/2⌋` and
`⌊(N+ell+1)/2⌋`, positive leading coefficients, simple strictly negative roots,
strictly interlace, and have no common root.

The proof writes the compression as a Schur–Szegő composition with a multiplier,
identifies the degree-changing kernel, establishes its negative-root geometry, and
transfers strict interlacing through the composition by the strict Schur–Szegő
endpoint: composition with a multiplier of the right degree having only negative
roots preserves strict interlacing of polynomials without common roots.  The
adjacent-degree lifting to gamma transforms is a separate step, used for the
separable permutations.

## References

Z. Zhang, *A Factorial Compression Theorem for Strict Interlacing* (2026),
[SSRN preprint](https://ssrn.com/abstract=7510941).  The Lean development follows the draft
formalization of PR #1132 by yyou59548-design.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.FactorialCompression` and
`RealRooted.Hadamard.SchurSzegoStrict`.
-/
