import RealRooted.BrandenLeite.CompositionFamilies
import RealRooted.BrandenLeite.ConstantDiagonal
import RealRooted.BrandenLeite.NetworkWhitney
import RealRooted.BrandenLeite.ResolvableTotallyNonneg
import RealRooted.BrandenLeite.Theorem37
import RealRooted.BrandenLeite.TwoKernel
import RealRooted.BrandenLeite.WeightedShiftTiling
import RealRooted.BrandenLeite.ZeroConstant

/-!
# Brändén–Saud Leite challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-leite"
authors = ["Brändén", "Saud Leite"]
years = [2024]

[[definitions]]
name = "RealRooted.BrandenLeite.chainPolynomial"
module = "RealRooted.BrandenLeite.ChainPolynomial.Algebra"

[[definitions]]
name = "RealRooted.BrandenLeite.IsResolvable"
module = "RealRooted.BrandenLeite.Resolvable"

[[definitions]]
name = "RealRooted.BrandenLeite.compositionRow"
module = "RealRooted.BrandenLeite.CompositionRow"

[[definitions]]
name = "RealRooted.BrandenLeite.twoKernelRow"
module = "RealRooted.BrandenLeite.TwoKernelAlgebra"

[[theorems]]
name = "RealRooted.BrandenLeite.interl_chainPolynomial_succ_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.Theorem37"

[[theorems]]
name = "RealRooted.BrandenLeite.roots_chainPolynomial_mem_Icc_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.Theorem37"

[[theorems]]
name = "RealRooted.BrandenLeite.chainPolynomial_hasNonnegCoeffs_of_isTotallyNonneg"
module = "RealRooted.BrandenLeite.Theorem37"

[[theorems]]
name = "RealRooted.BrandenLeite.isResolvable_iff_lowerUnitriangular_and_isTotallyNonneg"
module = "RealRooted.BrandenLeite.ResolvableTotallyNonneg"

[[theorems]]
name = "RealRooted.BrandenLeite.chainPolynomial_isPFPolynomial_of_pos_constantDiagonal"
module = "RealRooted.BrandenLeite.ConstantDiagonal"

[[theorems]]
name = "RealRooted.BrandenLeite.compositionRows_mk_pf_and_interl_of_zero"
module = "RealRooted.BrandenLeite.ZeroConstant"

[[theorems]]
name = "RealRooted.BrandenLeite.twoKernelRows_pf_and_interl"
module = "RealRooted.BrandenLeite.TwoKernel"

[[theorems]]
name = "RealRooted.BrandenLeite.binomialCompositionRows_pf_and_interl"
module = "RealRooted.BrandenLeite.CompositionFamilies"

[[theorems]]
name = "RealRooted.BrandenLeite.inversePowerCompositionRows_pf_and_interl"
module = "RealRooted.BrandenLeite.CompositionFamilies"

[[theorems]]
name = "RealRooted.BrandenLeite.networkMatrix_resolutionLambda_eq"
module = "RealRooted.BrandenLeite.NetworkWhitney"

[[theorems]]
name = "RealRooted.BrandenLeite.weightedShiftTilingRow_separated_isPFPolynomial"
module = "RealRooted.BrandenLeite.WeightedShiftTiling"
-->

<!-- realrooted-catalog-content -->
# Totally nonnegative matrices and chain polynomials

A lower-triangular matrix `A` defines chain polynomials by `P_0 = 1` and

```text
P_{n+1}(x) = x * sum_{k ≤ n} A(n+1,k) P_k(x).
```

When `A` counts weighted chains in a poset, `P_n` enumerates the chains by
length.

**Theorem (Brändén–Saud Leite, Theorem 3.7).** If `A` is lower unitriangular
and totally nonnegative, then every `P_n` has nonnegative coefficients and
only real zeros in `[-1, 0]`, and `P_n` interlaces `P_{n+1}`.

The matrices covered are exactly the resolvable ones: a lower-unitriangular
matrix admits a resolution by nonnegative weights and monic polynomials if and
only if it is totally nonnegative. The same conclusion holds for totally
nonnegative matrices with a positive constant diagonal.

Applied to power-series kernels built from Pólya frequency sequences, the
theorem gives PF polynomials whose consecutive rows interlace, for two row
families:

- the rows of `1 / (1 - x h(z))` when `h(0) = 0`;
- the rows of `g / (1 - x g h)`.

In particular, the rows of `1 / (1 - x z (1+z)^d)` and of
`1 / (1 - x z / (1-z)^e)` are PF and interlace. These include OEIS A116088
(`d = 2`), A116089 (`d = 3`) and A206294 (`e = 3`).

The resolution theorem has a network form. Every lower-unitriangular totally
nonnegative matrix is the path matrix of a triangular planar network whose
nonnegative weights come from Whitney elimination. The same machinery gives PF
rows for tiling polynomials built from weighted lower shifts.

## Proof idea

Whitney elimination factors a totally nonnegative unitriangular matrix into
nonnegative resolution data. The subdivision operator `X^n ↦ P_n` sends each
row of the resolution to an interlacing sequence, and interlacing is preserved
under the nonnegative combinations that assemble the chain polynomials.

## References

P. Brändén and L. Saud Maia Leite, [“Totally nonnegative matrices, chain
enumeration and zeros of polynomials,”](https://arxiv.org/abs/2412.06595)
arXiv:2412.06595 (2024).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.BrandenLeite`.
-/
