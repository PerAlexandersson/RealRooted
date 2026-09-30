import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.MultiplierSequence.Laguerre
import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIReverse
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeISigned
import RealRooted.MultiplierSequence.Sign

/-!
# Multiplier sequence challenge entry point

<!-- realrooted-catalog
version = 1
section = "concepts"
slug = "multiplier-sequences"
authors = ["Pólya", "Schur"]
years = [1914]

[[definitions]]
name = "RealRooted.diagonalOperator"
module = "RealRooted.MultiplierSequence"

[[definitions]]
name = "RealRooted.jensenPolynomial"
module = "RealRooted.MultiplierSequence"

[[definitions]]
name = "RealRooted.IsFiniteMultiplierSequence"
module = "RealRooted.MultiplierSequence"

[[definitions]]
name = "RealRooted.IsMultiplierSequence"
module = "RealRooted.MultiplierSequence.Infinite"

[[definitions]]
name = "RealRooted.IsPFMultiplierSequence"
module = "RealRooted.MultiplierSequence.Infinite"

[[definitions]]
name = "RealRooted.IsLaguerrePolyaTypeI"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI"

[[theorems]]
name = "RealRooted.isMultiplierSequence_iff_jensenPolynomial_isPF"
module = "RealRooted.MultiplierSequence.PolyaSchur"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_iff_isLaguerrePolyaTypeI_complexExpGeneratingFunction"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIReverse"

[[theorems]]
name = "RealRooted.isMultiplierSequence_iff_isLaguerrePolyaTypeISigned_complexExpGeneratingFunction"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeISigned"

[[theorems]]
name = "RealRooted.IsMultiplierSequence.exists_pf_sign_normalization"
module = "RealRooted.MultiplierSequence.Sign"

[[theorems]]
name = "RealRooted.IsPFMultiplierSequence.logConcave"
module = "RealRooted.MultiplierSequence.PolyaSchur"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_inv_ascPochhammer"
module = "RealRooted.MultiplierSequence.InvPochhammer"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_inv_factorial"
module = "RealRooted.MultiplierSequence.InvPochhammer"

[[theorems]]
name = "RealRooted.isMultiplierSequence_eval_of_roots_nonpos"
module = "RealRooted.MultiplierSequence.Laguerre"

[[theorems]]
name = "RealRooted.isPFMultiplierSequence_natCast_add"
module = "RealRooted.MultiplierSequence.Laguerre"
-->

<!-- realrooted-catalog-content -->
# Multiplier sequences

A real sequence `γ = (γ_0, γ_1, …)` is a **multiplier sequence** if the
diagonal operator

```text
a_0 + a_1 x + ⋯ + a_n x^n  ↦  γ_0 a_0 + γ_1 a_1 x + ⋯ + γ_n a_n x^n
```

sends every real-rooted polynomial to a real-rooted polynomial (or zero). It is
a **PF multiplier sequence** if it preserves real-rootedness with nonnegative
coefficients. The finite version restricts to inputs of degree at most `n`.

The following are formalized:

- **Jensen polynomials** (Pólya–Schur): a nonnegative sequence is a multiplier
  sequence if and only if every Jensen polynomial
  `g_n(x) = sum_k choose(n,k) γ_k x^k` has only real nonpositive zeros.
- **Laguerre–Pólya classification** (Pólya–Schur): under a growth condition,
  `γ` is a PF multiplier sequence if and only if its exponential generating
  function `sum_k γ_k z^k / k!` is a locally uniform limit of PF polynomials,
  that is, lies in the Laguerre–Pólya class of type I. Without the sign
  condition, `γ` is a multiplier sequence if and only if one of `±f(±z)` is of
  type I, where `f` is the generating function; equivalently, one of `±γ_k`
  and `±(-1)^k γ_k` is a PF multiplier sequence.
- **Log-concavity:** PF multiplier sequences are log-concave.
- **Laguerre's theorem:** if a polynomial `φ` has only real nonpositive
  zeros, then `φ(0), φ(1), φ(2), …` is a multiplier sequence. It is a PF
  multiplier sequence when the leading coefficient is nonnegative. The basic
  case `k + r`, for real `r ≥ 0`, has Jensen polynomials
  `(1 + x)^(n-1) ((n + r) x + r)`.
- **Examples:** for real `α > 0`, the reciprocal rising factorials
  `1 / (α)_k` form a PF multiplier sequence, and so in particular do `1 / k!`.
  After clearing denominators, their Jensen polynomials are generalized
  Laguerre polynomials.

## References

G. Pólya and J. Schur, “Über zwei Arten von Faktorenfolgen in der Theorie der
algebraischen Gleichungen,” *J. Reine Angew. Math.* 144 (1914), 89–113.
The finite Pólya–Schur theorem through the Schur–Szegő composition is on the
[Hadamard products page](/RealRooted/theorems/hadamard-products/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.MultiplierSequence`.
-/
