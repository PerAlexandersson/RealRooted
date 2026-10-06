import RealRooted.Transforms.BrandenE
import RealRooted.Transforms.BrandenE.IntervalPreserver

/-!
# Brändén E transform challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "branden-e-transform"
authors = ["Brändén"]
years = [2006]

[[definitions]]
name = "RealRooted.brandenE"
module = "RealRooted.Transforms.BrandenE.Basic"
label = "The E transform x^n ↦ ordered Bell polynomial"

[[definitions]]
name = "RealRooted.brandenBasisImage"
module = "RealRooted.Transforms.BrandenE.BasisImage"
label = "Images E(x^k (x + 1)^(n − k))"

[[theorems]]
name = "RealRooted.brandenE_isPFPolynomial_of_roots_mem_Icc"
module = "RealRooted.Transforms.BrandenE.IntervalPreserver"
label = "Roots in [−1, 0] give a PF image"
headline = true

[[theorems]]
name = "RealRooted.brandenE_eq_zero_or_splits_and_roots_nonpos"
module = "RealRooted.Transforms.BrandenE.IntervalPreserver"
label = "Roots in [−1, 0] give a real-rooted image, for either sign"

[[theorems]]
name = "RealRooted.brandenBasisImage_strictInterl"
module = "RealRooted.Transforms.BrandenE.ProperPosition"
label = "The images of the binomial basis form an interlacing sequence"
headline = true

[[theorems]]
name = "RealRooted.orderedBellPolynomial_isPFPolynomial"
module = "RealRooted.Transforms.BrandenE.ProperPosition"
label = "Ordered Bell polynomials are PF polynomials"

[[theorems]]
name = "RealRooted.Challenges.BrandenETransform.brandenE_descPochhammer"
label = "E sends x(x − 1)⋯(x − n + 1) to n! xⁿ"
-->

<!-- realrooted-catalog-content -->
# Brändén’s E transform

The ordered Bell polynomials are defined by
$$
F_0(x) = 1, \qquad F_{n+1}(x) = x F_n(x) + x(1 + x) F_n'(x),
$$
so that $F_n(x) = \sum_k k!\, S(n, k)\, x^k$, where $S(n, k)$ are the Stirling
numbers of the second kind. The **E transform** is the linear map with
$E(x^n) = F_n(x)$. Equivalently,
$E\bigl(x(x - 1) \cdots (x - n + 1)\bigr) = n!\, x^n$, that is,
$E\binom{x}{n} = x^n$.

**Theorem (Brändén).** Let $p$ be a real polynomial whose roots are all real
and lie in $[-1, 0]$.

- If $p$ has positive leading coefficient, then $E(p)$ is a PF polynomial: it
  has nonnegative coefficients and only real, nonpositive roots.
- Without a sign condition, $E(p)$ is either zero, or nonzero and real-rooted
  with only nonpositive roots.

**Interlacing basis.** For $0 \le k \le n$ let
$b_{n,k} = E\bigl(x^k (x + 1)^{n-k}\bigr)$. Then $b_{n,i} \ll b_{n,j}$ for all
$i \le j \le n$. In particular every ordered Bell polynomial
$F_n = b_{n,n}$ is a PF polynomial.

## Proof idea

The polynomials $x^k (x + 1)^{n - k}$ form a basis of the polynomials of degree
at most $n$, and a polynomial with all roots in $[-1, 0]$ has nonnegative
coordinates in it. Each image $b_{n,k}$ is obtained from a lower-degree one by
an Euler differential step $(x + r) f + x(1 + x) f'$, which preserves
interlacing. The images thus form an interlacing sequence, and a nonnegative
combination of an interlacing sequence is real-rooted.

## References

P. Brändén, “On linear transformations preserving the Pólya frequency
property,” *Transactions of the American Mathematical Society* 358 (2006),
3697–3716.
The ordered Bell numbers are [OEIS A000670](https://oeis.org/A000670).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Transforms.BrandenE`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace BrandenETransform

/-- The `E` transform sends the descending Pochhammer polynomial
`X (X - 1) ⋯ (X - n + 1)` to `n! X ^ n`. -/
theorem brandenE_descPochhammer {R : Type*} [CommRing R] (n : ℕ) :
    brandenE (descPochhammer R n) = C (n.factorial : R) * X ^ n :=
  RealRooted.brandenE_descPochhammer n

end BrandenETransform
end Challenges
end RealRooted
