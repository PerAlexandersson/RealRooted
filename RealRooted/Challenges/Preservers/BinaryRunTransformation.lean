module

public import RealRooted.BalancedRunTransformation.Interlacing
public import RealRooted.BalancedRunTransformation.Preservation
public import RealRooted.BinaryRunTransformation.Continuation
public import RealRooted.BinaryRunTransformation.MultiplierMotzkin
public import RealRooted.BinaryRunTransformation.SymbolCounterexample

/-!
# Binary-run transformation challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "binary-run-transformation"
formalized = "2026-09-28"
references = [
  "BorceaBranden2009I",
  "MaoWang2026x",
]

[[definitions]]
name = "RealRooted.binaryRunPolynomial"
module = "RealRooted.BinaryRunTransformation.Coefficients"
label = "Binary-run basis polynomials"

[[definitions]]
name = "RealRooted.binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Coefficients"
label = "Binary-run transformation"

[[definitions]]
name = "RealRooted.motzkinWeightedRow"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "Multiplier-weighted Motzkin rows"

[[definitions]]
name = "RealRooted.balancedRunTransform"
module = "RealRooted.BalancedRunTransformation"
label = "Balanced run transformation"

[[theorems]]
name = "RealRooted.IsPFPolynomial.binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Continuation"
label = "The transformation preserves PF polynomials"
headline = true

[[theorems]]
name = "RealRooted.binaryRunTransform_splits_and_roots_neg"
module = "RealRooted.BinaryRunTransformation.Continuation"
label = "Positive constant term gives strictly negative zeros"

[[theorems]]
name = "RealRooted.strictInterl_binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Interlacing"
label = "The transformation preserves interlacing"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_binaryRunTransform_succ"
module = "RealRooted.BinaryRunTransformation.CrossLength"
label = "Interlacing across lengths"

[[theorems]]
name = "RealRooted.motzkinWeightedRow_strictInterl_succ"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "Weighted Motzkin rows form a Sturm chain"

[[theorems]]
name = "RealRooted.motzkinWeightedRow_inv_ascPochhammer_strictInterl_succ"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "The Sturm chain for γ_m = 1/(α)_m"

[[theorems]]
name = "RealRooted.motzkinWeightedRow_inv_ascPochhammer_succ_strictInterl"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "Monotonicity in α"

[[theorems]]
name = "RealRooted.motzkinAscentRow_strictInterl_succ"
module = "RealRooted.BinaryRunTransformation.MultiplierMotzkin"
label = "The rows with weights 1/(m+1)! form a Sturm chain"

[[theorems]]
name = "RealRooted.IsPFPolynomial.balancedRunTransform"
module = "RealRooted.BalancedRunTransformation.Preservation"
label = "The balanced transformation preserves PF polynomials"

[[theorems]]
name = "RealRooted.strictInterl_balancedRunTransform"
module = "RealRooted.BalancedRunTransformation.Interlacing"
label = "The balanced transformation preserves interlacing"
-->

<!-- realrooted-catalog-content -->
# The binary-run transformation

For fixed $n$, the linear map `binaryRunTransform n` sends $1$ to $1$ and
sends $X^m$, for $1 \leq m \leq n$, to

$$\frac{1}{\binom{n}{m}} \sum_k \binom{m-1}{k-1}\binom{n+1-m}{k} X^k.$$

By the algebraic-symbol method [@BorceaBranden2009I], if the input has degree
at most $n$, nonnegative coefficients, and only real
nonpositive zeros, then its image has the same properties. If the input has
positive constant coefficient, every zero of the image is strictly negative.

The fixed-sum Narayana-type transform is the reweighted version with basis
images

$$T_n(X^m) = \frac{\binom{n}{m}}{m+1}\, \mathtt{binaryRunPolynomial}\ n\ m.$$

Equivalently, it is `binaryRunTransform n` after the standard finite
Narayana/Schur–Szegő diagonal multiplier. Combined with preservation by that
multiplier, this preservation theorem yields the corresponding
[Narayana transformation theorem](/RealRooted/families/narayana/)
[@MaoWang2026x]; that
deduction is cited, and Lean does not connect `binaryRunTransform` to
`narayanaTransform`.

## Interlacing

On inputs of degree at most $(n+1)/2$, the transform also preserves
interlacing. With $N = n + 1$ and $\Theta = x\, d/dx$, it transports interlacing
across lengths: for a PF polynomial $g$ with $g(0) \neq 0$ and
$2 \leq \deg g \leq N/2$,

$$J_n\bigl((N - 2\Theta)\, g\bigr) \ll J_{n+1}(g).$$

For a PF multiplier sequence $\gamma$ with positive entries, put
$G_n^{\gamma}(t) = \sum_m \frac{n!\,\gamma_m}{m!\,(n-2m)!}\, t^m$, a weighted matching polynomial of
the complete graph. These satisfy $(N-2\Theta)\, G_N^{\gamma} = N G_n^{\gamma}$, so the rows
$R_n^{\gamma} = J_n(G_n^{\gamma})$ form a Sturm chain: $R_n^{\gamma} \ll R_{n+1}^{\gamma}$ for all
$n$. This holds in particular for $\gamma_m = 1/(\alpha)_m$ with $\alpha > 0$. The case
$\alpha = 2$, where $\gamma_m = 1/(m+1)!$, gives rows that are classically the Motzkin-ascent
polynomials (OEIS A114580); that identification is cited, not formalized.

The rows also move monotonically in $\alpha$. Write $P_n^{(\alpha)}$ for the row with
$\gamma_m = 1/(\alpha)_m$. Then $P_n^{(\alpha+1)} \ll P_n^{(\alpha)}$ for every $n$ and every
$\alpha > 0$. The proof uses the shift identity
$\alpha\, G_n^{(\alpha)} = (\Theta + \alpha)\, G_n^{(\alpha+1)}$, which follows from
$\alpha\, (\alpha+1)_m = (\alpha+m)(\alpha)_m$. A PF polynomial $g$ of degree at least 2 satisfies
$g \ll (\Theta + \alpha)\, g$, and the transform preserves interlacing.

## The balanced run transformation

The companion map `balancedRunTransform n` sends $X^m$ to
$$
U_{n,m} = \frac{1}{\binom{n}{m}} \sum_k \binom{m}{k}\binom{n-m}{k} X^k .
$$
Let $n \ge 2$. If $p$ is a PF polynomial of degree at most $(n+1)/2$, then its
image is a PF polynomial. If $f \ll g$, both have nonnegative coefficients,
and $\deg g \le (n+1)/2$, then the images satisfy the same interlacing.

## Proof idea

After scaling the input factors, a stable pointing construction controls the
motion of every critical value of the output. A polarized path-matching
polynomial supplies the small-parameter anchor, and the critical-value sign
prevents collisions throughout the deformation.

## References

The stability-preserving contraction uses the algebraic-symbol machinery
[@BorceaBranden2009I]. For the related Narayana transform, see [@MaoWang2026x].
<!-- /realrooted-catalog-content -->

This module exposes the strictly negative root corollary of the checked
preservation theorem `RealRooted.IsPFPolynomial.binaryRunTransform`. The
stability, contraction, anchor, and continuation arguments remain in
`RealRooted.BinaryRunTransformation`.
-/

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace BinaryRunTransformation

end BinaryRunTransformation
end Challenges
end RealRooted
