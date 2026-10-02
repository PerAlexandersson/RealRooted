import RealRooted.BinaryRunTransformation.Continuation
import RealRooted.BinaryRunTransformation.MultiplierMotzkin

/-!
# Binary-run transformation challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "binary-run-transformation"

[[definitions]]
name = "RealRooted.binaryRunPolynomial"
module = "RealRooted.BinaryRunTransformation.Coefficients"
label = "Binary-run basis polynomials"

[[definitions]]
name = "RealRooted.binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Coefficients"
label = "Binary-run transformation"

[[theorems]]
name = "RealRooted.Challenges.BinaryRunTransformation.preservesPF"
label = "The transformation preserves PF polynomials"

[[theorems]]
name = "RealRooted.Challenges.BinaryRunTransformation.preservesStrictlyNegativeRoots"
label = "Positive constant term gives strictly negative zeros"

[[theorems]]
name = "RealRooted.strictInterl_binaryRunTransform"
module = "RealRooted.BinaryRunTransformation.Interlacing"
label = "The transformation preserves interlacing"

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
label = "Motzkin-ascent polynomials (A114580) form a Sturm chain"
-->

<!-- realrooted-catalog-content -->
# The binary-run transformation

For fixed $n$, the linear map `binaryRunTransform n` sends $1$ to $1$ and
sends $X^m$, for $1 \leq m \leq n$, to

$$\frac{1}{\binom{n}{m}} \sum_k \binom{m-1}{k-1}\binom{n+1-m}{k} X^k.$$

If the input has degree at most $n$, nonnegative coefficients, and only real
nonpositive zeros, then its image has the same properties. If the input has
positive constant coefficient, every zero of the image is strictly negative.

The fixed-sum Narayana-type transform is the reweighted version with basis
images

$$T_n(X^m) = \frac{\binom{n}{m}}{m+1}\, \mathtt{binaryRunPolynomial}\ n\ m.$$

Equivalently, it is `binaryRunTransform n` after the standard finite
Narayana/Schur–Szegő diagonal multiplier. Thus this preservation theorem,
together with preservation by that multiplier, gives the corresponding
[Narayana transformation theorem](/RealRooted/families/narayana/).

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
$\alpha = 2$, where $\gamma_m = 1/(m+1)!$, gives the Motzkin-ascent polynomials (OEIS A114580).

The rows also move monotonically in $\alpha$. Write $P_n^{(\alpha)}$ for the row with
$\gamma_m = 1/(\alpha)_m$. Then $P_n^{(\alpha+1)} \ll P_n^{(\alpha)}$ for every $n$ and every
$\alpha > 0$. The proof uses the shift identity
$\alpha\, G_n^{(\alpha)} = (\Theta + \alpha)\, G_n^{(\alpha+1)}$, which follows from
$\alpha\, (\alpha+1)_m = (\alpha+m)(\alpha)_m$. A PF polynomial $g$ of degree at least 2 satisfies
$g \ll (\Theta + \alpha)\, g$, and the transform preserves interlacing.

## Proof idea

After scaling the input factors, a stable pointing construction controls the
motion of every critical value of the output. A polarized path-matching
polynomial supplies the small-parameter anchor, and the critical-value sign
prevents collisions throughout the deformation.

## References

The stability-preserving contraction uses the algebraic-symbol machinery of
J. Borcea and P. Brändén, [“The Lee–Yang and Pólya–Schur programs. I. Linear
operators preserving stability,”](https://arxiv.org/abs/0809.0401)
*Inventiones Mathematicae* 177 (2009), 541–569. For the related transform, see
J. Mao and L. Wang, [“The Narayana transformation,”](https://arxiv.org/abs/2607.01572)
arXiv:2607.01572 (2026).
<!-- /realrooted-catalog-content -->

This module exposes the checked preservation theorem and its strictly negative
root corollary. The stability, contraction, anchor, and continuation arguments
remain in `RealRooted.BinaryRunTransformation`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace BinaryRunTransformation

/-- The normalized binary-run transformation preserves PF polynomials in its
finite degree box. -/
theorem preservesPF {n : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (binaryRunTransform n p) :=
  hp.binaryRunTransform hpdeg

private theorem constantCoeff {n : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ n) :
    (binaryRunTransform n p).coeff 0 = p.coeff 0 := by
  have hbasis (m : ℕ) :
      (binaryRunPolynomial n m).coeff 0 = if m = 0 then 1 else 0 := by
    by_cases hm : m = 0
    · simp [hm]
    · simp only [binaryRunPolynomial, hm, ite_false]
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Polynomial.coeff_monomial]
      have hk0 : k ≠ 0 := by
        have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        lia
      simp [hk0]
  rw [coeff_binaryRunTransform_eq_sum_range hpdeg]
  simp_rw [hbasis]
  simp

/-- A positive constant coefficient upgrades the output root bound from
nonpositive to strictly negative. -/
theorem preservesStrictlyNegativeRoots {n : ℕ} {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ n)
    (hconst : 0 < p.coeff 0) :
    (binaryRunTransform n p).Splits ∧
      ∀ r ∈ (binaryRunTransform n p).roots, r < 0 := by
  have hq := preservesPF hp hpdeg
  have hq0 : binaryRunTransform n p ≠ 0 := by
    intro hzero
    have hcoeff : (binaryRunTransform n p).coeff 0 = 0 := by simp [hzero]
    rw [constantCoeff hpdeg] at hcoeff
    linarith
  refine ⟨(hq.ne_zero_and_splits hq0).2, ?_⟩
  intro r hr
  have hrle : r ≤ 0 := hq.roots_nonpos r hr
  have hrne : r ≠ 0 := by
    intro hrzero
    subst r
    have hroot : (binaryRunTransform n p).IsRoot 0 :=
      (Polynomial.mem_roots hq0).mp hr
    have heval : (binaryRunTransform n p).eval 0 = 0 := hroot
    rw [← Polynomial.coeff_zero_eq_eval_zero, constantCoeff hpdeg] at heval
    linarith
  exact lt_of_le_of_ne hrle hrne

end BinaryRunTransformation
end Challenges
end RealRooted
