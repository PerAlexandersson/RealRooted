import RealRooted.FiniteFreeAdditive.HalfIntegerPreservation
import RealRooted.FiniteFreeAdditive.Preservation
import RealRooted.FiniteFreeMultiplicative
import RealRooted.Hadamard.Grace
import RealRooted.NarayanaTransformation.Rectangular.Preservation
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Finite free convolutions challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "finite-free-convolutions"
authors = ["Marcus", "Spielman", "Srivastava", "Gribinski"]
years = [2022]

[[definitions]]
name = "RealRooted.finiteFreeAdditiveConvolution"
module = "RealRooted.FiniteFreeAdditive"
label = "Finite free additive convolution"

[[definitions]]
name = "RealRooted.rectangularAdditiveConvolution"
module = "RealRooted.RectangularConvolution"
label = "Rectangular additive convolution"

[[definitions]]
name = "RealRooted.generalizedRectangularAdditiveConvolution"
module = "RealRooted.FiniteFreeAdditive.HalfIntegerConvolution"
label = "Rectangular additive convolution with a real parameter"

[[definitions]]
name = "RealRooted.finiteFreeMultiplicativeConvolution"
module = "RealRooted.FiniteFreeMultiplicative"
label = "Finite free multiplicative convolution"

[[definitions]]
name = "RealRooted.signedReciprocal"
module = "RealRooted.FiniteFreeMultiplicative"
label = "Signed reciprocal x^d p(-1/x)"

[[definitions]]
name = "RealRooted.HasOnlyNonnegRoots"
module = "RealRooted.NarayanaTransformation.RootGeometry"
label = "Zero, or real-rooted with nonnegative roots"

[[theorems]]
name = "RealRooted.splits_finiteFreeAdditiveConvolution"
module = "RealRooted.FiniteFreeAdditive.Preservation"
label = "Marcus–Spielman–Srivastava: ⊞_d preserves real-rootedness"
headline = true

[[theorems]]
name = """RealRooted.Challenges.FiniteFreeConvolutions.\
hasOnlyNonnegRoots_rectangularAdditiveConvolution"""
label = "Gribinski–Marcus: the rectangular convolution preserves nonnegative roots"
headline = true

[[theorems]]
name = "RealRooted.Challenges.FiniteFreeConvolutions.splits_and_roots_nonneg_rectangular_neg_half"
label = "The parameter −1/2 preserves nonnegative roots"

[[theorems]]
name = "RealRooted.Challenges.FiniteFreeConvolutions.splits_and_roots_nonneg_rectangular_pos_half"
label = "The parameter 1/2 preserves nonnegative roots"

[[theorems]]
name = "RealRooted.Challenges.FiniteFreeConvolutions.splits_finiteFreeMultiplicativeConvolution"
label = "Marcus–Spielman–Srivastava: ⊠_d preserves real-rootedness"
headline = true

[[theorems]]
name = "RealRooted.signedReciprocal_schurSzegoComp"
module = "RealRooted.FiniteFreeMultiplicative"
label = "The signed reciprocal turns Schur–Szegő composition into ⊠_d"
-->

<!-- realrooted-catalog-content -->
# Finite free convolutions

Write $p(x) = \sum_{i=0}^{d} a_i x^{d-i}$ and $q(x) = \sum_{j=0}^{d} b_j x^{d-j}$
in a degree box of size $d$. The **finite free additive convolution** is
$$
(p \boxplus_d q)(x) = \sum_{k=0}^{d} x^{d-k} \sum_{i + j = k}
  \frac{(d - i)!\,(d - j)!}{d!\,(d - k)!}\, a_i b_j .
$$
The **rectangular additive convolution** $p \boxplus_{m,n} q$ in a degree box of
size $n$ multiplies each term by the second factor
$\frac{(n + m - i)!\,(n + m - j)!}{(n + m)!\,(n + m - k)!}$. More generally, for
real $\alpha$ the term weight is
$$
\frac{(n)^{\underline{k}}}{(n)^{\underline{i}}\,(n)^{\underline{j}}}
\cdot \frac{(n + \alpha)^{\underline{k}}}
  {(n + \alpha)^{\underline{i}}\,(n + \alpha)^{\underline{j}}},
$$
with falling factorials $(x)^{\underline{k}}$; $\alpha = m$ is the rectangular
case. The **finite free multiplicative convolution** is
$$
(p \boxtimes_d q)(x) = \sum_{k=0}^{d} (-1)^{k} \binom{d}{k}^{-1}
  a_k b_k\, x^{d-k}
$$
in the same box, that is, $(-1)^d\, (p *_d q)(-x)$ for the Schur–Szegő
composition $p *_d q = \sum_k \binom{d}{k}^{-1} p_k q_k x^k$ of the coefficient
lists $p_k$, $q_k$.

**Theorem.**

- If $p$ and $q$ are real-rooted of degree at most $d$, then $p \boxplus_d q$ is
  real-rooted (Marcus, Spielman, Srivastava).
- If $f$ and $g$ have degree exactly $n$, positive leading coefficients, and
  only nonnegative real roots, then $f \boxplus_{m,n} g$ is zero or has only
  nonnegative real roots (Gribinski, Marcus).
- The same holds for the parameters $\alpha = -\tfrac12$ and
  $\alpha = \tfrac12$, for inputs of degree at most $n$ that are real-rooted with
  nonnegative roots.
- If $p$ is real-rooted, $q$ is real-rooted with nonnegative roots, and both
  have degree at most $d$, then $p \boxtimes_d q$ is real-rooted
  (Marcus, Spielman, Srivastava).
- The signed reciprocal $p \mapsto x^d\, p(-1/x)$ carries Schur–Szegő
  composition to multiplicative convolution:
  $\widehat{p *_d q} = \widehat{p} \boxtimes_d \widehat{q}$.

## Proof idea

The additive theorem follows from the Lieb–Sokal lemma: the convolution is a
differential operator in $q$ applied to $p$, and real stability is preserved.
The half-integer cases reduce to $\boxplus_{2n}$ and $\boxplus_{2n+1}$ through
the even and odd lifts $p(x^2)$ and $x\,p(x^2)$. The rectangular case uses a
real-stable lift of $f(xy)$. For the multiplicative theorem, substituting
$-x$ in $q$ turns $q$ into a PF polynomial up to sign, and the Schur–Szegő
composition theorem on the Hadamard page applies.

## References

A. W. Marcus, D. A. Spielman, and N. Srivastava, “Finite free convolutions of
polynomials,” *Probability Theory and Related Fields* 182 (2022), 807–848;
A. Gribinski and A. W. Marcus, [“A rectangular additive convolution for
polynomials,”](https://doi.org/10.5070/C62156888) *Combinatorial Theory* 2(1)
(2022), #16.
For the application to the Narayana transformation, see
[symmetricfunctions.com][mao-wang].

[mao-wang]: https://www.symmetricfunctions.com/realRooted.htm#thm:narayanaTransformationMaoWang
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.FiniteFreeAdditive`, `RealRooted.RectangularConvolution`,
`RealRooted.NarayanaTransformation.Rectangular` and
`RealRooted.FiniteFreeMultiplicative`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace FiniteFreeConvolutions

/-- **Gribinski–Marcus.** The rectangular additive convolution of two
polynomials of degree `n` with positive leading coefficients and only
nonnegative roots has only nonnegative roots. -/
theorem hasOnlyNonnegRoots_rectangularAdditiveConvolution {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf : HasOnlyNonnegRoots f) (hg : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m n f g) :=
  rectangularAdditiveConvolutionPreservesNonnegRoots hfdeg hgdeg hf_pos hg_pos hf hg

/-- The generalized rectangular convolution with parameter `-1 / 2` preserves
real-rootedness with nonnegative roots in degree at most `n`. -/
theorem splits_and_roots_nonneg_rectangular_neg_half (n : ℕ) (p q : ℝ[X])
    (hp : p.Splits) (hq : q.Splits)
    (hproots : ∀ r ∈ p.roots, 0 ≤ r) (hqroots : ∀ r ∈ q.roots, 0 ≤ r)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n) :
    (generalizedRectangularAdditiveConvolution (-(1 / 2 : ℝ)) n p q).Splits ∧
      ∀ r ∈ (generalizedRectangularAdditiveConvolution (-(1 / 2 : ℝ)) n p q).roots,
        0 ≤ r :=
  splits_and_forall_roots_nonneg_generalizedRectangularAdditiveConvolution_neg_half n p q
    hp hq hproots hqroots hpdeg hqdeg

/-- The generalized rectangular convolution with parameter `1 / 2` preserves
real-rootedness with nonnegative roots in degree at most `n`. -/
theorem splits_and_roots_nonneg_rectangular_pos_half (n : ℕ) (p q : ℝ[X])
    (hp : p.Splits) (hq : q.Splits)
    (hproots : ∀ r ∈ p.roots, 0 ≤ r) (hqroots : ∀ r ∈ q.roots, 0 ≤ r)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n) :
    (generalizedRectangularAdditiveConvolution (1 / 2 : ℝ) n p q).Splits ∧
      ∀ r ∈ (generalizedRectangularAdditiveConvolution (1 / 2 : ℝ) n p q).roots,
        0 ≤ r :=
  splits_and_forall_roots_nonneg_generalizedRectangularAdditiveConvolution_pos_half n p q
    hp hq hproots hqroots hpdeg hqdeg

/-- **Marcus–Spielman–Srivastava, multiplicative case.** If `p` is
real-rooted, `q` is real-rooted with nonnegative roots, and both have degree at
most `d`, then their finite free multiplicative convolution is real-rooted. -/
theorem splits_finiteFreeMultiplicativeConvolution {d : ℕ} {p q : ℝ[X]}
    (hp : p.Splits) (hpdeg : p.natDegree ≤ d) (hq : q.Splits) (hqdeg : q.natDegree ≤ d)
    (hq_roots : ∀ r ∈ q.roots, 0 ≤ r) :
    (finiteFreeMultiplicativeConvolution d p q).Splits := by
  set q' := q.comp (-X) with hq'
  have hcoeff (k : ℕ) : q'.coeff k = q.coeff k * (-1 : ℝ) ^ k := by
    simpa [q'] using Polynomial.comp_C_mul_X_coeff (p := q) (r := (-1 : ℝ)) (n := k)
  have hconv : finiteFreeMultiplicativeConvolution d p q =
      C ((-1 : ℝ) ^ d) * schurSzegoComp d q' p := by
    rw [finiteFreeMultiplicativeConvolution]
    congr 1
    ext k
    have h := Polynomial.comp_C_mul_X_coeff (p := schurSzegoComp d p q) (r := (-1 : ℝ)) (n := k)
    simp only [map_neg, map_one, neg_mul, one_mul] at h
    rw [h, coeff_schurSzegoComp, coeff_schurSzegoComp, hcoeff]
    split_ifs <;> ring
  rw [hconv]
  refine Splits.C_mul ?_ _
  by_cases hq0 : q' = 0
  · simp [hq0, schurSzegoComp]
  have hlc : q'.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
  set f := C q'.leadingCoeff⁻¹ * q' with hf
  have hq'f : q' = C q'.leadingCoeff * f := by
    rw [hf, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
  have hfsplit : f.Splits := hq.comp_neg_X.C_mul _
  have hfpos : HasPosLeadingCoeff f := by
    change 0 < f.leadingCoeff
    rw [hf, leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc)),
      inv_mul_cancel₀ hlc]
    exact one_pos
  have hfroots : ∀ r ∈ f.roots, r ≤ 0 := by
    intro r hr
    rw [hf, roots_C_mul _ (inv_ne_zero hlc), hq', roots_comp_neg_X] at hr
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hr
    linarith [hq_roots s hs]
  have hfpf : IsPFPolynomial f :=
    IsPFPolynomial.of_realRooted_nonneg
      ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hfsplit).mpr
        ⟨hfpos, hfroots⟩).1 hfsplit
  have hfdeg : f.natDegree ≤ d := by
    rw [hf, natDegree_C_mul (inv_ne_zero hlc), hq', natDegree_comp]
    simpa using hqdeg
  rw [hq'f, schurSzegoComp_C_mul_left]
  refine Splits.C_mul ?_ _
  rcases finiteSchurSzegoComposition hfpf hfdeg hpdeg hp with h | h
  · rw [h]
    exact Splits.zero
  · exact h

end FiniteFreeConvolutions
end Challenges
end RealRooted
