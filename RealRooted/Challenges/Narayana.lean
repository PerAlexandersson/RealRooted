import RealRooted.CombinatorialExamples.DyckNarayana
import RealRooted.MaoWangMatrixProduct
import RealRooted.NarayanaTransformation.Endpoints
import RealRooted.NarayanaTransformation.Falling
import RealRooted.NarayanaTransformation.Rising

/-!
# Narayana polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "narayana"
authors = ["Mao", "Wang", "Dominici", "Johnston", "Jordaan", "Brenti"]
years = [1989, 2013, 2026]

[[definitions]]
name = "RealRooted.narayanaPolynomial"
module = "RealRooted.NarayanaTransformation.Coefficients"
label = "Generalized Narayana polynomials"

[[definitions]]
name = "RealRooted.narayanaTransform"
module = "RealRooted.NarayanaTransformation.Coefficients"
label = "Narayana transform"

[[definitions]]
name = "RealRooted.HasOnlyNonposRoots"
module = "RealRooted.NarayanaTransformation.RootGeometry"
label = "Zero, or real-rooted with nonpositive zeros"

[[definitions]]
name = "Polynomial.basisTransform"
module = "RealRooted.Mathlib.Algebra.Polynomial.BasisTransform"
label = "The linear map sending x^n to B_n"

[[definitions]]
name = "RealRooted.fallingFactorialPolynomial"
module = "RealRooted.NarayanaTransformation.Basis"
label = "Falling factorials"

[[definitions]]
name = "RealRooted.risingFactorialPolynomial"
module = "RealRooted.NarayanaTransformation.Basis"
label = "Generalized rising factorials"

[[definitions]]
name = "RealRooted.LowerTriangularMatrix.RowGeneratingFunctionsPF"
module = "RealRooted.LowerTriangularMatrix"
label = "Every row-generating polynomial is Pólya-frequency"

[[definitions]]
name = "RealRooted.LowerTriangularMatrix.MaoWangAdmissibleMatrix"
module = "RealRooted.MaoWangMatrixProduct"
label = "The Mao–Wang one-step factors"

[[theorems]]
name = "RealRooted.splits_narayanaPolynomial"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "Generalized Narayana polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.narayanaPolynomialRootLocation"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "Generalized Narayana polynomials are Pólya-frequency"

[[theorems]]
name = "RealRooted.narayanaTransformPreservesPF"
module = "RealRooted.NarayanaTransformation.Endpoints"
label = "The Narayana transform preserves Pólya-frequency polynomials"
headline = true

[[theorems]]
name = "RealRooted.Challenges.Narayana.HasOnlyNonposRoots.of_basisTransform_fallingFactorial"
label = "Brenti: nonpositive zeros in the falling-factorial basis pull back"
headline = true

[[theorems]]
name = "RealRooted.Challenges.Narayana.isPFPolynomial_basisTransform_touchard"
label = "The Touchard transform preserves Pólya-frequency polynomials"

[[theorems]]
name = "RealRooted.Challenges.Narayana.isPFPolynomial_basisTransform_risingFactorial"
label = "Rising-factorial transforms preserve Pólya-frequency polynomials"

[[theorems]]
name = "RealRooted.Challenges.Narayana.rowGeneratingFunctionsPF_mul_listProduct"
label = "Mao–Wang: products with admissible factors keep Pólya-frequency rows"
headline = true

[[theorems]]
name = "RealRooted.Challenges.Narayana.rowGeneratingFunctionsPF_mul_pow"
label = "Mao–Wang: powers of an admissible factor keep Pólya-frequency rows"

[[theorems]]
name = "DyckWord.card_semilength_peakCount"
module = "RealRooted.Mathlib.Combinatorics.Enumerative.DyckStatistics"
label = "Dyck paths of semilength n with k peaks are counted by Narayana numbers"

[[theorems]]
name = "DyckWord.peakGeneratingPolynomial_eq_narayanaPolynomial"
module = "RealRooted.CombinatorialExamples.DyckNarayana"
label = "The peak polynomial of Dyck paths is x N_{n,1}(x)"
-->

<!-- realrooted-catalog-content -->
# Generalized Narayana polynomials and basis transforms

For $m, n \geq 0$, the generalized Narayana polynomial is

$$N_{n,m}(x) = \sum_{k=0}^{n} \frac{\binom{n}{k}\binom{n+m}{k}}{\binom{m+k}{k}}\, x^k.$$

For $m = 1$ the coefficients are Narayana numbers; for example
$N_{2,1}(x) = 1 + 3x + x^2$. Combinatorially, the Dyck paths of semilength
$n + 1$ counted by peaks have generating polynomial $x\, N_{n,1}(x)$; this is
formalized. These polynomials are Pólya-frequency, and the Narayana transform
$x^n \mapsto N_{n,m}(x)$ preserves Pólya-frequency polynomials. Here a
polynomial is Pólya-frequency (`IsPFPolynomial`) if it has nonnegative
coefficients and is either zero or real-rooted with nonpositive zeros.

## Basis transforms

For a sequence of polynomials $B_0, B_1, \dotsc$, the basis transform
$T_B$ (`basisTransform B`) is the linear map with $T_B(x^n) = B_n(x)$. We
say that $p$ has only nonpositive zeros (`HasOnlyNonposRoots p`) if $p = 0$ or
$p$ is real-rooted with all zeros $\leq 0$. Write
$$
\langle x\rangle_k = x(x-1)\dotsm(x-k+1), \qquad
(x \mid \mu)_k = x(x+\mu)\dotsm(x+(k-1)\mu),
$$
for the falling factorials and the generalized rising factorials, and $T_n(x)$
for the Touchard polynomials, $T_0 = 1$ and $T_{n+1} = x T_n + x T_n'$.

**Theorem (Brenti).** If
$\sum_k a_k \langle x\rangle_k$ has only nonpositive zeros, then so does
$\sum_k a_k x^k$.

**Theorem.** The Touchard transform $x^n \mapsto T_n(x)$ maps
Pólya-frequency polynomials to Pólya-frequency polynomials. For every
$\mu > 0$, so does the rising-factorial transform
$x^n \mapsto (x \mid \mu)_n$.

## Matrix products

For a lower-triangular array $M = (M(n,k))_{n,k \geq 0}$, the row-generating
polynomial of row $n$ is $M_n(x) = \sum_{k=0}^n M(n,k) x^k$, and
`RowGeneratingFunctionsPF M` says that every $M_n$ is Pólya-frequency. The
Mao–Wang admissible factors (`MaoWangAdmissibleMatrix`) are the coefficient
matrices of the bases
$(ax + d)^n$ with $a > 0$ and $d \geq 0$, $T_n(x)$, $(x \mid \mu)_n$ with
$\mu > 0$, and $N_{n,m}(x)$; row $n$ of the coefficient matrix of a basis
$(B_n)$ lists the coefficients of $B_n$.

**Theorem (Mao–Wang).** Let $M$ be lower-triangular with Pólya-frequency
row-generating polynomials, and let $B_1, \dotsc, B_r$ be admissible factors.
Then $M B_1 \dotsm B_r$ has Pólya-frequency row-generating polynomials. In
particular this holds for $M B^r$ with $B$ admissible and $r \geq 0$.

## References

The coefficient normalization is from Jianxi Mao and Lijie Wang, [“The
Narayana transformation,”](https://arxiv.org/abs/2607.01572) arXiv:2607.01572
(2026).  The root-location input is D. Dominici, S. J. Johnston,
and K. Jordaan, [“Real zeros of 2F1 hypergeometric
polynomials,”](https://arxiv.org/abs/1301.4771) *Journal of Computational and
Applied Mathematics* 247 (2013), 152–161.  The falling-factorial theorem is
F. Brenti, [“Unimodal, log-concave and Pólya frequency sequences in
combinatorics,”](https://doi.org/10.1090/memo/0413) *Memoirs of the American
Mathematical Society* 81 (1989), no. 413, Theorem 2.4.2; Mao and Wang
use it as Lemma 3.2, and the matrix-product theorem is their Theorem 1.3.
See also the
[Narayana real-rootedness examples on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedCatalan.htm#ex:narayanaSturm),
[Brenti's falling-factorial theorem](https://www.symmetricfunctions.com/realRooted.htm#thm:brentiFallingFactorialBasis),
and the
[Mao–Wang row-generating functions](https://www.symmetricfunctions.com/realRooted.htm#rowGeneratingFunction).
<!-- /realrooted-catalog-content -->
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Narayana

/-- **Brenti's falling-factorial theorem** (Brenti 1989, Theorem 2.4.2).  If the
falling-factorial transform of `p` has only nonpositive roots, then so does `p`. -/
theorem HasOnlyNonposRoots.of_basisTransform_fallingFactorial {p : ℝ[X]}
    (h : HasOnlyNonposRoots (basisTransform fallingFactorialPolynomial p)) :
    HasOnlyNonposRoots p :=
  brentiFallingFactorial h

/-- The Touchard transform `x ^ n ↦ touchard n` preserves PF polynomials. -/
theorem isPFPolynomial_basisTransform_touchard {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform touchard p) :=
  touchardTransformPreservesPF hp

/-- For `μ > 0`, the generalized rising-factorial transform preserves PF polynomials. -/
theorem isPFPolynomial_basisTransform_risingFactorial {μ : ℝ} (hμ : 0 < μ) {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (basisTransform (risingFactorialPolynomial μ) p) :=
  generalizedRisingFactorialPreservesPF hμ hp

open LowerTriangularMatrix

/-- **Mao–Wang matrix-product theorem** (Mao–Wang 2026, Theorem 1.3).  Right multiplication
by a finite product of admissible factors keeps every row-generating polynomial PF. -/
theorem rowGeneratingFunctionsPF_mul_listProduct {M : LowerTriangularMatrix ℝ}
    {Bs : List (LowerTriangularMatrix ℝ)} (hBs : ∀ B ∈ Bs, MaoWangAdmissibleMatrix B)
    (hM : RowGeneratingFunctionsPF M) :
    RowGeneratingFunctionsPF (LowerTriangularMatrix.mul M (listProduct Bs)) :=
  maoWang_matrixListProduct_rowGeneratingFunctions_pf hBs hM

/-- **Mao–Wang matrix-product theorem, powers.**  Right multiplication by a power of one
admissible factor keeps every row-generating polynomial PF. -/
theorem rowGeneratingFunctionsPF_mul_pow {M B : LowerTriangularMatrix ℝ}
    (hB : MaoWangAdmissibleMatrix B) (r : ℕ) (hM : RowGeneratingFunctionsPF M) :
    RowGeneratingFunctionsPF (LowerTriangularMatrix.mul M (LowerTriangularMatrix.pow B r)) :=
  maoWang_matrixProduct_rowGeneratingFunctions_pf hB r hM

end Narayana
end Challenges
end RealRooted
