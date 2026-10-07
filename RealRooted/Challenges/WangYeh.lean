import RealRooted.WangYeh.TriangularMatrix

/-!
# The Wang–Yeh affine criterion

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "wang-yeh"
authors = ["Wang", "Yeh"]
years = [2005]

[[definitions]]
name = "RealRooted.bidiagonalOperator"
module = "RealRooted.MultiplierSequence.Bidiagonal"
label = "Coefficient-bidiagonal operator"

[[theorems]]
name = "RealRooted.Challenges.WangYeh.eq_zero_or_splits_affine_add"
label = "(bx + a) f + (dx + c) g is real-rooted or zero when ad ≥ bc"
headline = true

[[theorems]]
name = "RealRooted.Challenges.WangYeh.isPFPolynomial_bidiagonalOperator"
label = "Affine bidiagonal transforms preserve Pólya-frequency polynomials"
headline = true

[[theorems]]
name = "RealRooted.Challenges.WangYeh.isPolyaFreqSeq_row_of_bilinear_recurrence"
label = "Rows of a bilinear triangular recurrence are Pólya-frequency sequences"
headline = true

[[theorems]]
name = "RealRooted.Challenges.WangYeh.isPFPolynomial_rows_of_bilinear_recurrence"
label = "Row polynomials of a bilinear triangular recurrence are Pólya-frequency"
-->

<!-- realrooted-catalog-content -->
# The Wang–Yeh affine criterion

For real-rooted polynomials $g$ and $f$ we write $g \ll f$ (`StrictInterl g f`)
as on the [interlacing page](/RealRooted/concepts/interlacing/). A polynomial
is Pólya-frequency (`IsPFPolynomial`) if it has nonnegative coefficients and is
either zero or real-rooted with nonpositive zeros. A sequence is
Pólya-frequency (`IsPolyaFreqSeq`) if its Toeplitz matrix is totally
nonnegative.

**Theorem (Wang–Yeh).** Let $f, g \in \mathbb{R}[x]$ have positive leading
coefficients and satisfy $g \ll f$. If $a, b, c, d \in \mathbb{R}$ satisfy
$bc \leq ad$, then
$$
(bx + a) f(x) + (dx + c) g(x)
$$
is zero or real-rooted.

The four coefficients have no sign assumptions.

**Theorem (PF preserver).** Let $p(x) = \sum_k x_k x^k$ be a Pólya-frequency
polynomial, and let $a, b, c, d \in \mathbb{R}$ satisfy $bc \leq ad$. Define
$$
y_k = (a + c(k-1))\, x_{k-1} + (b + dk)\, x_k, \qquad x_{-1} = 0.
$$
If every $y_k$ is nonnegative, then $\sum_k y_k x^k$ is Pólya-frequency. In
Lean the map $p \mapsto \sum_k y_k x^k$ is the coefficient-bidiagonal operator
`bidiagonalOperator (fun k ↦ b + d * k) (fun k ↦ a + c * k)`.

**Theorem (bilinear triangular arrays).** Let $A(n, k)$ be a nonnegative
lower-triangular array with $A(0, 0) = 1$, and suppose that
$$
A(n+1, k) = (r(n+1) + sk + t)\, A(n, k-1) + (a(n+1) + bk + c)\, A(n, k)
$$
for all $n, k \geq 0$, with $A(n, -1) = 0$. If
$$
as \leq rb \qquad\text{and}\qquad (a + c)s \leq (r + s + t)b,
$$
then every row $(A(n, 0), A(n, 1), \dotsc)$ is a Pólya-frequency sequence.
Equivalently, every row-generating polynomial $\sum_k A(n, k) x^k$ is
Pólya-frequency.

## Proof idea

Put $H = (bx + a) f + (dx + c) g$ and $K = (bx + a) g - (dx + c) f$. By the
Hermite–Biehler theorem, $g \ll f$ makes $f + ig$ stable in the upper half
plane. The complex combination $H + iK$ is $f + ig$ times the linear factor
$(b - id)x + (a - ic)$, whose zero lies in the closed lower half plane exactly
when $bc \leq ad$. Hence $H + iK$ is stable, and its real part $H$ is zero or
real-rooted. If $b = d = 0$, the claim is the classical fact that every real
combination $af + cg$ is real-rooted.

For the PF preserver, a nonconstant Pólya-frequency polynomial $p$ satisfies
$p \ll xp'$, and the bidiagonal image of $p$ equals
$(ax + b)\,p + (cx + d)\,xp'$, the Wang–Yeh combination for this pair. Each row of the
triangular array is the bidiagonal image of the previous row, and the two
inequalities give the determinant condition at every step.

## References

Y. Wang and Y.-N. Yeh, [“Polynomials with real zeros and Pólya frequency
sequences,”](https://doi.org/10.1016/j.jcta.2004.07.008) *Journal of
Combinatorial Theory, Series A* 109 (2005), 63–74, Theorem 1 and Corollaries 2
and 3.
See also the
[Wang–Yeh criterion on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#wangYehAffineCriterion)
and the
[Wang–Yeh PF preserver](https://www.symmetricfunctions.com/polyaFrequency.htm#wangYehPfPreserver).
<!-- /realrooted-catalog-content -->

The affine criterion lives in `RealRooted.WangYeh.Affine`, the PF preserver in
`RealRooted.WangYeh.PF`, and the triangular-array corollaries in
`RealRooted.WangYeh.TriangularArray` and `RealRooted.WangYeh.TriangularMatrix`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace WangYeh

/-- **Wang–Yeh affine criterion** (Wang–Yeh 2005, Theorem 1).  If `g ≪ f`, both with positive
leading coefficient, and `b * c ≤ a * d`, then `(bX + a) f + (dX + c) g` is zero or splits. -/
theorem eq_zero_or_splits_affine_add {f g : ℝ[X]} {a b c d : ℝ} (hgf : StrictInterl g f)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) (hdet : b * c ≤ a * d) :
    (C b * X + C a) * f + (C d * X + C c) * g = 0 ∨
      ((C b * X + C a) * f + (C d * X + C c) * g).Splits :=
  wangYehAffine_eq_zero_or_splits hgf hf_pos hg_pos hdet

/-- **Wang–Yeh PF preserver** (Wang–Yeh 2005, Corollary 2).  The coefficient-bidiagonal
operator `y_k = (b + d k) x_k + (a + c (k - 1)) x_{k-1}` maps a PF polynomial to a PF
polynomial when `b * c ≤ a * d` and the output has nonnegative coefficients. -/
theorem isPFPolynomial_bidiagonalOperator {p : ℝ[X]} {a b c d : ℝ} (hp : IsPFPolynomial p)
    (hdet : b * c ≤ a * d)
    (hout : HasNonnegCoeffs
      (bidiagonalOperator (fun k ↦ b + d * (k : ℝ)) (fun k ↦ a + c * (k : ℝ)) p)) :
    IsPFPolynomial
      (bidiagonalOperator (fun k ↦ b + d * (k : ℝ)) (fun k ↦ a + c * (k : ℝ)) p) :=
  hp.wangYeh_bidiagonal hdet hout

/-- **Wang–Yeh triangular arrays** (Wang–Yeh 2005, Corollary 3).  A nonnegative
lower-triangular array with `A 0 0 = 1` and the bilinear row recurrence has a PF sequence in
every row, provided `a * s ≤ r * b` and `(a + c) * s ≤ (r + s + t) * b`. -/
theorem isPolyaFreqSeq_row_of_bilinear_recurrence (A : ℕ → ℕ → ℝ) (r s t a b c : ℝ)
    (hlower : ∀ i j, i < j → A i j = 0) (hbase : A 0 0 = 1)
    (hzero : ∀ n, A (n + 1) 0 = (a * (n + 1 : ℝ) + c) * A n 0)
    (hsucc : ∀ n k, A (n + 1) (k + 1) =
      (r * (n + 1 : ℝ) + s * (k + 1 : ℝ) + t) * A n k +
        (a * (n + 1 : ℝ) + b * (k + 1 : ℝ) + c) * A n (k + 1))
    (hnonneg : ∀ n k, 0 ≤ A n k) (hrb : a * s ≤ r * b)
    (hboundary : (a + c) * s ≤ (r + s + t) * b) (n : ℕ) :
    IsPolyaFreqSeq (A n) :=
  wangYeh_triangularMatrix_rows_pf A r s t a b c (fun h ↦ hlower _ _ h) hbase hzero hsucc
    hnonneg hrb hboundary n

/-- **Wang–Yeh triangular arrays, row polynomials.**  If `P 0 = 1`, the coefficients of
consecutive rows satisfy the bilinear recurrence, every row has nonnegative coefficients, and
`a * s ≤ r * b` and `(a + c) * s ≤ (r + s + t) * b`, then every row polynomial is PF. -/
theorem isPFPolynomial_rows_of_bilinear_recurrence (P : ℕ → ℝ[X]) (r s t a b c : ℝ)
    (hbase : P 0 = 1)
    (hzero : ∀ n, (P (n + 1)).coeff 0 = (a * (n + 1 : ℝ) + c) * (P n).coeff 0)
    (hsucc : ∀ n k, (P (n + 1)).coeff (k + 1) =
      (r * (n + 1 : ℝ) + s * (k + 1 : ℝ) + t) * (P n).coeff k +
        (a * (n + 1 : ℝ) + b * (k + 1 : ℝ) + c) * (P n).coeff (k + 1))
    (hnonneg : ∀ n, HasNonnegCoeffs (P n)) (hrb : a * s ≤ r * b)
    (hboundary : (a + c) * s ≤ (r + s + t) * b) (n : ℕ) :
    IsPFPolynomial (P n) :=
  wangYeh_triangularRows_pf P r s t a b c hbase hzero hsucc hnonneg hrb hboundary n

end WangYeh
end Challenges
end RealRooted
