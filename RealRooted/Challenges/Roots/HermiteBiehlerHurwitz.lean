module

import RealRooted.ClassicalHurwitzMatrix.Stability.CoefficientSigns
import RealRooted.ClassicalHurwitzMatrix.Stability.Converse
import RealRooted.ClassicalHurwitzMatrix.Stability.Lace
import RealRooted.ClassicalHurwitzMatrix.Stability.OddEvenConverse
import RealRooted.ClassicalHurwitzMatrix.Stability.WeakConverse
import RealRooted.HermiteBiehler.Basic
import RealRooted.HermiteBiehler.Forward
import RealRooted.HermiteBiehler.OddEven
import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz
import RealRooted.SamePhaseInterlacing

/-!
# Hermite–Biehler and Hurwitz stability criteria

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "hermite-biehler-hurwitz"
formalized = "2026-07-10"
references = [
  "Holtz2003",
]
authors = ["Hermite", "Routh", "Biehler", "Hurwitz", "Holtz"]
years = [1856, 1877, 1879, 1895, 2003]

[[definitions]]
name = "RealRooted.IsHurwitzStable"
module = "RealRooted.HermiteBiehler.Basic"
label = "Hurwitz stable: nonnegative coefficients and no zeros with positive real part"

[[definitions]]
name = "RealRooted.oddEvenPolynomial"
module = "RealRooted.HermiteBiehler.OddEven"
label = "The odd/even polynomial q(x²) + x p(x²)"

[[definitions]]
name = "Matrix.hurwitz"
module = "RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz"
label = "The classical Hurwitz matrix"

[[theorems]]
name = "RealRooted.hermiteBiehlerForwardPos"
module = "RealRooted.HermiteBiehler.Forward"
label = "Hermite–Biehler: g ≪ f implies f + ig has no zeros with positive imaginary part"

[[theorems]]
name = "RealRooted.strictInterl_of_upperHalfPlaneStable_hermiteBiehler"
module = "RealRooted.SamePhaseInterlacing"
label = "Hermite–Biehler, converse: f + ig without such zeros implies g ≪ f"

[[theorems]]
name = "RealRooted.isHurwitzStable_oddEvenPolynomial_iff"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.OddEvenConverse"
label = "q(x²) + x p(x²) is Hurwitz stable iff p ≪ q with nonnegative coefficients"
headline = true

[[theorems]]
name = "RealRooted.isHurwitzStable_iff_hurwitz_isTotallyNonneg"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.WeakConverse"
label = "Hurwitz criterion: stable iff the Hurwitz matrix is totally nonnegative"

[[theorems]]
name = "RealRooted.hasNonnegCoeffs_of_isRightHalfPlaneStable"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.CoefficientSigns"
label = "No zeros with positive real part implies nonnegative coefficients"

[[theorems]]
name = "RealRooted.fullyInterlacingPair_of_isHurwitzStable_oddEvenPolynomial"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.Lace"
label = "If q(x²) + x p(x²) is Hurwitz stable, the Lace matrix of (q, p) is totally nonnegative"

[[theorems]]
name = "Matrix.strictlyHurwitzStable_iff_hurwitzLeadingPrincipal_det_pos"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.Converse"
label = "Routh–Hurwitz: all zeros in the open left half-plane iff leading minors are positive"
-->

<!-- realrooted-catalog-content -->
# Hermite–Biehler and Hurwitz stability criteria

By the Hermite–Biehler theorem, $g\ll f$ exactly when $f+ig$ has no zeros in the open upper
half-plane. Consequently a real polynomial is Hurwitz stable if and only if its even and odd
parts interlace, and if and only if its Hurwitz matrix is totally nonnegative.

## Results

A real polynomial is *Hurwitz stable* if it has nonnegative coefficients and no zeros with
positive real part. Let $p=\sum_k a_kx^k$ with $a_k=0$ for $k<0$. The *Hurwitz matrix* of $p$ is
$(a_{2j-i})_{i,j\ge0}$.

**Theorem (Hermite–Biehler).** Let $f$ and $g$ be real polynomials with positive leading
coefficients. Then $g\ll f$ if and only if $f+ig$ has no zeros with positive imaginary part.

**Corollary (odd and even parts).** For nonzero real polynomials $p$ and $q$, the polynomial
$q(x^2)+x\,p(x^2)$ is Hurwitz stable if and only if $p$ and $q$ have nonnegative coefficients
and $p\ll q$. In that case the two-row Lace matrix of $(q,p)$, whose rows are shifts of the
coefficient sequences of $q$ and $p$, is totally nonnegative.

**Theorem (Hurwitz).** A nonzero real polynomial is Hurwitz stable if and only if its Hurwitz
matrix is totally nonnegative.

**Theorem (Routh–Hurwitz).** A real polynomial $p$ with positive leading coefficient has all
zeros in the open left half-plane if and only if the leading principal minors of its Hurwitz
matrix of orders $1,\dots,\deg p$ are positive.

**Proposition (coefficient signs).** A real polynomial with positive leading coefficient and no
zeros with positive real part has nonnegative coefficients.

## Use

The corollary translates between Hurwitz stability of one polynomial and interlacing of two
polynomials in $x^2$, and turns interlacing pairs with nonnegative coefficients into totally
nonnegative matrices; see [totally nonnegative matrices](rr:totally-nonnegative-matrices).

## References

The classical sources are Hermite (1856), Routh (1877), Biehler (1879) and Hurwitz (1895); we
follow the account of [@Holtz2003]. See also the
[Hermite–Biehler theorem](sf:hermiteBiehlerTheorem),
[coefficient signs of Hurwitz-stable polynomials](sf:hurwitzImpliesCoefficientPositivity) and
the related [Hurwitz–Lace criterion](sf:hurwitzLaceCriterion) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
