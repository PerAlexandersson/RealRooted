module

public import RealRooted.ClassicalHurwitzMatrix
import RealRooted.ClassicalHurwitzMatrix.Stability.CoefficientSigns
public import RealRooted.ClassicalHurwitzMatrix.Stability.Converse
public import RealRooted.ClassicalHurwitzMatrix.Stability.Lace
import RealRooted.ClassicalHurwitzMatrix.Stability.OddEvenConverse
import RealRooted.ClassicalHurwitzMatrix.Stability.WeakConverse
public import RealRooted.HurwitzMatrix
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz.Determinant
public import RealRooted.ClassicalHurwitzMatrix.Stability
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz
import RealRooted.SamePhaseInterlacing
public import RealRooted.HermiteBiehler.OddEven
import RealRooted.HermiteBiehler.Forward
public import RealRooted.Basic.ProperPosition

public section

open Polynomial

/-!
# Hermite–Biehler and Hurwitz stability criteria

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hermite-biehler-hurwitz"
formalized = "2026-07-10"
tags = []
references = [
  "Holtz2003",
]
authors = ["Holtz"]
years = [2003]

[[definitions]]
name = "RealRooted.hermiteBiehlerPolynomial"
module = "RealRooted.HermiteBiehler.Basic"
label = "The Hermite–Biehler combination f + ig"

[[definitions]]
name = "RealRooted.IsUpperHalfPlaneStable"
module = "RealRooted.HermiteBiehler.Basic"
label = "No zeros in the open upper half-plane"

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
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.hermiteBiehler_forward"
label = "Hermite–Biehler: g ≪ f implies f + ig has no zeros with positive imaginary part"

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.hermiteBiehler_converse"
label = "Hermite–Biehler, converse: f + ig without such zeros implies g ≪ f"

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.isHurwitzStable_oddEvenPolynomial_iff"
label = "q(x²) + x p(x²) is Hurwitz stable iff p ≪ q with nonnegative coefficients"
headline = true

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.classicalHurwitzCriterion"
label = "Hurwitz criterion: stable iff the Hurwitz matrix is totally nonnegative"

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.hasNonnegCoeffs_of_isRightHalfPlaneStable"
label = "No zeros with positive real part implies nonnegative coefficients"

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.coeff_pos_of_isStrictlyHurwitzStable"
label = "All zeros with negative real part implies positive coefficients"

[[theorems]]
name = "RealRooted.fullyInterlacingPair_of_isHurwitzStable_oddEvenPolynomial"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.Lace"
label = "If q(x²) + x p(x²) is Hurwitz stable, the Lace matrix of (q, p) is totally nonnegative"

[[theorems]]
name = "RealRooted.StrictInterl.fullyInterlacingPair"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.Lace"
label = "If p ≪ q have nonnegative coefficients, the Lace matrix of (q, p) is totally nonnegative"

[[theorems]]
name = "Matrix.strictlyHurwitzStable_iff_hurwitzLeadingPrincipal_det_pos"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.Converse"
label = "Routh–Hurwitz: all zeros in the open left half-plane iff leading minors are positive"
-->

<!-- realrooted-catalog-content -->
# Hermite–Biehler and Hurwitz stability criteria

A real polynomial is Hurwitz stable if and only if its even and odd parts interlace, and if and
only if its Hurwitz matrix is totally nonnegative.

## Results

We write $f\ll g$ if $f$ interlaces $g$ (see [interlacing](/RealRooted/concepts/interlacing/)).
A real polynomial is *Hurwitz stable* if it has nonnegative coefficients and no zeros with
positive real part. Let $p=\sum_k a_kx^k$ with $a_k=0$ for $k<0$. The *Hurwitz matrix* of $p$ is
$(a_{2j-i})_{i,j\ge0}$.

**Theorem (Hermite–Biehler).** Let $f$ and $g$ be real polynomials with positive leading
coefficients. Then $g\ll f$ if and only if $f+ig$ has no zeros with positive imaginary part.

**Corollary (odd and even parts).** For nonzero real polynomials $p$ and $q$, the polynomial
$q(x^2)+x\,p(x^2)$ is Hurwitz stable if and only if $p$ and $q$ have nonnegative coefficients
and $p\ll q$.

**Theorem (Hurwitz).** A nonzero real polynomial is Hurwitz stable if and only if its Hurwitz
matrix is totally nonnegative.

**Theorem (Routh–Hurwitz).** A real polynomial $p$ with positive leading coefficient has all
zeros in the open left half-plane if and only if the leading principal minors of its Hurwitz
matrix of orders $1,\dots,\deg p$ are positive.

**Proposition (coefficient signs).** Let $p$ be a real polynomial with positive leading
coefficient. If $p$ has no zeros with positive real part, its coefficients are nonnegative. If all
its zeros have negative real part, then $a_0,\dots,a_{\deg p}$ are positive.

**Proposition (Lace form).** If $q(x^2)+x\,p(x^2)$ is Hurwitz stable, then the two-row Lace matrix
of $(q,p)$ is totally nonnegative. Its even rows are shifts of the coefficient sequence of $q$
and its odd rows are shifts of that of $p$. In particular this holds whenever $p\ll q$ and $p,q$
have nonnegative coefficients.

## Use

The Corollary reduces stability of a polynomial to interlacing of two polynomials in $x^2$.
By the Lace form, interlacing pairs with nonnegative coefficients have a totally nonnegative Lace
matrix.

## References

See [@Holtz2003], the [Hermite–Biehler theorem](sf:hermiteBiehlerTheorem), and the
[coefficient signs of Hurwitz-stable polynomials](sf:hurwitzImpliesCoefficientPositivity).
The related [Hurwitz–Lace criterion](sf:hurwitzLaceCriterion) is stated for a different matrix,
built from two polynomials.
<!-- /realrooted-catalog-content -->

Human statements:

* Hermite--Biehler:
  sf:hermiteBiehlerTheorem
* Hurwitz stability implies coefficient positivity:
  sf:hurwitzImpliesCoefficientPositivity
* Related, not formalized: the Hurwitz--Lace criterion, stated for a different
  matrix:
  sf:hurwitzLaceCriterion

Classical references include C. Hermite, A. Hurwitz, M. G. Krein, M. A. Naimark,
and the modern account by O. Holtz, "Hermite-Biehler, Routh-Hurwitz, and
total positivity", Linear Algebra Appl. 372 (2003), 105--110.

This module exposes the checked Hermite--Biehler and Hurwitz theorems. The refutation of
the criterion for the row-oriented matrix and the finite regressions for the classical
convention are in `RealRooted.ClassicalHurwitzMatrix.Examples`; the analytic stability bridges
and finite-minor plumbing remain in `RealRooted.HermiteBiehler` and `RealRooted.HurwitzMatrix`.
-/

namespace RealRooted
namespace Challenges
namespace HermiteBiehlerHurwitz


/-- Forward Hermite--Biehler theorem, sign-normalized: if `f` and `g` have
positive leading coefficients and `g` interlaces `f`, then `f + i g` has no
zeros in the open upper half-plane. -/
theorem hermiteBiehler_forward {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : StrictInterl g f) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) :=
  RealRooted.hermiteBiehlerForwardPos hf hg h

/-- Converse Hermite--Biehler theorem: if `f` and `g` have positive leading
coefficients and `f + i g` has no zeros in the open upper half-plane, then `g`
interlaces `f`. -/
theorem hermiteBiehler_converse {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    StrictInterl g f :=
  RealRooted.strictInterl_of_upperHalfPlaneStable_hermiteBiehler hf hg h

/-- Hermite--Biehler theorem for odd and even parts: for nonzero `p` and `q`,
the polynomial `q(x²) + x p(x²)` is Hurwitz stable exactly when `p` and `q`
have nonnegative coefficients and `p` interlaces `q`. -/
theorem isHurwitzStable_oddEvenPolynomial_iff {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    IsHurwitzStable (RealRooted.oddEvenPolynomial p q) ↔
      HasNonnegCoeffs p ∧ HasNonnegCoeffs q ∧ StrictInterl p q :=
  RealRooted.isHurwitzStable_oddEvenPolynomial_iff hp hq

/-- A real polynomial with positive leading coefficient and no zeros in the
open right half-plane has nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_isRightHalfPlaneStable {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) (h : IsRightHalfPlaneStable (complexify p)) :
    HasNonnegCoeffs p :=
  RealRooted.hasNonnegCoeffs_of_isRightHalfPlaneStable hp h

/-- A real polynomial with positive leading coefficient and all zeros in the
open left half-plane has every coefficient up to its degree positive. -/
theorem coeff_pos_of_isStrictlyHurwitzStable {p : ℝ[X]}
    (h : RealRooted.IsStrictlyHurwitzStable p) (hp : HasPosLeadingCoeff p) {k : ℕ}
    (hk : k ≤ p.natDegree) : 0 < p.coeff k :=
  h.coeff_pos hp hk

/-- The classical Hurwitz criterion for nonzero real polynomials. -/
theorem classicalHurwitzCriterion {p : ℝ[X]} (hp : p ≠ 0) :
    RealRooted.IsHurwitzStable p ↔
      (Matrix.hurwitz p.coeff).IsTotallyNonneg :=
  RealRooted.isHurwitzStable_iff_hurwitz_isTotallyNonneg hp

end HermiteBiehlerHurwitz
end Challenges
end RealRooted
