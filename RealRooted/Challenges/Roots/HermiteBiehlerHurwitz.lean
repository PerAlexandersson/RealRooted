module

public import RealRooted.ClassicalHurwitzMatrix
public import RealRooted.ClassicalHurwitzMatrix.Stability.CoefficientSigns
public import RealRooted.ClassicalHurwitzMatrix.Stability.Converse
public import RealRooted.ClassicalHurwitzMatrix.Stability.Lace
public import RealRooted.ClassicalHurwitzMatrix.Stability.OddEvenConverse
public import RealRooted.ClassicalHurwitzMatrix.Stability.WeakConverse
public import RealRooted.HurwitzMatrix
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz.Determinant

public section

open Polynomial

/-!
# Hermite--Biehler and Hurwitz challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hermite-biehler-hurwitz"
formalized = "2026-07-10"
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
label = "Weak Hurwitz stability with nonnegative coefficients"

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
label = "Hermite–Biehler: interlacing gives stability"
headline = true

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.hermiteBiehler_converse"
label = "Hermite–Biehler: stability gives interlacing"
headline = true

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.isHurwitzStable_oddEvenPolynomial_iff"
label = "Hermite–Biehler for odd and even parts"

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.classicalHurwitzCriterion"
label = "Hurwitz criterion via total nonnegativity"
headline = true

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.hasNonnegCoeffs_of_isRightHalfPlaneStable"
label = "Weak Hurwitz stability gives nonnegative coefficients"

[[theorems]]
name = "RealRooted.Challenges.HermiteBiehlerHurwitz.coeff_pos_of_isStrictlyHurwitzStable"
label = "Strict Hurwitz stability gives positive coefficients"

[[theorems]]
name = "RealRooted.fullyInterlacingPair_of_isHurwitzStable_oddEvenPolynomial"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.Lace"
label = "Hurwitz stability gives a totally nonnegative Lace matrix"

[[theorems]]
name = "RealRooted.StrictInterl.fullyInterlacingPair"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.Lace"
label = "Hermite–Biehler in Lace form"

[[theorems]]
name = "Matrix.strictlyHurwitzStable_iff_hurwitzLeadingPrincipal_det_pos"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.Converse"
label = "Routh–Hurwitz: strict stability iff all leading Hurwitz minors are positive"
headline = true
-->

<!-- realrooted-catalog-content -->
# Hermite–Biehler and Hurwitz criteria

The Hermite–Biehler theorem characterizes half-plane stability through
interlacing of the even and odd parts. The Hurwitz criterion characterizes
weak Hurwitz stability by total nonnegativity of the classical Hurwitz matrix.
Reversing the polynomial turns the Hurwitz matrix into the two-row Lace matrix of the
even and odd parts: if $q(x^2) + x\,p(x^2)$ is Hurwitz stable, then the matrix whose even
rows are shifts of the coefficients of $q$ and whose odd rows are shifts of those of $p$ is
totally nonnegative. In particular this holds when $p \ll q$ have nonnegative coefficients.

**Theorem (Hermite–Biehler).** Let $f$ and $g$ be real polynomials with
positive leading coefficients. If $g \ll f$ (see
[interlacing](/RealRooted/concepts/interlacing/)), then $f + ig$ has no zeros
in the open upper half-plane. Conversely, if $f + ig$ has no zeros there, then
$g \ll f$.

**Corollary (odd and even parts).** Let $p$ and $q$ be nonzero real
polynomials. Then $q(x^2) + x\,p(x^2)$ has nonnegative coefficients and no
zeros with positive real part if and only if $p$ and $q$ have nonnegative
coefficients and $p \ll q$.

**Theorem (Hurwitz).** A nonzero real polynomial $p = \sum_k a_k x^k$ has
nonnegative coefficients and no zeros with positive real part if and only if its
classical Hurwitz matrix $(a_{2j-i})_{i,j \geq 0}$, with $a_k = 0$ for $k < 0$,
is totally nonnegative.

**Proposition (coefficient signs).** Let $p$ be a real polynomial with
positive leading coefficient. If $p$ has no zeros with positive real part, then
all coefficients of $p$ are nonnegative. If all zeros of $p$ have negative real
part, then all coefficients $a_0, \dotsc, a_{\deg p}$ are positive.

**Theorem** (Routh–Hurwitz). A real polynomial with positive leading
coefficient is strictly Hurwitz stable if and only if all leading principal
minors of its Hurwitz matrix are positive. The library uses the
constant-term-first convention for the Hurwitz matrix, and the proof propagates
the minors along the Routh reduction.

## References

See [@Holtz2003], the
[Hermite–Biehler theorem](sf:hermiteBiehlerTheorem), and the
[coefficient signs of Hurwitz-stable polynomials](sf:hurwitzImpliesCoefficientPositivity).
The related [Hurwitz–Lace criterion](sf:hurwitzLaceCriterion) is stated for a
different matrix, built from two polynomials, and is not formalized here.
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
