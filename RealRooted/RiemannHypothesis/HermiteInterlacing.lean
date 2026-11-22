module

public import RealRooted.RiemannHypothesis.HermiteSimple
import RealRooted.Hermite.Appell

/-!
# Consecutive xi Hermite polynomials

The Appell identity preserves the xi coefficient shift. Under RH, adjacent
degree rows interlace and share no root. The separate no-common-root assertion
is essential because the project's `StrictInterl` permits coincident roots.
-/

public section

open Polynomial

namespace RealRooted

/-- Differentiation lowers the degree and leaves the xi coefficient shift fixed. -/
theorem derivative_riemannXiHermitePolynomial (d n : ℕ) :
    (riemannXiHermitePolynomial (d + 1) n).derivative =
      C (2 * (d + 1 : ℝ)) * riemannXiHermitePolynomial d n :=
  derivative_hermiteJensenPolynomial d (fun k => riemannXiCoeff (n + k))

/-- Under RH, consecutive fixed-shift Hermite rows interlace, including the
constant-to-linear endpoint. -/
theorem riemannXiHermitePolynomial_strictInterl
    (hRH : RiemannHypothesis) (d n : ℕ) :
    StrictInterl (riemannXiHermitePolynomial d n) (riemannXiHermitePolynomial (d + 1) n) := by
  apply hermiteJensenPolynomial_strictInterl (riemannXiHermitePolynomial_splits hRH (d + 1) n)
  have h0 := riemannXiHermitePolynomial_ne_zero 0 n
  simpa [riemannXiHermitePolynomial, hermiteJensenPolynomial] using h0

/-- Adjacent fixed-shift Hermite rows have disjoint real zero sets under RH. -/
theorem riemannXiHermitePolynomial_no_common_root
    (hRH : RiemannHypothesis) (d n : ℕ) (r : ℝ) :
    ¬ ((riemannXiHermitePolynomial d n).IsRoot r ∧
      (riemannXiHermitePolynomial (d + 1) n).IsRoot r) :=
  hermiteJensenPolynomial_no_common_root
    (isSimpleRealRooted_riemannXiHermitePolynomial hRH (d + 1) n).2.2 r

end RealRooted
