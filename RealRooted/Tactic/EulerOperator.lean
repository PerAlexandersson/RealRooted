import RealRooted.EulerOperator

/-!
# Euler-operator tactic frontends

Thin wrappers for the proved `theta + 1`, polar-theta, and iterate APIs in
`RealRooted.EulerOperator`.
-/

open Polynomial

namespace RealRooted

/-- Default proved PF preservation for the `l`-fold iterate of `theta + 1`. -/
theorem isPFPolynomial_iterateThetaPlusOne
    (l : ℕ) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (iterateThetaPlusOne l p) :=
  iterateThetaPlusOne_preserves_pf thetaPlusOne_preserves_pf l hp

/-- Default proved `Prec0` preservation for the `l`-fold iterate of `theta + 1`. -/
theorem prec0_iterateThetaPlusOne
    (l : ℕ) {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Prec0 p q) :
    Prec0 (iterateThetaPlusOne l p) (iterateThetaPlusOne l q) :=
  iterateThetaPlusOne_preserves_prec0
    thetaPlusOne_preserves_pf thetaPlusOnePreservesPrec0 l hp hq hpq

namespace Tactic

syntax (name := rr_theta_nonneg_named)
  "rr_theta_nonneg" " using " "nonneg" ":=" term :
  tactic

syntax (name := rr_thetaPlusOne_nonneg_named)
  "rr_thetaPlusOne_nonneg" " using " "nonneg" ":=" term :
  tactic

syntax (name := rr_polarTheta_nonneg_named)
  "rr_polarTheta_nonneg" " using "
    "nonneg" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_thetaPlusOne_pf_named)
  "rr_thetaPlusOne_pf" " using " "pf" ":=" term :
  tactic

syntax (name := rr_polarTheta_pf_named)
  "rr_polarTheta_pf" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_iterateThetaPlusOne_pf_named)
  "rr_iterateThetaPlusOne_pf" " using "
    "index" ":=" term ","
    "pf" ":=" term :
  tactic

syntax (name := rr_thetaPlusOne_prec0_named)
  "rr_thetaPlusOne_prec0" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "prec0" ":=" term :
  tactic

syntax (name := rr_iterateThetaPlusOne_prec0_named)
  "rr_iterateThetaPlusOne_prec0" " using "
    "index" ":=" term ","
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "prec0" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_theta_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.theta $hp)
  | `(tactic| rr_thetaPlusOne_nonneg using nonneg := $hp:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.thetaPlusOne $hp)
  | `(tactic|
      rr_polarTheta_nonneg using
        nonneg := $hp:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.polarTheta $hp $hdeg)
  | `(tactic| rr_thetaPlusOne_pf using pf := $hp:term) =>
      `(tactic| exact RealRooted.thetaPlusOne_preserves_pf $hp)
  | `(tactic|
      rr_polarTheta_pf using
        pf := $hp:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.polarTheta_preserves_pf $hp $hdeg)
  | `(tactic|
      rr_iterateThetaPlusOne_pf using
        index := $l:term,
        pf := $hp:term) =>
      `(tactic| exact RealRooted.isPFPolynomial_iterateThetaPlusOne $l $hp)
  | `(tactic|
      rr_thetaPlusOne_prec0 using
        left_pf := $hp:term,
        right_pf := $hq:term,
        prec0 := $hpq:term) =>
      `(tactic| exact RealRooted.thetaPlusOnePreservesPrec0 $hp $hq $hpq)
  | `(tactic|
      rr_iterateThetaPlusOne_prec0 using
        index := $l:term,
        left_pf := $hp:term,
        right_pf := $hq:term,
        prec0 := $hpq:term) =>
      `(tactic| exact RealRooted.prec0_iterateThetaPlusOne $l $hp $hq $hpq)

end Tactic
end RealRooted
