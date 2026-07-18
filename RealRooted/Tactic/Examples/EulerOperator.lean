import RealRooted.Tactic.EulerOperator

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (theta p) := by
  rr_theta_nonneg using nonneg := hp

example {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (thetaPlusOne p) := by
  rr_thetaPlusOne_nonneg using nonneg := hp

example {N : ℕ} {p : ℝ[X]} (hp : HasNonnegCoeffs p) (hdeg : p.natDegree ≤ N) :
    HasNonnegCoeffs (polarTheta N p) := by
  rr_polarTheta_nonneg using nonneg := hp, degree := hdeg

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (thetaPlusOne p) := by
  rr_thetaPlusOne_pf using pf := hp

example {N : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hdeg : p.natDegree ≤ N) :
    IsPFPolynomial (polarTheta N p) := by
  rr_polarTheta_pf using pf := hp, degree := hdeg

example {l : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (iterateThetaPlusOne l p) := by
  rr_iterateThetaPlusOne_pf using index := l, pf := hp

example {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (thetaPlusOne p) (thetaPlusOne q) := by
  rr_thetaPlusOne_prec0 using left_pf := hp, right_pf := hq, prec0 := hpq

example {l : ℕ} {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (iterateThetaPlusOne l p) (iterateThetaPlusOne l q) := by
  rr_iterateThetaPlusOne_prec0 using
    index := l,
    left_pf := hp,
    right_pf := hq,
    prec0 := hpq

end Tactic
end RealRooted
