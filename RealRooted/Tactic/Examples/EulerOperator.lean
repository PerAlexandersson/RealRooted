import RealRooted.Tactic.EulerOperator

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (theta p) := by
  rr_theta_nonneg using nonneg := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (theta (P i)) := by
  rr_theta_sequence_nonneg using nonneg := hP

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (theta p) := by
  rr_theta_pf using pf := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (theta (P i)) := by
  rr_theta_sequence_pf using pf := hP

example {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (thetaPlusOne p) := by
  rr_thetaPlusOne_nonneg using nonneg := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, HasNonnegCoeffs (thetaPlusOne (P i)) := by
  rr_thetaPlusOne_sequence_nonneg using nonneg := hP

example {N : ℕ} {p : ℝ[X]} (hp : HasNonnegCoeffs p) (hdeg : p.natDegree ≤ N) :
    HasNonnegCoeffs (polarTheta N p) := by
  rr_polarTheta_nonneg using nonneg := hp, degree := hdeg

example {N : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ N i) :
    ∀ i : Nat, HasNonnegCoeffs (polarTheta (N i) (P i)) := by
  rr_polarTheta_sequence_nonneg using
    nonneg := hP,
    degree := hdeg

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (thetaPlusOne p) := by
  rr_thetaPlusOne_pf using pf := hp

example {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (thetaPlusOne (P i)) := by
  rr_thetaPlusOne_sequence_pf using pf := hP

example {N : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) (hdeg : p.natDegree ≤ N) :
    IsPFPolynomial (polarTheta N p) := by
  rr_polarTheta_pf using pf := hp, degree := hdeg

example {N : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hdeg : ∀ i : Nat, (P i).natDegree ≤ N i) :
    ∀ i : Nat, IsPFPolynomial (polarTheta (N i) (P i)) := by
  rr_polarTheta_sequence_pf using
    pf := hP,
    degree := hdeg

example {l : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (iterateThetaPlusOne l p) := by
  rr_iterateThetaPlusOne_pf using index := l, pf := hp

example {l : Nat → Nat} {P : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i)) :
    ∀ i : Nat, IsPFPolynomial (iterateThetaPlusOne (l i) (P i)) := by
  rr_iterateThetaPlusOne_sequence_pf using
    index := l,
    pf := hP

example {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (thetaPlusOne p) (thetaPlusOne q) := by
  rr_thetaPlusOne_prec0 using left_pf := hp, right_pf := hq, prec0 := hpq

example {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i))
    (hPQ : ∀ i : Nat, Prec0 (P i) (Q i)) :
    ∀ i : Nat, Prec0 (thetaPlusOne (P i)) (thetaPlusOne (Q i)) := by
  rr_thetaPlusOne_sequence_prec0 using
    left_pf := hP,
    right_pf := hQ,
    prec0 := hPQ

example {l : ℕ} {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (iterateThetaPlusOne l p) (iterateThetaPlusOne l q) := by
  rr_iterateThetaPlusOne_prec0 using
    index := l,
    left_pf := hp,
    right_pf := hq,
    prec0 := hpq

example {l : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i))
    (hPQ : ∀ i : Nat, Prec0 (P i) (Q i)) :
    ∀ i : Nat,
      Prec0 (iterateThetaPlusOne (l i) (P i)) (iterateThetaPlusOne (l i) (Q i)) := by
  rr_iterateThetaPlusOne_sequence_prec0 using
    index := l,
    left_pf := hP,
    right_pf := hQ,
    prec0 := hPQ

end Tactic
end RealRooted
