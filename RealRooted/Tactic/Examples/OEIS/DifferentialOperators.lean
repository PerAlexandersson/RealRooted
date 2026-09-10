import RealRooted.Tactic.EulerOperator
import RealRooted.Tactic.IteratedDerivativeShift
import RealRooted.Tactic.Wagner

/-!
# OEIS differential-operator regression examples

Regression examples for Euler, derivative-shift, and Wagner frontends.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Euler-operator PF row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, IsPFPolynomial (thetaPlusOne (P n)) := by
  rr_thetaPlusOne_sequence_pf using pf := hP

/-- Iterated Euler-operator proper-position row-family exit exposed through
the OEIS facade. -/
example {l : Nat → Nat} {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hQ : ∀ n : Nat, IsPFPolynomial (Q n))
    (hPQ : ∀ n : Nat, Prec0 (P n) (Q n)) :
    ∀ n : Nat,
      Prec0 (iterateThetaPlusOne (l n) (P n)) (iterateThetaPlusOne (l n) (Q n)) := by
  rr_iterateThetaPlusOne_sequence_prec0 using
    index := l,
    left_pf := hP,
    right_pf := hQ,
    prec0 := hPQ

/-- Derivative-shift row-family real-rootedness exit exposed through the OEIS
facade. -/
example {eps : Nat → ℝ} {P : Nat → ℝ[X]}
    (heps : ∀ n : Nat, 0 < eps n)
    (hP : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat, (TDeriv (eps n) (P n)).Splits := by
  rr_TDeriv_sequence_splits using
    eps_pos := heps,
    splits := hP

/-- Iterated derivative-shift row-family proper-position exit exposed through
the OEIS facade. -/
example {eps : Nat → ℝ} {K : Nat → Nat} {P : Nat → ℝ[X]}
    (heps : ∀ n : Nat, 0 < eps n)
    (hP0 : ∀ n : Nat, P n ≠ 0)
    (hP : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat,
      Prec (iterateTDeriv (eps n) (K n) (P n))
        (iterateTDeriv (eps n) (K n + 1) (P n)) := by
  rr_iterateTDeriv_sequence_prec_succ using
    eps_pos := heps,
    nonzero := hP0,
    splits := hP,
    index := K

/-- Wagner common-left addition row-family exit exposed through the OEIS
facade. -/
example {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (H n))
    (hHF : ∀ n : Nat, Prec (H n) (F n))
    (hHG : ∀ n : Nat, Prec (H n) (G n)) :
    ∀ n : Nat, Prec (H n) (F n + G n) := by
  rr_wagner_common_left_add_sequence using
    left := hF,
    right := hG,
    common := hH,
    common_interlaces_left := hHF,
    common_interlaces_right := hHG


end Tactic
end RealRooted
