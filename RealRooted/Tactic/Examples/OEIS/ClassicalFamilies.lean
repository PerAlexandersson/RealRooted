import RealRooted.Tactic.HermiteBiehler
import RealRooted.Tactic.HermitePoulain
import RealRooted.Tactic.Kurtz
import RealRooted.Tactic.Narayana

/-!
# OEIS classical-family regression examples

Regression examples for classical real-rootedness family frontends.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- Kurtz coefficient-criterion exit exposed through the OEIS facade. -/
example {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : RealRooted.Kurtz.KurtzStrictInequalities p) :
    p.Splits := by
  rr_kurtz using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

/-- Kurtz row-family exit exposed through the OEIS facade. -/
example {P : Nat → ℝ[X]}
    (hdeg : ∀ n : Nat, 2 ≤ (P n).natDegree)
    (hpos : ∀ n : Nat, ∀ i ≤ (P n).natDegree, 0 < (P n).coeff i)
    (hineq : ∀ n : Nat, RealRooted.Kurtz.KurtzStrictInequalities (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_kurtz_sequence using
    degree := hdeg,
    positive_coeffs := hpos,
    inequalities := hineq

end Tactic
end RealRooted
