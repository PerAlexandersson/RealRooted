import RealRooted.Tactic.ScalarDen

/-!
# Shared OEIS tactic syntax

Small OEIS-facing aliases for the scalar-denominator certificate tactics.
Certificate-family frontends import this module rather than each duplicating
these term elaborators.
-/

namespace RealRooted
namespace Tactic

macro "rr_oeis_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

macro "rr_oeis_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

macro "rr_oeis_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

syntax (name := rr_oeis_active_den_all_term)
  "rr_oeis_active_den_all_term" : term

syntax (name := rr_oeis_coeff_at_term)
  "rr_oeis_coeff_at_term " term : term

syntax (name := rr_oeis_coeff_all_term)
  "rr_oeis_coeff_all_term" : term

macro_rules
  | `(rr_oeis_active_den_all_term) =>
      `(by rr_oeis_active_den_all)
  | `(rr_oeis_coeff_at_term $n:term) =>
      `(by rr_oeis_coeff_at $n)
  | `(rr_oeis_coeff_all_term) =>
      `(by rr_oeis_coeff_all)

end Tactic
end RealRooted
