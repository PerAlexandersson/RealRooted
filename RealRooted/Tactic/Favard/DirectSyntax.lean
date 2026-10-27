module

public import RealRooted.Tactic.Favard.Basic

/-!
# Favard tactic direct syntax

Parser declarations for direct monic and positive-slope affine Favard certificates.
-/

public section

namespace RealRooted
namespace Tactic

/-- Positional form of `rr_favard using ...`: the same arguments as the named form, in the order
`recurrence` and `beta_pos`. -/
syntax (name := rr_favard) "rr_favard" " using " term ", " term : tactic

/-- Bare form of `rr_favard`: takes `recurrence` and `beta_pos` from the local context by
`assumption`. -/
syntax (name := rr_favard_inferred) "rr_favard" : tactic

/-- Closes the Favard conclusion for `P`, namely `∀ n, StrictInterl (P n) (P (n + 1))`,
`∀ n, P n ≠ 0 ∧ (P n).Splits` or `∀ n, P n ≠ 0`, as the goal states, or the generalized Sturm
sequence statement of the Favard theorem, for a monic three-term recurrence. Arguments:
`recurrence : SatisfiesFavardRecurrence P α β` and `beta_pos : ∀ n, 0 < β (n + 1)`. -/
syntax (name := rr_favard_named)
  "rr_favard" " using "
    "recurrence" ":=" term ","
    "beta_pos" ":=" term :
  tactic

/-- Version of `rr_favard` that proves `beta_pos` itself, by `rr_positivity_seq` on the side goal;
the only argument is `recurrence : SatisfiesFavardRecurrence P α β`. -/
syntax (name := rr_favard_auto_named)
  "rr_favard_auto" " using "
    "recurrence" ":=" term :
  tactic

/-- Bare form of `rr_favard_auto`: takes `recurrence` from the local context by `assumption`. -/
syntax (name := rr_favard_auto_inferred) "rr_favard_auto" : tactic

/-- Positional form of `rr_favard_affine_param using ...`: the same arguments as the named form, in
the order `slope`, `alpha`, `beta`, `slope_pos`, `beta_pos`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_affine_param)
  "rr_favard_affine_param" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term ", " term :
  tactic

/-- Closes `∀ n, Interlaces (P n) (P (n + 1))` or the Favard conclusion for `P`, namely
`∀ n, StrictInterl (P n) (P (n + 1))`, `∀ n, P n ≠ 0 ∧ (P n).Splits` or `∀ n, P n ≠ 0`, as the goal
states, for the positive-slope parameterized recurrence
`P (n + 2) = (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n`. Arguments:
`slope`, `alpha` and `beta` (all `ℕ → ℝ`), `slope_pos : ∀ n, 0 < s n`,
`beta_pos : ∀ n, 0 < β (n + 1)`, `base_zero : P 0 = 1`, `base_one : P 1 = C (s 0) * X - C (α 0)` and
`step`. -/
syntax (name := rr_favard_affine_param_named)
  "rr_favard_affine_param" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_affine_param` that takes only `slope`, `alpha`, `beta` and `step`:
`slope_pos`, `beta_pos`, `base_zero` and `base_one` are found in the local context by lookup, and
the plain recurrence is tried first, then the row-sign one of `rr_favard_affine_param_row_sign`. -/
syntax (name := rr_favard_affine_param_infer_named)
  "rr_favard_affine_param_infer" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "step" ":=" term :
  tactic


end Tactic
end RealRooted
