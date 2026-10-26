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

/-- Positional form of `rr_favard_const using ...`: the same arguments as the named form, in the
order `alpha`, `beta`, `beta_pos`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_const)
  "rr_favard_const" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

/-- Closes the Favard conclusion for `P`, namely `∀ n, StrictInterl (P n) (P (n + 1))`,
`∀ n, P n ≠ 0 ∧ (P n).Splits` or `∀ n, P n ≠ 0`, as the goal states, for the constant-coefficient
recurrence `P (n + 2) = (X - C α) * P (n + 1) - C β * P n`. Arguments: the reals `alpha` and `beta`,
`beta_pos : 0 < β`, `base_zero : P 0 = 1`, `base_one : P 1 = X - C α` and `step`, the recurrence. -/
syntax (name := rr_favard_const_named)
  "rr_favard_const" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_const` that proves `beta_pos : 0 < β` by `rr_positivity_term`; the other
arguments are as for `rr_favard_const`. -/
syntax (name := rr_favard_const_auto_named)
  "rr_favard_const_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_const` for `β = 1`: `beta` and `beta_pos` are omitted, and `base_one` and
`step` are normalized by `simpa` before use. The arguments are `alpha`, `base_zero`, `base_one` and
`step`. -/
syntax (name := rr_favard_const_unit_named)
  "rr_favard_const_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Positional form of `rr_favard_const_unit using ...`: the same arguments as the named form, in
the order `alpha`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_const_unit)
  "rr_favard_const_unit" " using " term ", " term ", " term ", " term :
  tactic

/-- Positional form of `rr_favard_param using ...`: the same arguments as the named form, in the
order `alpha`, `beta`, `beta_pos`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_param)
  "rr_favard_param" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

/-- Closes the Favard conclusion for `P`, namely `∀ n, StrictInterl (P n) (P (n + 1))`,
`∀ n, P n ≠ 0 ∧ (P n).Splits` or `∀ n, P n ≠ 0`, as the goal states, for the parameterized
recurrence `P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n` with `α β : ℕ → ℝ`.
Arguments: `alpha`, `beta`, `beta_pos : ∀ n, 0 < β (n + 1)`, `base_zero : P 0 = 1`,
`base_one : P 1 = X - C (α 0)` and `step`, the recurrence. -/
syntax (name := rr_favard_param_named)
  "rr_favard_param" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_param` that proves `beta_pos` by `rr_positivity_seq_term` and normalizes
`base_one` and `step` by `dsimp` and `simp` before use; the other arguments are as for
`rr_favard_param`. -/
syntax (name := rr_favard_param_auto_named)
  "rr_favard_param_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_param` for `β n = 1` for every `n`: `beta` and `beta_pos` are omitted, and
the positivity and normalization are handled as in `rr_favard_param_auto`. The arguments are
`alpha`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_param_unit_named)
  "rr_favard_param_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Positional form of `rr_favard_param_unit using ...`: the same arguments as the named form, in
the order `alpha`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_param_unit)
  "rr_favard_param_unit" " using " term ", " term ", " term ", " term :
  tactic

/-- Positional form of `rr_favard_affine_const using ...`: the same arguments as the named form, in
the order `slope`, `alpha`, `beta`, `slope_pos`, `beta_pos`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_affine_const)
  "rr_favard_affine_const" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term ", " term :
  tactic

/-- Closes the Favard conclusion for `P`, namely `∀ n, StrictInterl (P n) (P (n + 1))`,
`∀ n, P n ≠ 0 ∧ (P n).Splits` or `∀ n, P n ≠ 0`, as the goal states, for the positive-slope
constant-coefficient recurrence `P (n + 2) = (C s * X - C α) * P (n + 1) - C β * P n`. Arguments:
the reals `slope` (`s`), `alpha` and `beta`, `slope_pos : 0 < s`, `beta_pos : 0 < β`,
`base_zero : P 0 = 1`, `base_one : P 1 = C s * X - C α` and `step`, the recurrence. -/
syntax (name := rr_favard_affine_const_named)
  "rr_favard_affine_const" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_affine_const` that proves `slope_pos` and `beta_pos` by
`rr_positivity_term`; the other arguments are as for `rr_favard_affine_const`. -/
syntax (name := rr_favard_affine_const_auto_named)
  "rr_favard_affine_const_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_affine_const` for `β = 1`: `beta`, `slope_pos` and `beta_pos` are omitted
(positivity is proved automatically), and `base_one` and `step` are normalized by `simpa` before
use. The arguments are `slope`, `alpha`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_affine_const_unit_named)
  "rr_favard_affine_const_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Positional form of `rr_favard_affine_const_unit using ...`: the same arguments as the named
form, in the order `slope`, `alpha`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_affine_const_unit)
  "rr_favard_affine_const_unit" " using " term ", " term ", " term ", "
    term ", " term :
  tactic

/-- Row-sign form of `rr_favard_affine_const`: closes the Favard conclusion for `P`, namely
`∀ n, StrictInterl (P n) (P (n + 1))`, `∀ n, P n ≠ 0 ∧ (P n).Splits` or `∀ n, P n ≠ 0`, as the goal
states, for the recurrence `P (n + 2) = -(C s * X - C α) * P (n + 1) - C β * P n` with
`P 1 = -(C s * X - C α)`. The arguments are the same as for `rr_favard_affine_const`. -/
syntax (name := rr_favard_affine_const_row_sign_named)
  "rr_favard_affine_const_row_sign" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_affine_const_row_sign` that proves `slope_pos` and `beta_pos` by
`rr_positivity_term`; the other arguments are as for the base tactic. -/
syntax (name := rr_favard_affine_const_row_sign_auto_named)
  "rr_favard_affine_const_row_sign_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Version of `rr_favard_affine_const_row_sign` for `s = 1` and `β = 1`: only `alpha`, `base_zero`,
`base_one` and `step` are given, and `base_one` and `step` are normalized by `simpa` before use. -/
syntax (name := rr_favard_const_row_sign_unit_named)
  "rr_favard_const_row_sign_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

/-- Positional form of `rr_favard_const_row_sign_unit using ...`: the same arguments as the named
form, in the order `alpha`, `base_zero`, `base_one` and `step`. -/
syntax (name := rr_favard_const_row_sign_unit)
  "rr_favard_const_row_sign_unit" " using " term ", " term ", " term ", " term :
  tactic

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

/-- Version of `rr_favard_affine_param` that proves `slope_pos` and `beta_pos` by
`rr_positivity_seq_term` and normalizes `base_one` and `step` by `dsimp` and `simp` before use; the
other arguments are as for `rr_favard_affine_param`. -/
syntax (name := rr_favard_affine_param_auto_named)
  "rr_favard_affine_param_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
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
