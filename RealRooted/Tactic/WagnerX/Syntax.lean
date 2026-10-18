import RealRooted.Tactic.WagnerX.TranslatedLag

/-!
# Wagner `X`-shift tactic syntax
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Closes `StrictInterl g (X * f)` from `proper : StrictInterl f g`;
`left_nonneg : HasNonnegCoeffs f`; and `right_nonneg : HasNonnegCoeffs g`. -/
syntax (name := rr_strict_interl_mul_X)
  "rr_strict_interl_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_mul_X`: finds the three certificates in the local context by
`rr_lookup`, using `rr_base_strict_interl` and `rr_nonneg`. -/
syntax (name := rr_strict_interl_mul_X_inferred)
  "rr_strict_interl_mul_X" : tactic

/-- Closes `StrictInterl (X * f) (X * g)` from `proper : StrictInterl f g`;
`left_nonneg : HasNonnegCoeffs f`; and `right_nonneg : HasNonnegCoeffs g`. -/
syntax (name := rr_strict_interl_mul_X_both)
  "rr_strict_interl_mul_X_both" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_mul_X_both`: finds the three certificates in the local context by
`rr_lookup`, using `rr_base_strict_interl` and `rr_nonneg`. -/
syntax (name := rr_strict_interl_mul_X_both_inferred)
  "rr_strict_interl_mul_X_both" : tactic

/-- Closes `StrictInterl g ((C c * X) * f)` from `proper : StrictInterl f g`;
`left_nonneg : HasNonnegCoeffs f`; `right_nonneg : HasNonnegCoeffs g`; and `coeff_ne : c ≠ 0`. -/
syntax (name := rr_strict_interl_C_mul_X)
  "rr_strict_interl_C_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "coeff_ne" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_C_mul_X` with `coeff_pos : 0 < c` in place of
`coeff_ne : c ≠ 0`. -/
syntax (name := rr_strict_interl_C_mul_X_pos)
  "rr_strict_interl_C_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "coeff_pos" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_C_mul_X`: takes `coeff_ne : c ≠ 0` from the `using` clause and
finds the other certificates in the local context by `rr_lookup`. -/
syntax (name := rr_strict_interl_C_mul_X_inferred)
  "rr_strict_interl_C_mul_X" " using "
    "coeff_ne" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_C_mul_X_pos`: takes `coeff_pos : 0 < c` from the `using` clause
and finds the other certificates in the local context by `rr_lookup`. -/
syntax (name := rr_strict_interl_C_mul_X_pos_inferred)
  "rr_strict_interl_C_mul_X" " using "
    "coeff_pos" ":=" term :
  tactic

/-- Closes `StrictInterl (X * f.derivative) (X * f)` from `splits : f.Splits`,
`degree_two : 2 ≤ f.natDegree` and `nonneg_coeffs : HasNonnegCoeffs f`. -/
syntax (name := rr_strict_interl_X_derivative_X_self)
  "rr_strict_interl_X_derivative_X_self" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "nonneg_coeffs" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_X_derivative_X_self`: finds the three certificates in the local
context by `rr_lookup`, using `rr_degree` and `rr_nonneg`. -/
syntax (name := rr_strict_interl_X_derivative_X_self_inferred)
  "rr_strict_interl_X_derivative_X_self" : tactic

/-- Closes `StrictInterl g (X * (C c * g.derivative + C a * f))` from `proper : StrictInterl f g`;
`left_nonneg : HasNonnegCoeffs f`; `right_nonneg : HasNonnegCoeffs g`;
`degree_two : 2 ≤ g.natDegree`; `lag_coeff_pos : 0 < a`; and `derivative_coeff_pos : 0 < c`. -/
syntax (name := rr_strict_interl_wagner_derivative_gap_lag)
  "rr_strict_interl_wagner_derivative_gap_lag" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_wagner_derivative_gap_lag`: finds all certificates in the local
context by `rr_lookup`, using `rr_base_strict_interl`, `rr_nonneg` and `rr_degree`, and proves the
coefficient positivity by `rr_wagner_pos` if needed. -/
syntax (name := rr_strict_interl_wagner_derivative_gap_lag_inferred)
  "rr_strict_interl_wagner_derivative_gap_lag" : tactic

/-- Closes `StrictInterl g p` from `proper : StrictInterl f g`; `left_nonneg : HasNonnegCoeffs f`;
`right_nonneg : HasNonnegCoeffs g`; `degree_two : 2 ≤ g.natDegree`; `lag_coeff_pos : 0 < a`;
`derivative_coeff_pos : 0 < c`; `denom_pos : 0 < d`; and
`recurrence : C d * p = X * (C c * g.derivative + C a * f)`. -/
syntax (name := rr_strict_interl_wagner_derivative_gap_lag_den)
  "rr_strict_interl_wagner_derivative_gap_lag_den" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` from `base : StrictInterl (P 0) (P 1)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `degree_two : ∀ n, 2 ≤ (P (n + 1)).natDegree`;
`lag_coeff_pos : ∀ n, 0 < a n`; `derivative_coeff_pos : ∀ n, 0 < c n`; and `recurrence : ∀ n, P (n +
2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)`. -/
syntax (name := rr_strict_interl_wagner_derivative_gap_lag_sequence)
  "rr_strict_interl_wagner_derivative_gap_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `base : StrictInterl (P 0) (P 1)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `degree_two : ∀ n, 2 ≤ (P (n + 1)).natDegree`;
`lag_coeff_pos : ∀ n, 0 < a n`; `derivative_coeff_pos : ∀ n, 0 < c n`; and `recurrence : ∀ n, P (n +
2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)`. -/
syntax (name := rr_strict_interl_wagner_derivative_gap_lag_sequence_realrooted)
  "rr_strict_interl_wagner_derivative_gap_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` from `base : StrictInterl (P 0) (P 1)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `degree_two : ∀ n, 2 ≤ (P (n + 1)).natDegree`;
`lag_coeff_pos : ∀ n, 0 < a n`; `derivative_coeff_pos : ∀ n, 0 < c n`; `denom_pos : ∀ n, 0 < d n`;
and `recurrence : ∀ n, C (d n) * P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P
n)`. -/
syntax (name := rr_strict_interl_wagner_derivative_gap_lag_sequence_den)
  "rr_strict_interl_wagner_derivative_gap_lag_sequence_den" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `base : StrictInterl (P 0) (P 1)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `degree_two : ∀ n, 2 ≤ (P (n + 1)).natDegree`;
`lag_coeff_pos : ∀ n, 0 < a n`; `derivative_coeff_pos : ∀ n, 0 < c n`; `denom_pos : ∀ n, 0 < d n`;
and `recurrence : ∀ n, C (d n) * P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P
n)`. -/
syntax (name := rr_strict_interl_wagner_derivative_gap_lag_sequence_den_realrooted)
  "rr_strict_interl_wagner_derivative_gap_lag_sequence_den_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `StrictInterl g (C a * g + (C c * X) * f)` from `proper : StrictInterl f g`;
`left_nonneg : HasNonnegCoeffs f`; and `right_nonneg : HasNonnegCoeffs g`;
`current_coeff_pos : 0 < a`; and `lag_coeff_nonneg : 0 ≤ c`. -/
syntax (name := rr_strict_interl_pos_X_lag_combo)
  "rr_strict_interl_pos_X_lag_combo" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_pos_X_lag_combo` with `lag_coeff_pos : 0 < c` in place of
`lag_coeff_nonneg : 0 ≤ c`. -/
syntax (name := rr_strict_interl_pos_X_lag_combo_lag_pos)
  "rr_strict_interl_pos_X_lag_combo" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` from `base : StrictInterl (P 0) (P 1)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `current_coeff_pos : ∀ n, 0 < a n`;
`lag_coeff_nonneg : ∀ n, 0 ≤ c n`; and
`recurrence : ∀ n, P (n + 2) = C (a n) * P (n + 1) + (C (c n) * X) * P n`. -/
syntax (name := rr_strict_interl_pos_X_lag_sequence)
  "rr_strict_interl_pos_X_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, (P n).natDegree = d + n / 2 ∧ HasPosLeadingCoeff (P n)` (up to `simpa`) from
`base_zero : (P 0).natDegree = d ∧ HasPosLeadingCoeff (P 0)`;
`base_one : (P 1).natDegree = d ∧ HasPosLeadingCoeff (P 1)`; `current_coeff_pos : ∀ n, 0 < a n`;
`lag_coeff_pos : ∀ n, 0 < c n`; and
`recurrence : ∀ n, P (n + 2) = C (a n) * P (n + 1) + (C (c n) * X) * P n`. -/
syntax (name := rr_natDegree_pos_X_lag_sequence)
  "rr_natDegree_pos_X_lag_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Shifted form of `rr_natDegree_pos_X_lag_sequence`: closes
`∀ n, (P n).natDegree = d + (n + 1) / 2 ∧ HasPosLeadingCoeff (P n)` (up to `simpa`), where
`base_one` now states `(P 1).natDegree = d + 1`. -/
syntax (name := rr_natDegree_pos_X_lag_sequence_shifted)
  "rr_natDegree_pos_X_lag_sequence_shifted" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_pos_X_lag_sequence` that takes only `base`, `nonneg_coeffs` and
`recurrence`: the coefficients `a` and `c` are inferred from `recurrence` (first trying the constant
coefficients `1`) and their sign conditions are closed by `rr_wagner_pos_seq`. -/
syntax (name := rr_strict_interl_pos_X_lag_sequence_auto)
  "rr_strict_interl_pos_X_lag_sequence_auto" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Automatic scalar-side-condition frontend for a positive-`X` lag sequence
with explicitly supplied current and lag coefficient functions. -/
syntax (name := rr_strict_interl_pos_X_lag_coeff_sequence_auto)
  "rr_strict_interl_pos_X_lag_coeff_sequence_auto" " using "
    "current_coeff" ":=" term ","
    "lag_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `base : StrictInterl (P 0) (P 1)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `current_coeff_pos : ∀ n, 0 < a n`;
`lag_coeff_nonneg : ∀ n, 0 ≤ c n`; and
`recurrence : ∀ n, P (n + 2) = C (a n) * P (n + 1) + (C (c n) * X) * P n`. -/
syntax (name := rr_strict_interl_pos_X_lag_sequence_realrooted)
  "rr_strict_interl_pos_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_pos_X_lag_sequence_realrooted` that takes only `base`,
`nonneg_coeffs` and `recurrence`: the coefficients `a` and `c` are inferred from `recurrence` (first
trying the constant coefficients `1`) and their sign conditions are closed by
`rr_wagner_pos_seq`. -/
syntax (name := rr_strict_interl_pos_X_lag_sequence_realrooted_auto)
  "rr_strict_interl_pos_X_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Real-rootedness endpoint for
`rr_strict_interl_pos_X_lag_coeff_sequence_auto`. -/
syntax (name := rr_strict_interl_pos_X_lag_coeff_sequence_realrooted_auto)
  "rr_strict_interl_pos_X_lag_coeff_sequence_realrooted_auto" " using "
    "current_coeff" ":=" term ","
    "lag_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, (P n).natDegree = d + n / 2 ∧ HasPosLeadingCoeff (P n)` (up to `simpa`) for the
recurrence `P (n + 2) = C (a n) * P (n + 1) + (C (c n) * (X - C r)) * P n`, from `shift : r`;
`base_zero : (P 0).natDegree = d ∧ HasPosLeadingCoeff (P 0)`;
`base_one : (P 1).natDegree = d ∧ HasPosLeadingCoeff (P 1)`; `current_coeff_pos : ∀ n, 0 < a n`;
`lag_coeff_pos : ∀ n, 0 < c n`; and `recurrence`. -/
syntax (name := rr_natDegree_pos_X_sub_C_lag_sequence)
  "rr_natDegree_pos_X_sub_C_lag_sequence" " using "
    "shift" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Shifted form of `rr_natDegree_pos_X_sub_C_lag_sequence`: closes
`∀ n, (P n).natDegree = d + (n + 1) / 2 ∧ HasPosLeadingCoeff (P n)` (up to `simpa`), where
`base_one` now states `(P 1).natDegree = d + 1`. -/
syntax (name := rr_natDegree_pos_X_sub_C_lag_sequence_shifted)
  "rr_natDegree_pos_X_sub_C_lag_sequence_shifted" " using "
    "shift" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` from `shift : r`;
`base : StrictInterl (P 0) (P 1)`;
`shift_nonneg_coeffs : ∀ n, HasNonnegCoeffs ((P n).comp (X + C r))`;
`current_coeff_pos : ∀ n, 0 < a n`; `lag_coeff_nonneg : ∀ n, 0 ≤ c n`; and `recurrence : ∀ n, P (n +
2) = C (a n) * P (n + 1) + (C (c n) * (X - C r)) * P n`. -/
syntax (name := rr_strict_interl_pos_X_sub_C_lag_sequence)
  "rr_strict_interl_pos_X_sub_C_lag_sequence" " using "
    "shift" ":=" term ","
    "base" ":=" term ","
    "shift_nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `shift : r`; `base : StrictInterl (P 0) (P 1)`;
`shift_nonneg_coeffs : ∀ n, HasNonnegCoeffs ((P n).comp (X + C r))`;
`current_coeff_pos : ∀ n, 0 < a n`; `lag_coeff_nonneg : ∀ n, 0 ≤ c n`; and `recurrence : ∀ n, P (n +
2) = C (a n) * P (n + 1) + (C (c n) * (X - C r)) * P n`. -/
syntax (name := rr_strict_interl_pos_X_sub_C_lag_sequence_realrooted)
  "rr_strict_interl_pos_X_sub_C_lag_sequence_realrooted" " using "
    "shift" ":=" term ","
    "base" ":=" term ","
    "shift_nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_pos_X_sub_C_lag_sequence_realrooted` that takes only `shift`,
`base`, `shift_nonneg_coeffs` and `recurrence`; the coefficient sign conditions are closed by
`rr_wagner_pos_seq`. -/
syntax (name := rr_strict_interl_pos_X_sub_C_lag_sequence_realrooted_auto)
  "rr_strict_interl_pos_X_sub_C_lag_sequence_realrooted_auto" " using "
    "shift" ":=" term ","
    "base" ":=" term ","
    "shift_nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_pos_X_lag_sequence` with lag coefficient `c n = 1`: takes
`current_coeff : a`, `base`, `nonneg_coeffs` and `recurrence`, and closes the sign conditions by
`rr_wagner_pos_seq`. -/
syntax (name := rr_strict_interl_pos_X_unit_lag_sequence_auto)
  "rr_strict_interl_pos_X_unit_lag_sequence_auto" " using "
    "current_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_pos_X_lag_sequence_realrooted` with lag coefficient `c n = 1`:
takes `current_coeff : a`, `base`, `nonneg_coeffs` and `recurrence`, and closes the sign conditions
by `rr_wagner_pos_seq`. -/
syntax (name := rr_strict_interl_pos_X_unit_lag_sequence_realrooted_auto)
  "rr_strict_interl_pos_X_unit_lag_sequence_realrooted_auto" " using "
    "current_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_pos_X_lag_sequence` with equal current and lag coefficients
`a n = c n`: takes `shared_coeff : c`, `base`, `nonneg_coeffs` and `recurrence`, and closes the sign
conditions by `rr_wagner_pos_seq`. -/
syntax (name := rr_strict_interl_pos_X_same_coeff_sequence_auto)
  "rr_strict_interl_pos_X_same_coeff_sequence_auto" " using "
    "shared_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_pos_X_lag_sequence_realrooted` with equal current and lag
coefficients `a n = c n`: takes `shared_coeff : c`, `base`, `nonneg_coeffs` and `recurrence`, and
closes the sign conditions by `rr_wagner_pos_seq`. -/
syntax (name := rr_strict_interl_pos_X_same_coeff_sequence_realrooted_auto)
  "rr_strict_interl_pos_X_same_coeff_sequence_realrooted_auto" " using "
    "shared_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

/-- Closes a positivity side goal for a coefficient by `rr_side_pos`. -/
syntax (name := rr_wagner_pos) "rr_wagner_pos" : tactic

/-- Term form of `rr_wagner_pos`: elaborates to `by rr_wagner_pos`. -/
syntax (name := rr_wagner_pos_term) "rr_wagner_pos_term" : term

/-- Term `fun n => by rr_wagner_pos`: positivity of a coefficient at every row. -/
syntax (name := rr_wagner_pos_seq) "rr_wagner_pos_seq" : term

/-- Term `fun n => by simpa using hrec n`, normalizing a recurrence certificate `hrec` for every
row. -/
syntax (name := rr_wagner_recurrence_seq) "rr_wagner_recurrence_seq " term : term

macro_rules
  | `(tactic| rr_wagner_pos) =>
      `(tactic| rr_side_pos)
  | `(rr_wagner_pos_term) =>
      `(by rr_wagner_pos)
  | `(rr_wagner_pos_seq) =>
      `(fun n => by rr_wagner_pos)
  | `(rr_wagner_recurrence_seq $hrec:term) =>
      `(fun n => by simpa using $hrec n)



end Tactic
end RealRooted
