module

public import RealRooted.Tactic.LiuWang.Step

/-!
# Positive-lag Liu--Wang sequence tactics

Parser declarations and macro implementations for this Liu--Wang tactic family.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_positive_t_sequence_named)
  "rr_lw_positive_t_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_positive_t_sequence_auto_named)
  "rr_lw_positive_t_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_positive_t_sequence_realrooted_named)
  "rr_lw_positive_t_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_positive_t_sequence_realrooted_auto_named)
  "rr_lw_positive_t_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + (C c * X) * g)` for one lag step, from
`interlaces : Interlaces g f`; `interlacer_pos_lc : HasPosLeadingCoeff g`;
`source_nonneg_coeffs : HasNonnegCoeffs f`; `coeff_nonneg : 0 ≤ c`;
`target_pos_lc : HasPosLeadingCoeff F`; `recurrence : F = a * f + (C c * X) * g`;
`degree_succ : f.natDegree + 1 = F.natDegree`; and
`no_common_roots : ∀ r, f.IsRoot r → ¬ g.IsRoot r`. -/
syntax (name := rr_lw_positive_t_lag_step_named)
  "rr_lw_positive_t_lag_step" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "source_nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + X * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_positive_X_lag_sequence_named)
  "rr_lw_positive_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + X * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_positive_X_lag_sequence_realrooted_named)
  "rr_lw_positive_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `scalar_nonneg : ∀ n, 0 ≤ c n`;
`constant_nonneg : ∀ n, 0 ≤ a n`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X - C (a n)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X - C (a n)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_auto_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `scalar_nonneg : ∀ n, 0 ≤ c n`;
`constant_nonneg : ∀ n, 0 ≤ a n`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X - C (a n)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "scalar_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X - C (a n)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto_named)
  "rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`; `root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(a n)`; `recurrence
: ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_positive_affine_lag_sequence_named)
  "rr_lw_positive_affine_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(a n)`; `recurrence : ∀ n, P (n + 2) = A n * P (n +
1) + (C (c n) * (C (a n) + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_positive_affine_lag_sequence_auto_named)
  "rr_lw_positive_affine_lag_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`; `root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(a n)`; `recurrence
: ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_named)
  "rr_lw_positive_affine_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(a n)`; `recurrence : ∀ n, P (n + 2) = A n * P (n +
1) + (C (c n) * (C (a n) + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_auto_named)
  "rr_lw_positive_affine_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`;
`shift_nonneg : ∀ n, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n)))`; `recurrence : ∀ n, P (n +
2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_positive_affine_lag_sequence_shift_nonneg_named)
  "rr_lw_positive_affine_lag_sequence_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`shift_nonneg : ∀ n, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n)))`; `recurrence : ∀ n, P (n +
2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_positive_affine_lag_sequence_shift_nonneg_auto_named)
  "rr_lw_positive_affine_lag_sequence_shift_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`;
`shift_nonneg : ∀ n, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n)))`; `recurrence : ∀ n, P (n +
2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_named)
  "rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`shift_nonneg : ∀ n, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n)))`; `recurrence : ∀ n, P (n +
2) = A n * P (n + 1) + (C (c n) * (C (a n) + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto_named)
  "rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(a n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_add_X_lag_sequence_named)
  "rr_lw_C_add_X_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(a n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_add_X_lag_sequence_realrooted_named)
  "rr_lw_C_add_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`shift_nonneg : ∀ n, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n)))`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_add_X_lag_sequence_shift_nonneg_named)
  "rr_lw_C_add_X_lag_sequence_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`shift_nonneg : ∀ n, HasNonnegCoeffs ((P (n + 1)).comp (X - C (a n)))`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (a n) + X) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg_named)
  "rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "shift_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (X * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (X * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (X * (1 - X) * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (X * (1 - X) * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name :=
    rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (X - X ^ 3) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_X_sub_X_pow_three_lag_sequence_nonneg_named)
  "rr_lw_X_sub_X_pow_three_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (X - X ^ 3) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_named)
  "rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`; `recurrence : ∀ n, P (n + 2) = A n * P (n +
1) + (C (c n) * X * (1 - X) * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 - X) * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`; `recurrence : ∀ n, P (n + 2) = A n * P (n +
1) + (C (c n) * X * (1 - X) * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name :=
    rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * X * (1 - X) * (1 + X)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name :=
    rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * (X - X ^ 3)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * (X - X ^ 3)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * (X - X ^ 3)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (C (c n) * (X - X ^ 3)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The nonnegativity of the scalar
coefficients is closed row by row by `rr_lw_active_nonneg_at`. -/
syntax (name :=
    rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto_named)
  "rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "root_lower" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_positive_t_lag_step using
        interlaces := $hInter:term,
        interlacer_pos_lc := $hg_pos:term,
        source_nonneg_coeffs := $hf_nonneg:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_positive_t_lag_of_nonneg_coeffs_of_recurrence
          $hInter $hg_pos $hf_nonneg $hc $hrec $hF_pos $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_t_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_positive_t_lag_sequence
          $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_t_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_positive_t_lag_sequence
          $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec $hdeg_succ
          $hno)
  | `(tactic|
      rr_lw_positive_t_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_positive_t_lag_sequence
            $hbase $hpos $hnonneg $hc $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_t_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_positive_t_lag_sequence
            $hbase $hpos $hnonneg rr_lw_active_nonneg $hrec
            $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_positive_X_lag_sequence
          $hbase $hpos $hnonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_positive_X_lag_sequence
            $hbase $hpos $hnonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        constant_nonneg := $ha:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_C_mul_X_sub_C_lag_sequence
          $hbase $hpos $hnonneg $hc $ha $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_C_mul_X_sub_C_lag_sequence
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        scalar_nonneg := $hc:term,
        constant_nonneg := $ha:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_sub_C_lag_sequence
            $hbase $hpos $hnonneg $hc $ha $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_C_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_sub_C_lag_sequence
            $hbase $hpos $hnonneg ?_ ?_ $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_positive_affine_lag_sequence
          $hbase $hpos $hc $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_positive_affine_lag_sequence
            $hbase $hpos ?_ $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_positive_affine_lag_sequence
            $hbase $hpos $hc $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_positive_affine_lag_sequence
            $hbase $hpos ?_ $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_positive_affine_lag_sequence_of_shift_nonneg_coeffs
          $hbase $hpos $hc $hshift_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_shift_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_positive_affine_lag_sequence_of_shift_nonneg_coeffs
            $hbase $hpos ?_ $hshift_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_positive_affine_lag_sequence_of_shift_nonneg_coeffs
            $hbase $hpos $hc $hshift_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_positive_affine_lag_sequence_realrooted_shift_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_positive_affine_lag_sequence_of_shift_nonneg_coeffs
            $hbase $hpos ?_ $hshift_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_add_X_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_C_add_X_lag_sequence
          $hbase $hpos $hroot_upper $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_add_X_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_upper := $hroot_upper:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_C_add_X_lag_sequence
            $hbase $hpos $hroot_upper $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_add_X_lag_sequence_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_C_add_X_lag_sequence_of_shift_nonneg_coeffs
          $hbase $hpos $hshift_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_add_X_lag_sequence_realrooted_shift_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        shift_nonneg := $hshift_nonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_C_add_X_lag_sequence_of_shift_nonneg_coeffs
            $hbase $hpos $hshift_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_X_one_sub_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          LiuWang.strictInterl_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (LiuWang.isRealRooted_of_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_X_sub_X_pow_three_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_X_sub_X_pow_three_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          LiuWang.strictInterl_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (LiuWang.strictInterl_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (LiuWang.isRealRooted_of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_one_sub_X_one_add_X_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (LiuWang.isRealRooted_of_C_mul_X_mul_one_sub_X_mul_one_add_X_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LiuWang.strictInterl_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_refine_active_nonneg_seq
          (RealRooted.LiuWang.strictInterl_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        coeff_nonneg := $hc:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hc $hroot_lower $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_C_mul_X_sub_X_pow_three_lag_sequence_realrooted_nonneg_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_exact_realrooted_active_nonneg_seq
          (RealRooted.LiuWang.isRealRooted_of_C_mul_X_sub_X_pow_three_lag_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg ?_ $hroot_lower $hrec $hdeg_succ $hno))

end Tactic
end RealRooted
