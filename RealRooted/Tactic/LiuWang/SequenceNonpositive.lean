module

public import RealRooted.Tactic.LiuWang.Step

/-!
# Nonpositive-lag Liu--Wang sequence tactics

Parser declarations and macro implementations for this Liu--Wang tactic family.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`lag_nonpos : ∀ n r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + B n * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_nonpos_lag_sequence_named)
  "rr_lw_nonpos_lag_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` from
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + B n * P n`, leaving the other certificates of
`rr_lw_nonpos_lag_sequence` to be found by `rr_lookup`. -/
syntax (name := rr_lw_nonpos_lag_sequence_inferred_of_recurrence)
  "rr_lw_nonpos_lag_sequence" " using " "recurrence" ":=" term : tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`lag_nonpos : ∀ n r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + B n * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_nonpos_lag_sequence_realrooted_named)
  "rr_lw_nonpos_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + B n * P n`, leaving the other certificates of
`rr_lw_nonpos_lag_sequence_realrooted` to be found by `rr_lookup`. -/
syntax (name := rr_lw_nonpos_lag_sequence_realrooted_inferred_of_recurrence)
  "rr_lw_nonpos_lag_sequence_realrooted" " using " "recurrence" ":=" term : tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`lag : B`, the lag coefficient sequence `B : ℕ → ℝ[X]`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + B n * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The sign condition on `lag` at
the roots is proved by `rr_sign`. -/
syntax (name := rr_lw_global_nonpos_sequence_auto_named)
  "rr_lw_global_nonpos_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `lag : B`,
the lag coefficient sequence `B : ℕ → ℝ[X]`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + B n * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The sign condition on `lag` at
the roots is proved by `rr_sign`. -/
syntax (name := rr_lw_global_nonpos_sequence_realrooted_auto_named)
  "rr_lw_global_nonpos_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`lag : B`, the lag coefficient sequence `B : ℕ → ℝ[X]`; `den_nonzero : ∀ n, d n ≠ 0`;
`raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1) + B n * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The sign condition on `lag` at
the roots is proved by `rr_sign`. -/
syntax (name := rr_lw_global_nonpos_sequence_den_auto_named)
  "rr_lw_global_nonpos_sequence_den_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `lag : B`,
the lag coefficient sequence `B : ℕ → ℝ[X]`; `den_nonzero : ∀ n, d n ≠ 0`; `raw_recurrence : ∀ n, C
(d n) * P (n + 2) = C (d n) * (A n * P (n + 1) + B n * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The sign condition on `lag` at
the roots is proved by `rr_sign`. -/
syntax (name := rr_lw_global_nonpos_sequence_den_realrooted_auto_named)
  "rr_lw_global_nonpos_sequence_den_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`lag_nonpos : ∀ n r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0`; `den_nonzero : ∀ n, d n ≠ 0`;
`raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1) + B n * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_nonpos_lag_sequence_den_named)
  "rr_lw_nonpos_lag_sequence_den" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`lag_nonpos : ∀ n r, (P (n + 1)).IsRoot r → (B n).eval r ≤ 0`; `den_nonzero : ∀ n, d n ≠ 0`;
`raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1) + B n * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_nonpos_lag_sequence_den_realrooted_named)
  "rr_lw_nonpos_lag_sequence_den_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "lag_nonpos" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`; `recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_negative_const_sequence_named)
  "rr_lw_negative_const_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The omitted certificates are
supplied automatically: `coeff_nonneg` is closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_const_sequence_auto_named)
  "rr_lw_negative_const_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`; `recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_negative_const_sequence_realrooted_named)
  "rr_lw_negative_const_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (-(C (c n))) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The omitted certificates are
supplied automatically: `coeff_nonneg` is closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_const_sequence_realrooted_auto_named)
  "rr_lw_negative_const_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`; `recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_negative_const_C_neg_sequence_named)
  "rr_lw_negative_const_C_neg_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The omitted certificates are
supplied automatically: `coeff_nonneg` is closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_const_C_neg_sequence_auto_named)
  "rr_lw_negative_const_C_neg_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`; `recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_negative_const_C_neg_sequence_realrooted_named)
  "rr_lw_negative_const_C_neg_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + C (-(c n)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The omitted certificates are
supplied automatically: `coeff_nonneg` is closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_const_C_neg_sequence_realrooted_auto_named)
  "rr_lw_negative_const_C_neg_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`; `recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (q
n) ^ 2) * P n`; `degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_negative_square_sequence_named)
  "rr_lw_negative_square_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The omitted certificates are
supplied automatically: `coeff_nonneg` is closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_square_sequence_auto_named)
  "rr_lw_negative_square_sequence_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff_nonneg : ∀ n, 0 ≤ c n`; `recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (q
n) ^ 2) * P n`; `degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_negative_square_sequence_realrooted_named)
  "rr_lw_negative_square_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `recurrence
: ∀ n, P (n + 2) = A n * P (n + 1) + (-(C (c n)) * (q n) ^ 2) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The omitted certificates are
supplied automatically: `coeff_nonneg` is closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_square_sequence_realrooted_auto_named)
  "rr_lw_negative_square_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (-((q n) ^ 2)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_negative_square_sequence_unit_named)
  "rr_lw_negative_square_sequence_unit" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`recurrence : ∀ n, P (n + 2) = A n * P (n + 1) + (-((q n) ^ 2)) * P n`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. -/
syntax (name := rr_lw_negative_square_sequence_realrooted_unit_named)
  "rr_lw_negative_square_sequence_realrooted_unit" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`den_nonzero : ∀ n, d n ≠ 0`; `coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d
n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. Here `q`, `b` and `d` are
inferred from `raw_recurrence`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_named)
  "rr_lw_negative_square_sequence_den_coeff" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `coeff_nonneg : ∀ n, 0 ≤ c n`; `raw_recurrence :
∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. Here `q`, `b` and `d` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `den_nonzero`
is closed by `rr_lw_active_den_all_term`; `coeff_eq` is closed by `rr_lw_coeff_all_term`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_scalar_named)
  "rr_lw_negative_square_sequence_den_coeff" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`square_factor : q`, the polynomial sequence `q : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence
`c : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `coeff_nonneg : ∀ n, 0 ≤ c n`; `den_nonzero : ∀ n, d n ≠ 0`;
`coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n *
P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The recurrence is normalized by
`rr_lw_raw_recurrence_seq`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_split_named)
  "rr_lw_negative_square_sequence_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`square_factor : q`, the polynomial sequence `q : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence
`c : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `coeff_nonneg : ∀ n, 0 ≤ c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C
(d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The recurrence is normalized by
`rr_lw_raw_recurrence_seq`. The omitted certificates are supplied automatically: `den_nonzero` is
closed by `rr_lw_active_den_all_term`; `coeff_eq` is closed by `rr_lw_coeff_all_term`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_split_scalar_named)
  "rr_lw_negative_square_sequence_den_coeff_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `den_nonzero : ∀ n, d n ≠ 0`;
`coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n *
P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. Here `q`, `b` and `d` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `coeff_nonneg`
is closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_auto_named)
  "rr_lw_negative_square_sequence_den_coeff_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d
n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. Here `q`, `b` and `d` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `coeff_nonneg`
is closed by `rr_lw_active_nonneg`; `den_nonzero` is closed by `rr_lw_active_den_all_term`;
`coeff_eq` is closed by `rr_lw_coeff_all_term`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_auto_active_named)
  "rr_lw_negative_square_sequence_den_coeff_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`square_factor : q`, the polynomial sequence `q : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence
`c : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `den_nonzero : ∀ n, d n ≠ 0`; `coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`;
`raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P
n)`; `degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The recurrence is normalized by
`rr_lw_raw_recurrence_seq`. The omitted certificates are supplied automatically: `coeff_nonneg` is
closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_auto_split_named)
  "rr_lw_negative_square_sequence_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Liu--Wang lag recurrence with an arbitrary
polynomial `A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`square_factor : q`, the polynomial sequence `q : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence
`c : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + C
(b n) * (-(q n) ^ 2 * P n)`; `degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The recurrence is normalized by
`rr_lw_raw_recurrence_seq`. The omitted certificates are supplied automatically: `coeff_nonneg` is
closed by `rr_lw_active_nonneg`; `den_nonzero` is closed by `rr_lw_active_den_all_term`; `coeff_eq`
is closed by `rr_lw_coeff_all_term`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_auto_split_active_named)
  "rr_lw_negative_square_sequence_den_coeff_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `coeff_nonneg : ∀ n, 0 ≤ c n`;
`den_nonzero : ∀ n, d n ≠ 0`; `coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d
n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. Here `q`, `b` and `d` are
inferred from `raw_recurrence`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `coeff_nonneg : ∀ n, 0 ≤ c n`; `raw_recurrence :
∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. Here `q`, `b` and `d` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `den_nonzero`
is closed by `rr_lw_active_den_all_term`; `coeff_eq` is closed by `rr_lw_coeff_all_term`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_scalar_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`square_factor : q`, the polynomial sequence `q : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence
`c : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `coeff_nonneg : ∀ n, 0 ≤ c n`; `den_nonzero : ∀ n, d n ≠ 0`;
`coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n *
P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The recurrence is normalized by
`rr_lw_raw_recurrence_seq`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_split_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`square_factor : q`, the polynomial sequence `q : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence
`c : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `coeff_nonneg : ∀ n, 0 ≤ c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C
(d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The recurrence is normalized by
`rr_lw_raw_recurrence_seq`. The omitted certificates are supplied automatically: `den_nonzero` is
closed by `rr_lw_active_den_all_term`; `coeff_eq` is closed by `rr_lw_coeff_all_term`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_split_scalar_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `den_nonzero : ∀ n, d n ≠ 0`;
`coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n *
P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. Here `q`, `b` and `d` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `coeff_nonneg`
is closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_auto_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d
n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P n)`;
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. Here `q`, `b` and `d` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `coeff_nonneg`
is closed by `rr_lw_active_nonneg`; `den_nonzero` is closed by `rr_lw_active_den_all_term`;
`coeff_eq` is closed by `rr_lw_coeff_all_term`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_auto_active_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`square_factor : q`, the polynomial sequence `q : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence
`c : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `den_nonzero : ∀ n, d n ≠ 0`; `coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`;
`raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + C (b n) * (-(q n) ^ 2 * P
n)`; `degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The recurrence is normalized by
`rr_lw_raw_recurrence_seq`. The omitted certificates are supplied automatically: `coeff_nonneg` is
closed by `rr_lw_active_nonneg`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    ("den_nonzero" ":=" term ",")?
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Liu--Wang lag recurrence with an arbitrary polynomial
`A n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`square_factor : q`, the polynomial sequence `q : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence
`c : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (A n * P (n + 1)) + C
(b n) * (-(q n) ^ 2 * P n)`; `degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`; and
`no_common_roots : ∀ n r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r`. The recurrence is normalized by
`rr_lw_raw_recurrence_seq`. The omitted certificates are supplied automatically: `coeff_nonneg` is
closed by `rr_lw_active_nonneg`; `den_nonzero` is closed by `rr_lw_active_den_all_term`; `coeff_eq`
is closed by `rr_lw_coeff_all_term`. -/
syntax (name := rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split_active_named)
  "rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "square_factor" ":=" term ","
    "coeff" ":=" term ","
    "raw_coeff" ":=" term ","
    "den" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_nonpos_lag_step using
        interlaces := $hInter:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term,
        lag_nonpos := $hB:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_two_of_nonpos_of_recurrence
          $hInter $hg_pos $hrec $hF_pos $hdeg_succ $hno $hB)
  | `(tactic|
      rr_lw_nonpos_lag_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_nonpos_lag_sequence
          $hbase $hpos $hB $hrec $hdeg_succ $hno)
  | `(tactic| rr_lw_nonpos_lag_sequence using recurrence := $hrec:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.LiuWang.strictInterl_nonpos_lag_sequence
            ?_ ?_ ?_ $hrec ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_nonpos_lag_sequence
            $hbase $hpos $hB $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_nonpos_lag_sequence_realrooted using recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_refine_then
          (RealRooted.LiuWang.isRealRooted_of_nonpos_lag_sequence
            ?_ ?_ ?_ $hrec ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_lw_global_nonpos_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_nonpos_lag_sequence
          (B := $B) $hbase $hpos (by
            intro n r hr
            rr_sign) $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_global_nonpos_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_nonpos_lag_sequence
            (B := $B) $hbase $hpos (by
              intro n r hr
              rr_sign) $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_den_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_lw_active_den_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_nonpos_lag_sequence_den
          (B := $B) $hbase $hpos (by
            intro n r hr
            rr_sign) $hden $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_global_nonpos_sequence_den_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          lag := $B,
          den_nonzero := rr_lw_active_den_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_global_nonpos_sequence_den_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag := $B:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        have hrr :=
          (RealRooted.LiuWang.isRealRooted_of_nonpos_lag_sequence_den
            (B := $B) $hbase $hpos (by
              intro n r hr
              rr_sign) $hden $hraw $hdeg_succ $hno);
        rr_exact_realrooted_sequence_or_projection hrr)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_den using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_nonpos_lag_sequence_den
          $hbase $hpos $hB $hden $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_nonpos_lag_sequence_den_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        lag_nonpos := $hB:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_nonpos_lag_sequence_den
            $hbase $hpos $hB $hden $hraw $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_const_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_const_lag_sequence
          $hbase $hpos $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_const_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_const_lag_sequence
          $hbase $hpos rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_const_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_const_lag_sequence
            $hbase $hpos $hc $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_const_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_const_lag_sequence
            $hbase $hpos rr_lw_active_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_const_C_neg_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_const_C_neg_lag_sequence
          $hbase $hpos $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_const_C_neg_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_const_C_neg_lag_sequence
          $hbase $hpos rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_const_C_neg_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_const_C_neg_lag_sequence
            $hbase $hpos $hc $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_const_C_neg_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_const_C_neg_lag_sequence
            $hbase $hpos rr_lw_active_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_square_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_square_lag_sequence
          $hbase $hpos $hc $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_square_lag_sequence
          $hbase $hpos rr_lw_active_nonneg $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff_nonneg := $hc:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_square_lag_sequence
            $hbase $hpos $hc $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_square_sequence_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_square_lag_sequence
            $hbase $hpos rr_lw_active_nonneg $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_square_sequence_unit using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_square_lag_sequence_unit
          $hbase $hpos $hrec $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_realrooted_unit using
        base := $hbase:term,
        pos_lc := $hpos:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_square_lag_sequence_unit
            $hbase $hpos $hrec $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          coeff_nonneg := $hc,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_square_lag_sequence_den_coeff
          (c := $c) $hbase $hpos $hc $hden $hcoeff $hraw $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_nonneg := $hc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_nonneg := $hc,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LiuWang.strictInterl_negative_square_lag_sequence_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hc $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact RealRooted.LiuWang.strictInterl_negative_square_lag_sequence_den_coeff
          (c := $c) $hbase $hpos rr_lw_active_nonneg $hden $hcoeff $hraw
          $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        exact
          RealRooted.LiuWang.strictInterl_negative_square_lag_sequence_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_active_nonneg $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          coeff_nonneg := $hc,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_square_lag_sequence_den_coeff
            (c := $c) $hbase $hpos $hc $hden $hcoeff $hraw $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_nonneg := $hc:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_nonneg := $hc,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_nonneg := $hc:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_square_lag_sequence_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos $hc $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
          base := $hbase,
          pos_lc := $hpos,
          coeff := $c,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto using
        base := $hbase:term,
        pos_lc := $hpos:term,
        coeff := $c:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_square_lag_sequence_den_coeff
            (c := $c) $hbase $hpos rr_lw_active_nonneg $hden $hcoeff $hraw
            $hdeg_succ $hno))
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          coeff_eq := rr_lw_coeff_all_term,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
          base := $hbase,
          pos_lc := $hpos,
          square_factor := $q,
          coeff := $c,
          raw_coeff := $b,
          den := $d,
          den_nonzero := rr_lw_active_den_all_term,
          coeff_eq := $hcoeff,
          raw_recurrence := $hraw,
          degree_succ := $hdeg_succ,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
        base := $hbase:term,
        pos_lc := $hpos:term,
        square_factor := $q:term,
        coeff := $c:term,
        raw_coeff := $b:term,
        den := $d:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term,
        raw_recurrence := $hraw:term,
        degree_succ := $hdeg_succ:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.LiuWang.isRealRooted_of_negative_square_lag_sequence_den_coeff
            (q := $q) (b := $b) (c := $c) (d := $d)
            $hbase $hpos rr_lw_active_nonneg $hden $hcoeff
            (rr_lw_raw_recurrence_seq $hraw)
            $hdeg_succ $hno))

end Tactic
end RealRooted
