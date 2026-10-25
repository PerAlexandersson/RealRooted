module

public import RealRooted.Tactic.MaWang.Basic

/-!
# Ma--Wang tactic step syntax

Parser declarations for one-step Ma--Wang and weak derivative certificates.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

/-- Positional form of `rr_ma_wang using ...`: the same six arguments as the named form, in the
order `splits`, `degree_lower`, `degree_upper`, `target_pos_lc`, `source_pos_lc` and `root_sign`. -/
syntax (name := rr_ma_wang)
  "rr_ma_wang" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

/-- Bare form of `rr_ma_wang`: finds all six certificates in the local context, using `rr_lookup`
with the `rr_degree` and `rr_pos_lc` registries for the degree bounds and leading coefficients. -/
syntax (name := rr_ma_wang_inferred) "rr_ma_wang" : tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from `splits : f.Splits`,
`degree_lower : f.natDegree ≤ F.natDegree`, `degree_upper : F.natDegree ≤ f.natDegree + 1`,
`target_pos_lc : HasPosLeadingCoeff F`, `source_pos_lc : HasPosLeadingCoeff f` and
`root_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0`. This is the Ma--Wang step
with the sign condition on `v` against the squared derivative. -/
syntax (name := rr_ma_wang_named)
  "rr_ma_wang" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

/-- Positional form of `rr_ma_wang_same using ...`: the same five arguments as the named form, in
the order `splits`, `degree`, `target_pos_lc`, `source_pos_lc` and `root_sign`. -/
syntax (name := rr_ma_wang_same)
  "rr_ma_wang_same" " using " term ", " term ", " term ", " term ", " term :
  tactic

/-- Bare form of `rr_ma_wang_same`: finds all five certificates in the local context by `rr_lookup`,
using `rr_degree` and `rr_pos_lc` for the degree and leading coefficients. -/
syntax (name := rr_ma_wang_same_inferred) "rr_ma_wang_same" : tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from `splits : f.Splits`,
`degree : F.natDegree = f.natDegree`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f` and
`root_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0`. Same-degree form of
`rr_ma_wang`. -/
syntax (name := rr_ma_wang_same_named)
  "rr_ma_wang_same" " using "
    "splits" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

/-- Positional form of `rr_ma_wang_succ using ...`: the same five arguments as the named form, in
the order `splits`, `degree`, `target_pos_lc`, `source_pos_lc` and `root_sign`. -/
syntax (name := rr_ma_wang_succ)
  "rr_ma_wang_succ" " using " term ", " term ", " term ", " term ", " term :
  tactic

/-- Bare form of `rr_ma_wang_succ`: finds all five certificates in the local context by `rr_lookup`,
using `rr_degree` and `rr_pos_lc` for the degree and leading coefficients. -/
syntax (name := rr_ma_wang_succ_inferred) "rr_ma_wang_succ" : tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from `splits : f.Splits`,
`degree : F.natDegree = f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f` and
`root_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0`. Degree-increasing form of
`rr_ma_wang`. -/
syntax (name := rr_ma_wang_succ_named)
  "rr_ma_wang_succ" " using "
    "splits" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `a * f + b * g`, from `interlaces : Interlaces g f`,
`source_pos_lc : HasPosLeadingCoeff g`, `target_pos_lc : HasPosLeadingCoeff F`,
`degree_lower : f.natDegree ≤ F.natDegree`, `degree_upper : F.natDegree ≤ f.natDegree + 1` and
`coeff_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0`. -/
syntax (name := rr_strict_interl_evalCoeff_nonpos_named)
  "rr_strict_interl_evalCoeff_nonpos" " using "
    "interlaces" ":=" term ","
    "source_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `a * f + b * g`, from `interlaces : Interlaces g f`,
`source_pos_lc : HasPosLeadingCoeff g`, `target_pos_lc : HasPosLeadingCoeff F`,
`degree : F.natDegree = f.natDegree` (or `f.natDegree + 1`), from which both degree bounds are
derived by `lia` and `coeff_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0`. -/
syntax (name := rr_strict_interl_evalCoeff_nonpos_degree_named)
  "rr_strict_interl_evalCoeff_nonpos" " using "
    "interlaces" ":=" term ","
    "source_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_evalCoeff_nonpos`: finds all six certificates in the local
context by `rr_lookup`, using `rr_degree` and `rr_pos_lc` for the degree bounds and leading
coefficients. -/
syntax (name := rr_strict_interl_evalCoeff_nonpos_inferred)
  "rr_strict_interl_evalCoeff_nonpos" : tactic

/-- Bare form of the `degree` variant of `rr_strict_interl_evalCoeff_nonpos`: takes `degree` from
the `using` clause and finds the other certificates in the local context by `rr_lookup`. -/
syntax (name := rr_strict_interl_evalCoeff_nonpos_degree_inferred)
  "rr_strict_interl_evalCoeff_nonpos" " using " "degree" ":=" term : tactic

/-- Positional form of `rr_mw_derivative_nonpos using ...`: the same six arguments as the named
form, in the order `splits`, `degree_lower`, `degree_upper`, `target_pos_lc`, `source_pos_lc` and
`coeff_nonpos`. -/
syntax (name := rr_mw_derivative_nonpos)
  "rr_mw_derivative_nonpos" " using " term ", " term ", " term ", " term ", "
    term ", " term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from `splits : f.Splits`,
`degree_lower : f.natDegree ≤ F.natDegree`, `degree_upper : F.natDegree ≤ f.natDegree + 1`,
`target_pos_lc : HasPosLeadingCoeff F`, `source_pos_lc : HasPosLeadingCoeff f` and
`coeff_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0`. -/
syntax (name := rr_mw_derivative_nonpos_named)
  "rr_mw_derivative_nonpos" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from `splits : f.Splits`,
`target_pos_lc : HasPosLeadingCoeff F`, `recurrence : F = u * f + v * f.derivative`,
`degree_lower : f.natDegree ≤ F.natDegree`, `degree_upper : F.natDegree ≤ f.natDegree + 1`,
`source_pos_lc : HasPosLeadingCoeff f` and `coeff_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0`. Here the
target `F` is given by `recurrence` rather than written out. -/
syntax (name := rr_mw_derivative_nonpos_step_named)
  "rr_mw_derivative_nonpos_step" " using "
    "splits" ":=" term ","
    "target_pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

/-- Closes `StrictInterl f F` from `recurrence : F = u * f + v * f.derivative`, finding the other
certificates of `rr_mw_derivative_nonpos_step` by `rr_lookup`. -/
syntax (name := rr_mw_derivative_nonpos_step_inferred_of_recurrence)
  "rr_mw_derivative_nonpos_step" " using " "recurrence" ":=" term : tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from `splits : f.Splits`,
`degree : F.natDegree = f.natDegree` (or `f.natDegree + 1`), from which both degree bounds are
derived by `lia`, `target_pos_lc : HasPosLeadingCoeff F`, `source_pos_lc : HasPosLeadingCoeff f` and
`coeff_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0`. -/
syntax (name := rr_mw_derivative_nonpos_degree_named)
  "rr_mw_derivative_nonpos" " using "
    "splits" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term :
  tactic

/-- Bare form of `rr_mw_derivative_nonpos`: finds all six certificates in the local context by
`rr_lookup`, using `rr_degree` and `rr_pos_lc` for the degree bounds and leading coefficients. -/
syntax (name := rr_mw_derivative_nonpos_inferred)
  "rr_mw_derivative_nonpos" : tactic

/-- Bare form of the `degree` variant of `rr_mw_derivative_nonpos`: takes `degree` from the `using`
clause and finds the other certificates in the local context by `rr_lookup`. -/
syntax (name := rr_mw_derivative_nonpos_degree_inferred)
  "rr_mw_derivative_nonpos" " using " "degree" ":=" term : tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from `splits : f.Splits`,
`degree_lower : f.natDegree ≤ F.natDegree`, `degree_upper : F.natDegree ≤ f.natDegree + 1`,
`target_pos_lc : HasPosLeadingCoeff F`, `source_pos_lc : HasPosLeadingCoeff f` and
`roots_nonpos : ∀ r, f.IsRoot r → r ≤ 0`. The sign condition `v.eval r ≤ 0` at the roots of `f` is
proved by `rr_sign`. -/
syntax (name := rr_mw_derivative_sign_roots_nonpos_named)
  "rr_mw_derivative_sign_roots_nonpos" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from
`realrooted : f ≠ 0 ∧ f.Splits`, `nonneg : HasNonnegCoeffs f`,
`degree_lower : f.natDegree ≤ F.natDegree`, `degree_upper : F.natDegree ≤ f.natDegree + 1`,
`target_pos_lc : HasPosLeadingCoeff F` and `source_pos_lc : HasPosLeadingCoeff f`. The sign
condition `v.eval r ≤ 0` at the roots of `f` follows from the nonnegative coefficients of `f`
through `rr_sign_at_roots_term`. -/
syntax (name := rr_mw_derivative_sign_nonneg_coeffs_named)
  "rr_mw_derivative_sign_nonneg_coeffs" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from
`realrooted : f ≠ 0 ∧ f.Splits`, `nonneg : HasNonnegCoeffs f`,
`factor_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F` and
`source_pos_lc : HasPosLeadingCoeff f`. The sign condition `v.eval r ≤ 0` at the roots of `f`
follows from the nonnegative coefficients of `f` and the factor `q` through
`rr_sign_at_roots_factor_term`. -/
syntax (name := rr_mw_derivative_sign_nonneg_factor_named)
  "rr_mw_derivative_sign_nonneg_factor" " using "
    "realrooted" ":=" term ","
    "nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from `splits : f.Splits`,
`degree_lower : f.natDegree ≤ F.natDegree`, `degree_upper : F.natDegree ≤ f.natDegree + 1`,
`target_pos_lc : HasPosLeadingCoeff F`, `source_pos_lc : HasPosLeadingCoeff f` and `root_upper`.
Here `root_upper : ∀ r, f.IsRoot r → r ≤ b` is an upper bound for the roots of `f`. The sign
condition `v.eval r ≤ 0` at the roots of `f` is proved by `rr_sign`. -/
syntax (name := rr_mw_derivative_sign_root_upper_named)
  "rr_mw_derivative_sign_root_upper" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_upper" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + v * f.derivative`, from `splits : f.Splits`,
`degree_lower : f.natDegree ≤ F.natDegree`, `degree_upper : F.natDegree ≤ f.natDegree + 1`,
`target_pos_lc : HasPosLeadingCoeff F`, `source_pos_lc : HasPosLeadingCoeff f`, `root_lower` and
`root_upper`. Here `root_lower` and `root_upper` bound the roots of `f` below and above, in the form
`∀ r, f.IsRoot r → a ≤ r` and `∀ r, f.IsRoot r → r ≤ b`. The sign condition `v.eval r ≤ 0` at the
roots of `f` is proved by `rr_sign`. -/
syntax (name := rr_mw_derivative_sign_window_named)
  "rr_mw_derivative_sign_window" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + (X * q) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f`, `roots_nonpos : ∀ r, f.IsRoot r → r ≤ 0` and
`factor_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r`. -/
syntax (name := rr_mw_derivative_X_mul_named)
  "rr_mw_derivative_X_mul" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + (C c * X * q) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f`, `coeff_nonneg : 0 ≤ c`,
`roots_nonpos : ∀ r, f.IsRoot r → r ≤ 0` and `factor_nonneg : ∀ r, f.IsRoot r → 0 ≤ q.eval r`. -/
syntax (name := rr_mw_derivative_C_mul_X_mul_named)
  "rr_mw_derivative_C_mul_X_mul" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + (X * (1 + X)) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f`, `root_lower : ∀ r, f.IsRoot r → -1 ≤ r` and
`root_upper : ∀ r, f.IsRoot r → r ≤ 0`. -/
syntax (name := rr_mw_derivative_X_one_add_window_named)
  "rr_mw_derivative_X_one_add_window" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + (-(C c) * X * (1 + X)) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f`, `coeff_nonneg : 0 ≤ c` and
`root_upper : ∀ r, f.IsRoot r → r ≤ -1`. -/
syntax (name := rr_mw_derivative_neg_X_one_add_outer_named)
  "rr_mw_derivative_neg_X_one_add_outer" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "root_upper" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + (-(C c) * X * (1 + X)) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f` and `root_upper : ∀ r, f.IsRoot r → r ≤ -1`. The
nonnegativity `0 ≤ c` is closed by `rr_mw_active_nonneg_at 0`. -/
syntax (name := rr_mw_derivative_neg_X_one_add_outer_auto_named)
  "rr_mw_derivative_neg_X_one_add_outer_auto" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_upper" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + ((1 + X) * (1 + C 2 * X)) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f`, `root_lower : ∀ r, f.IsRoot r → -1 ≤ r` and
`root_upper : ∀ r, f.IsRoot r → r ≤ -(1 / 2)`. -/
syntax (name := rr_mw_derivative_one_add_two_window_named)
  "rr_mw_derivative_one_add_two_window" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the sequence recurrence with derivative factor
`(1 + X) * (1 + C 2 * X)` and an arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2)`; `recurrence : ∀ n, P (n + 2) = U n * P (n
+ 1) + ((1 + X) * (1 + C 2 * X)) * (P (n + 1)).derivative`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. -/
syntax (name := rr_mw_derivative_one_add_two_window_sequence_named)
  "rr_mw_derivative_one_add_two_window_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for the sequence recurrence with derivative factor
`(1 + X) * (1 + C 2 * X)` and an arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2)`; `recurrence : ∀ n, P (n + 2) = U n * P (n
+ 1) + ((1 + X) * (1 + C 2 * X)) * (P (n + 1)).derivative`; and
`degree_succ : ∀ n, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1`, from which both degree
bounds are derived. -/
syntax (name := rr_mw_derivative_one_add_two_window_sequence_degree_succ_named)
  "rr_mw_derivative_one_add_two_window_sequence" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the sequence recurrence with derivative factor
`(1 + X) * (1 + C 2 * X)` and an arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2)`; `recurrence : ∀ n, P (n + 2) = U n * P (n
+ 1) + ((1 + X) * (1 + C 2 * X)) * (P (n + 1)).derivative`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. -/
syntax (name := rr_mw_derivative_one_add_two_window_sequence_realrooted_named)
  "rr_mw_derivative_one_add_two_window_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the sequence recurrence with derivative factor
`(1 + X) * (1 + C 2 * X)` and an arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `root_lower : ∀ n r, (P (n + 1)).IsRoot r → -1 ≤ r`;
`root_upper : ∀ n r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2)`; `recurrence : ∀ n, P (n + 2) = U n * P (n
+ 1) + ((1 + X) * (1 + C 2 * X)) * (P (n + 1)).derivative`; and
`degree_succ : ∀ n, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1`, from which both degree
bounds are derived. -/
syntax (name := rr_mw_derivative_one_add_two_window_sequence_realrooted_degree_succ_named)
  "rr_mw_derivative_one_add_two_window_sequence_realrooted" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "root_lower" ":=" term ","
    "root_upper" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + C (-c) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f` and `coeff_nonneg : 0 ≤ c`. -/
syntax (name := rr_mw_derivative_neg_const_named)
  "rr_mw_derivative_neg_const" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + C (-c) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F` and
`source_pos_lc : HasPosLeadingCoeff f`. The nonnegativity `0 ≤ c` is closed by
`rr_mw_active_nonneg_at 0`. -/
syntax (name := rr_mw_derivative_neg_const_auto_named)
  "rr_mw_derivative_neg_const_auto" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + (-(C c) * X ^ 2) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F`,
`source_pos_lc : HasPosLeadingCoeff f` and `coeff_nonneg : 0 ≤ c`. -/
syntax (name := rr_mw_derivative_neg_X_sq_named)
  "rr_mw_derivative_neg_X_sq" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term :
  tactic

/-- Closes `StrictInterl f F`, where `F` is `u * f + (-(C c) * X ^ 2) * f.derivative`, from
`splits : f.Splits`, `degree_lower : f.natDegree ≤ F.natDegree`,
`degree_upper : F.natDegree ≤ f.natDegree + 1`, `target_pos_lc : HasPosLeadingCoeff F` and
`source_pos_lc : HasPosLeadingCoeff f`. The nonnegativity `0 ≤ c` is closed by
`rr_mw_active_nonneg_at 0`. -/
syntax (name := rr_mw_derivative_neg_X_sq_auto_named)
  "rr_mw_derivative_neg_X_sq_auto" " using "
    "splits" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term :
  tactic

end Tactic
end RealRooted
