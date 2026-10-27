module

public import RealRooted.Tactic.MaWang.SequenceSyntax

/-!
# Ma--Wang tactic scalar-denominator syntax

Parser declarations for normalized scalar-denominator recurrence certificates.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff : c`,
the coefficient sequence `c : ℕ → ℝ`; `den_nonzero : ∀ n, d n ≠ 0`;
`coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n *
P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. Here `V` and `b` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `coeff_nonneg`
is closed by `rr_mw_active_nonneg`; `coeff_nonpos_of_nonpos` is closed by `rr_sign`. -/
syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff : c`,
the coefficient sequence `c : ℕ → ℝ`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n *
P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. Here `V` and `b` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `coeff_nonneg`
is closed by `rr_mw_active_nonneg`; `coeff_nonpos_of_nonpos` is closed by `rr_sign`; `den_nonzero`
is closed by `rr_mw_active_den_all_term`; `coeff_eq` is closed by `rr_mw_coeff_all_term`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff : c`,
the coefficient sequence `c : ℕ → ℝ`; `den_nonzero : ∀ n, d n ≠ 0`;
`coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n *
P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`; and
`degree_succ : ∀ n, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1`, from which both degree
bounds are derived by `lia`. Here `V` and `b` are inferred from `raw_recurrence`. The omitted
certificates are supplied automatically: `coeff_nonneg` is closed by `rr_mw_active_nonneg`;
`coeff_nonpos_of_nonpos` is closed by `rr_sign`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff : c`,
the coefficient sequence `c : ℕ → ℝ`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n *
P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`; and
`degree_succ : ∀ n, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1`, from which both degree
bounds are derived by `lia`. Here `V` and `b` are inferred from `raw_recurrence`. The omitted
certificates are supplied automatically: `coeff_nonneg` is closed by `rr_mw_active_nonneg`;
`coeff_nonpos_of_nonpos` is closed by `rr_sign`; `den_nonzero` is closed by
`rr_mw_active_den_all_term`; `coeff_eq` is closed by `rr_mw_coeff_all_term`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_active_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`deriv_factor : V`, the derivative factor sequence `V : ℕ → ℝ[X]`; `coeff : c`, the coefficient
sequence `c : ℕ → ℝ`; `den : d`, the denominator sequence `d : ℕ → ℝ`; `raw_coeff : b`, the raw
coefficient sequence `b : ℕ → ℝ`; `den_nonzero : ∀ n, d n ≠ 0`;
`coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n *
P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. The raw recurrence is
normalized by `rr_mw_raw_recurrence_seq`. The omitted certificates are supplied automatically:
`coeff_nonneg` is closed by `rr_mw_active_nonneg`; `coeff_nonpos_of_nonpos` is closed by
`rr_sign`. -/
syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`deriv_factor : V`, the derivative factor sequence `V : ℕ → ℝ[X]`; `coeff : c`, the coefficient
sequence `c : ℕ → ℝ`; `den : d`, the denominator sequence `d : ℕ → ℝ`; `raw_coeff : b`, the raw
coefficient sequence `b : ℕ → ℝ`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n * P
(n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. The raw recurrence is
normalized by `rr_mw_raw_recurrence_seq`. The omitted certificates are supplied automatically:
`coeff_nonneg` is closed by `rr_mw_active_nonneg`; `coeff_nonpos_of_nonpos` is closed by `rr_sign`;
`den_nonzero` is closed by `rr_mw_active_den_all_term`; `coeff_eq` is closed by
`rr_mw_coeff_all_term`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`deriv_factor : V`, the derivative factor sequence `V : ℕ → ℝ[X]`; `coeff : c`, the coefficient
sequence `c : ℕ → ℝ`; `den : d`, the denominator sequence `d : ℕ → ℝ`; `raw_coeff : b`, the raw
coefficient sequence `b : ℕ → ℝ`; `den_nonzero : ∀ n, d n ≠ 0`;
`coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n *
P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`; and
`degree_succ : ∀ n, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1`, from which both degree
bounds are derived by `lia`. The raw recurrence is normalized by `rr_mw_raw_recurrence_seq`. The
omitted certificates are supplied automatically: `coeff_nonneg` is closed by `rr_mw_active_nonneg`;
`coeff_nonpos_of_nonpos` is closed by `rr_sign`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`deriv_factor : V`, the derivative factor sequence `V : ℕ → ℝ[X]`; `coeff : c`, the coefficient
sequence `c : ℕ → ℝ`; `den : d`, the denominator sequence `d : ℕ → ℝ`; `raw_coeff : b`, the raw
coefficient sequence `b : ℕ → ℝ`; `raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n * P
(n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`; and
`degree_succ : ∀ n, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1`, from which both degree
bounds are derived by `lia`. The raw recurrence is normalized by `rr_mw_raw_recurrence_seq`. The
omitted certificates are supplied automatically: `coeff_nonneg` is closed by `rr_mw_active_nonneg`;
`coeff_nonpos_of_nonpos` is closed by `rr_sign`; `den_nonzero` is closed by
`rr_mw_active_den_all_term`; `coeff_eq` is closed by `rr_mw_coeff_all_term`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split_active_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Ma--Wang derivative recurrence with an arbitrary
polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff : c`, the coefficient sequence `c : ℕ → ℝ`;
`den_nonzero : ∀ n, d n ≠ 0`; `coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d
n) * P (n + 2) = C (d n) * (U n * P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. Here `V` and `b` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `coeff_nonneg`
is closed by `rr_mw_active_nonneg`; `coeff_nonpos_of_nonpos` is closed by `rr_sign`. -/
syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Ma--Wang derivative recurrence with an arbitrary
polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff : c`, the coefficient sequence `c : ℕ → ℝ`;
`raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n * P (n + 1)) + C (b n) * (V n * (P (n +
1)).derivative)`; `degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. Here `V` and `b` are
inferred from `raw_recurrence`. The omitted certificates are supplied automatically: `coeff_nonneg`
is closed by `rr_mw_active_nonneg`; `coeff_nonpos_of_nonpos` is closed by `rr_sign`; `den_nonzero`
is closed by `rr_mw_active_den_all_term`; `coeff_eq` is closed by `rr_mw_coeff_all_term`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Ma--Wang derivative recurrence with an arbitrary
polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff : c`, the coefficient sequence `c : ℕ → ℝ`;
`den_nonzero : ∀ n, d n ≠ 0`; `coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d
n) * P (n + 2) = C (d n) * (U n * P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`; and
`degree_succ : ∀ n, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1`, from which both degree
bounds are derived by `lia`. Here `V` and `b` are inferred from `raw_recurrence`. The omitted
certificates are supplied automatically: `coeff_nonneg` is closed by `rr_mw_active_nonneg`;
`coeff_nonpos_of_nonpos` is closed by `rr_sign`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Ma--Wang derivative recurrence with an arbitrary
polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `coeff : c`, the coefficient sequence `c : ℕ → ℝ`;
`raw_recurrence : ∀ n, C (d n) * P (n + 2) = C (d n) * (U n * P (n + 1)) + C (b n) * (V n * (P (n +
1)).derivative)`; and `degree_succ : ∀ n, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1`, from
which both degree bounds are derived by `lia`. Here `V` and `b` are inferred from `raw_recurrence`.
The omitted certificates are supplied automatically: `coeff_nonneg` is closed by
`rr_mw_active_nonneg`; `coeff_nonpos_of_nonpos` is closed by `rr_sign`; `den_nonzero` is closed by
`rr_mw_active_den_all_term`; `coeff_eq` is closed by `rr_mw_coeff_all_term`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_active_degree_succ_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`recurrence : ∀ n, P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. -/
syntax (name := rr_mw_derivative_X_sequence_nonneg_named)
  "rr_mw_derivative_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, StrictInterl (P n) (P (n + 1))` for a Ma--Wang derivative recurrence with an
arbitrary polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`;
`pos_lc : ∀ n, HasPosLeadingCoeff (P n)`; `nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`;
`recurrence : ∀ n, P (n + 2) = U n * P (n + 1) + X * (P (n + 1)).derivative`; and
`degree_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree`, from which both degree bounds are
derived by `lia`. -/
syntax (name := rr_mw_derivative_X_sequence_nonneg_degree_succ_named)
  "rr_mw_derivative_X_sequence_nonneg" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Ma--Wang derivative recurrence with an arbitrary
polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `deriv_factor : V`, the derivative factor sequence
`V : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`;
`den_nonzero : ∀ n, d n ≠ 0`; `coeff_eq : ∀ n, (d n)⁻¹ * b n = c n`; `raw_recurrence : ∀ n, C (d
n) * P (n + 2) = C (d n) * (U n * P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. The raw recurrence is
normalized by `rr_mw_raw_recurrence_seq`. The omitted certificates are supplied automatically:
`coeff_nonneg` is closed by `rr_mw_active_nonneg`; `coeff_nonpos_of_nonpos` is closed by
`rr_sign`. -/
syntax (name := rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a Ma--Wang derivative recurrence with an arbitrary
polynomial `U n`, from `base : StrictInterl (P 0) (P 1)`; `pos_lc : ∀ n, HasPosLeadingCoeff (P n)`;
`nonneg_coeffs : ∀ n, HasNonnegCoeffs (P n)`; `deriv_factor : V`, the derivative factor sequence
`V : ℕ → ℝ[X]`; `coeff : c`, the coefficient sequence `c : ℕ → ℝ`; `den : d`, the denominator
sequence `d : ℕ → ℝ`; `raw_coeff : b`, the raw coefficient sequence `b : ℕ → ℝ`; `raw_recurrence : ∀
n, C (d n) * P (n + 2) = C (d n) * (U n * P (n + 1)) + C (b n) * (V n * (P (n + 1)).derivative)`;
`degree_lower : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree`; and
`degree_upper : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1`. The raw recurrence is
normalized by `rr_mw_raw_recurrence_seq`. The omitted certificates are supplied automatically:
`coeff_nonneg` is closed by `rr_mw_active_nonneg`; `coeff_nonpos_of_nonpos` is closed by `rr_sign`;
`den_nonzero` is closed by `rr_mw_active_den_all_term`; `coeff_eq` is closed by
`rr_mw_coeff_all_term`. -/
syntax (name :=
    rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split_active_named)
  "rr_mw_derivative_nonpos_sequence_den_coeff_realrooted_nonneg_sign_auto_split" " using "
    "base" ":=" term ","
    "pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "deriv_factor" ":=" term ","
    "coeff" ":=" term ","
    "den" ":=" term ","
    "raw_coeff" ":=" term ","
    "raw_recurrence" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term :
  tactic


end Tactic
end RealRooted
