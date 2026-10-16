module

public import RealRooted.Tactic.Product

/-!
# OEIS product-parity certificate frontend

Parser declarations and dispatch rules for alternating scalar/product steps and
endpoint-pair certificates.
-/

public section

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by a real-rooted factor `F n` (`certificate := scalarThenFactor`, as
`rr_product_scalar_factor_sequence`); the arguments are `base`,
`scalar_ne`, `factor_realrooted`, an optional `cutoff`, `scalar_step` and `factor_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_factor)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenFactor" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by a real-rooted factor `F n` (`certificate := scalarThenFactorAuto`, as
`rr_product_scalar_factor_sequence_auto`); the nonvanishing of the scalars is proved
automatically, and the arguments are `base`, `factor_realrooted`, an optional `cutoff`,
`scalar_step` and `factor_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_factor_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenFactorAuto" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `X + C (b n)` (`certificate := scalarThenXAddC`, as
`rr_product_scalar_linear_sequence`); the arguments are `base`,
`scalar_ne`, an optional `cutoff`, `scalar_step` and `linear_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_x_add_c)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddC" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `X + C (b n)` (`certificate := scalarThenXAddCAuto`, as
`rr_product_scalar_linear_sequence_auto`); the nonvanishing of the scalars is proved
automatically, and the arguments are `base`, an optional `cutoff`, `scalar_step` and
`linear_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_x_add_c_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddCAuto" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `C (b n) + X` (`certificate := scalarThenCAddX`, as
`rr_product_scalar_C_add_X_sequence`); the arguments are `base`,
`scalar_ne`, an optional `cutoff`, `scalar_step` and `linear_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_c_add_x)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddX" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `C (b n) + X` (`certificate := scalarThenCAddXAuto`, as
`rr_product_scalar_C_add_X_sequence_auto`); the nonvanishing of the scalars is proved
automatically, and the arguments are `base`, an optional `cutoff`, `scalar_step` and
`linear_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_c_add_x_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddXAuto" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `X ^ m n` (`certificate := scalarThenRootZeroPow`, as
`rr_product_scalar_X_pow_sequence`); the arguments are `base`,
`scalar_ne`, an optional `cutoff`, `scalar_step` and `factor_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_root_zero_pow)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenRootZeroPow" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `X ^ m n` (`certificate := scalarThenRootZeroPowAuto`, as
`rr_product_scalar_X_pow_sequence_auto`); the nonvanishing of the scalars is proved
automatically, and the arguments are `base`, an optional `cutoff`, `scalar_step` and
`factor_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_root_zero_pow_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenRootZeroPowAuto" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `(X + C (b n)) ^ m n` (`certificate := scalarThenXAddCPow`, as
`rr_product_scalar_X_add_C_pow_sequence`); the arguments are `base`,
`scalar_ne`, an optional `cutoff`, `scalar_step` and `factor_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_x_add_c_pow)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddCPow" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `(X + C (b n)) ^ m n` (`certificate := scalarThenXAddCPowAuto`, as
`rr_product_scalar_X_add_C_pow_sequence_auto`); the nonvanishing of the scalars is proved
automatically, and the arguments are `base`, an optional `cutoff`, `scalar_step` and
`factor_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_x_add_c_pow_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddCPowAuto" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `(C (b n) + X) ^ m n` (`certificate := scalarThenCAddXPow`, as
`rr_product_scalar_C_add_X_pow_sequence`); the arguments are `base`,
`scalar_ne`, an optional `cutoff`, `scalar_step` and `factor_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_c_add_x_pow)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddXPow" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the two-step recurrence that multiplies by a scalar
`C (a n)` and then by `(C (b n) + X) ^ m n` (`certificate := scalarThenCAddXPowAuto`, as
`rr_product_scalar_C_add_X_pow_sequence_auto`); the nonvanishing of the scalars is proved
automatically, and the arguments are `base`, an optional `cutoff`, `scalar_step` and
`factor_step`. -/
syntax (name := rr_product_parity_sequence_scalar_then_c_add_x_pow_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddXPowAuto" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a parity-split sequence
(`certificate := scalarXOdd`, as
`rr_even_product_odd_X_scalar_sequence`) from `even_realrooted`,
`scalar_ne`, `even_factorization : P (2 * n) = Q n` and `odd_factorization : P (2 * n + 1) = C
(a n) * X * Q n`. -/
syntax (name := rr_product_parity_lift_sequence_scalar_x_odd)
  "rr_product_parity_lift_sequence" " using "
    "even_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "scalarXOdd" :
  tactic

/-- Closes `∀ n, StrictInterl (A n) (B n)` for the endpoint pair with `A (n + 1) = A n + B n`
and `B (n + 1) = B n + X * A (n + 1)` (`certificate := sumThenX`, as
`rr_endpoint_sum_then_X_pair_sequence`); the arguments are `base`,
`left_nonneg`, `right_nonneg`, `sum_step` and `x_step`. -/
syntax (name := rr_endpoint_pair_sequence_sum_then_x)
  "rr_endpoint_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "certificate" ":=" "sumThenX" :
  tactic

/-- Closes `∀ n, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits)` for the endpoint pair of
`rr_endpoint_pair_sequence` with `certificate := sumThenX`, with the same arguments. -/
syntax (name := rr_endpoint_pair_sequence_realrooted_sum_then_x)
  "rr_endpoint_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "certificate" ":=" "sumThenX" :
  tactic

/-- Closes `∀ n, StrictInterl (A n) (B n)` for the endpoint pair with
`B (n + 1) = B n + X * A n` and `A (n + 1) = A n + B (n + 1)` (`certificate := xThenSum`, as
`rr_endpoint_X_then_sum_pair_sequence`); the arguments are `base`,
`left_nonneg`, `right_nonneg`, `x_step` and `sum_step`. -/
syntax (name := rr_endpoint_pair_sequence_x_then_sum)
  "rr_endpoint_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "certificate" ":=" "xThenSum" :
  tactic

/-- Closes `∀ n, (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits)` for the endpoint pair of
`rr_endpoint_pair_sequence` with `certificate := xThenSum`, with the same arguments. -/
syntax (name := rr_endpoint_pair_sequence_realrooted_x_then_sum)
  "rr_endpoint_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "certificate" ":=" "xThenSum" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` when the even and odd rows are endpoint powers times
`A n` and `B n` for the pair of `rr_endpoint_pair_sequence` with `certificate :=
sumThenX` (as `rr_endpoint_sum_then_X_pair_lift_sequence`);
`even_factorization` and `odd_factorization` give the rows. -/
syntax (name := rr_endpoint_pair_lift_sequence_sum_then_x)
  "rr_endpoint_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "sumThenX" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` when the even and odd rows are endpoint powers times
`A n` and `B n` for the pair of `rr_endpoint_pair_sequence` with `certificate :=
xThenSum` (as `rr_endpoint_X_then_sum_pair_lift_sequence`);
`even_factorization` and `odd_factorization` give the rows. -/
syntax (name := rr_endpoint_pair_lift_sequence_x_then_sum)
  "rr_endpoint_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "xThenSum" :
  tactic

/-- Swapped form of the `xThenSum` lift (`certificate :=
xThenSumSwapped`, as `rr_endpoint_X_then_sum_pair_lift_swapped_sequence`): the even rows are
endpoint powers times `B n` and the odd rows endpoint powers times `A n`. -/
syntax (name := rr_endpoint_pair_lift_sequence_x_then_sum_swapped)
  "rr_endpoint_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "xThenSumSwapped" :
  tactic

macro_rules
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenFactor) =>
      `(tactic|
        rr_product_scalar_factor_sequence using
          base := $hbase,
          scalar_ne := $ha,
          factor_realrooted := $hfactor,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        factor_realrooted := $hfactor:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenFactor) =>
      `(tactic|
        rr_product_scalar_factor_sequence using
          base := $hbase,
          scalar_ne := $ha,
          factor_realrooted := $hfactor,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenFactorAuto) =>
      `(tactic|
        rr_product_scalar_factor_sequence_auto using
          base := $hbase,
          factor_realrooted := $hfactor,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenFactorAuto) =>
      `(tactic|
        rr_product_scalar_factor_sequence_auto using
          base := $hbase,
          factor_realrooted := $hfactor,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenXAddC) =>
      `(tactic|
        rr_product_scalar_linear_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenXAddC) =>
      `(tactic|
        rr_product_scalar_linear_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenXAddCAuto) =>
      `(tactic|
        rr_product_scalar_linear_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenXAddCAuto) =>
      `(tactic|
        rr_product_scalar_linear_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenCAddX) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenCAddX) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenCAddXAuto) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        linear_step := $hlinear:term,
        certificate := scalarThenCAddXAuto) =>
      `(tactic|
        rr_product_scalar_C_add_X_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          linear_step := $hlinear)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenRootZeroPow) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenRootZeroPow) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenRootZeroPowAuto) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenRootZeroPowAuto) =>
      `(tactic|
        rr_product_scalar_X_pow_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenXAddCPow) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenXAddCPow) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenXAddCPowAuto) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenXAddCPowAuto) =>
      `(tactic|
        rr_product_scalar_X_add_C_pow_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenCAddXPow) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_ne := $ha:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenCAddXPow) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence using
          base := $hbase,
          scalar_ne := $ha,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenCAddXPowAuto) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_sequence using
        base := $hbase:term,
        scalar_step := $hscalar:term,
        factor_step := $hstep:term,
        certificate := scalarThenCAddXPowAuto) =>
      `(tactic|
        rr_product_scalar_C_add_X_pow_sequence_auto using
          base := $hbase,
          scalar_step := $hscalar,
          factor_step := $hstep)
  | `(tactic|
      rr_product_parity_lift_sequence using
        even_realrooted := $hquot:term,
        scalar_ne := $ha:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term,
        certificate := scalarXOdd) =>
      `(tactic|
        rr_even_product_odd_X_scalar_sequence using
          even_realrooted := $hquot,
          scalar_ne := $ha,
          even_factorization := $heven,
          odd_factorization := $hodd)
  | `(tactic|
      rr_endpoint_pair_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        certificate := sumThenX) =>
      `(tactic|
        rr_endpoint_sum_then_X_pair_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          sum_step := $hsum_step,
          x_step := $hx_step)
  | `(tactic|
      rr_endpoint_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        certificate := sumThenX) =>
      `(tactic|
        rr_endpoint_sum_then_X_pair_sequence_realrooted using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          sum_step := $hsum_step,
          x_step := $hx_step)
  | `(tactic|
      rr_endpoint_pair_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        certificate := xThenSum) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step)
  | `(tactic|
      rr_endpoint_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        certificate := xThenSum) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_sequence_realrooted using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step)
  | `(tactic|
      rr_endpoint_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term,
        certificate := sumThenX) =>
      `(tactic|
        rr_endpoint_sum_then_X_pair_lift_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          sum_step := $hsum_step,
          x_step := $hx_step,
          even_factorization := $heven,
          odd_factorization := $hodd)
  | `(tactic|
      rr_endpoint_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term,
        certificate := xThenSum) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_lift_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step,
          even_factorization := $heven,
          odd_factorization := $hodd)
  | `(tactic|
      rr_endpoint_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        even_factorization := $heven:term,
        odd_factorization := $hodd:term,
        certificate := xThenSumSwapped) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_lift_swapped_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step,
          even_factorization := $heven,
          odd_factorization := $hodd)
end Tactic
end RealRooted
