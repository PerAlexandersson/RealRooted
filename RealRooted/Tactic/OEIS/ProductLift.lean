import RealRooted.Tactic.Product

/-!
# OEIS product-lift certificate frontend

Parser declarations and dispatch rules for quotient-real-rooted product lifts,
with explicit factorization and cutoff variants.
-/

namespace RealRooted
namespace Tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `quotient_realrooted : ∀ n, Q n ≠ 0 ∧ (Q n).Splits`;
`factor_realrooted : ∀ n, F n ≠ 0 ∧ (F n).Splits`; and `factorization : ∀ n, P n = F n * Q n`. The
keyword `certificate := suppliedFactor` selects the row factor `F n` that comes with its own
real-rootedness proof. -/
syntax (name := rr_product_lift_sequence_supplied_factor)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "suppliedFactor" :
  tactic

/-- Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` from `base : ∀ n ≤ N, P n ≠ 0 ∧ (P n).Splits`;
`quotient_realrooted : ∀ n ≥ N, Q n ≠ 0 ∧ (Q n).Splits`;
`factor_realrooted : ∀ n ≥ N, F n ≠ 0 ∧ (F n).Splits`; `cutoff : N`; and
`factorization : ∀ n ≥ N, P n = F n * Q n`. The keyword `certificate := suppliedFactor` selects the
row factor `F n` that comes with its own real-rootedness proof. -/
syntax (name := rr_product_lift_sequence_supplied_factor_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "factor_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "suppliedFactor" :
  tactic

/-- Certificate form of `rr_product_lift_sequence_auto`: with `certificate := auto` it runs
`rr_product_lift_sequence_auto` with the same arguments. -/
syntax (name := rr_product_lift_sequence_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "auto" :
  tactic

/-- Certificate form of `rr_product_lift_sequence_auto`: with `certificate := auto` it runs
`rr_product_lift_sequence_auto` with the same arguments, including the `base` and `cutoff` of the
cutoff form. -/
syntax (name := rr_product_lift_sequence_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "auto" :
  tactic

/-- Certificate form of `rr_product_lift_X_sequence`: with `certificate := rootZero` it runs
`rr_product_lift_X_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_root_zero)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZero" :
  tactic

/-- Certificate form of `rr_product_lift_X_sequence`: with `certificate := rootZero` it runs
`rr_product_lift_X_sequence` with the same arguments, including the `base` and `cutoff` of the
cutoff form. -/
syntax (name := rr_product_lift_sequence_root_zero_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZero" :
  tactic

/-- Certificate form of `rr_product_lift_X_pow_sequence`: with `certificate := rootZeroPow` it runs
`rr_product_lift_X_pow_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_root_zero_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZeroPow" :
  tactic

/-- Certificate form of `rr_product_lift_X_pow_sequence`: with `certificate := rootZeroPow` it runs
`rr_product_lift_X_pow_sequence` with the same arguments, including the `base` and `cutoff` of the
cutoff form. -/
syntax (name := rr_product_lift_sequence_root_zero_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rootZeroPow" :
  tactic

/-- Certificate form of `rr_product_lift_X_add_C_sequence`: with `certificate := xAddC` it runs
`rr_product_lift_X_add_C_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_x_add_c)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "xAddC" :
  tactic

/-- Certificate form of `rr_product_lift_X_add_C_sequence`: with `certificate := xAddC` it runs
`rr_product_lift_X_add_C_sequence` with the same arguments, including the `base` and `cutoff` of the
cutoff form. -/
syntax (name := rr_product_lift_sequence_x_add_c_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "xAddC" :
  tactic

/-- Certificate form of `rr_product_lift_C_add_X_sequence`: with `certificate := cAddX` it runs
`rr_product_lift_C_add_X_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_c_add_x)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "cAddX" :
  tactic

/-- Certificate form of `rr_product_lift_C_add_X_sequence`: with `certificate := cAddX` it runs
`rr_product_lift_C_add_X_sequence` with the same arguments, including the `base` and `cutoff` of the
cutoff form. -/
syntax (name := rr_product_lift_sequence_c_add_x_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "cAddX" :
  tactic

/-- Certificate form of `rr_product_lift_X_add_C_pow_sequence`: with `certificate := fixedXAddCPow`
it runs `rr_product_lift_X_add_C_pow_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_fixed_x_add_c_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "fixedXAddCPow" :
  tactic

/-- Certificate form of `rr_product_lift_X_add_C_pow_sequence`: with `certificate := fixedXAddCPow`
it runs `rr_product_lift_X_add_C_pow_sequence` with the same arguments, including the `base` and
`cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_fixed_x_add_c_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "fixedXAddCPow" :
  tactic

/-- Certificate form of `rr_product_lift_X_add_C_row_pow_sequence`: with
`certificate := rowXAddCPow` it runs `rr_product_lift_X_add_C_row_pow_sequence` with the same
arguments. -/
syntax (name := rr_product_lift_sequence_row_x_add_c_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rowXAddCPow" :
  tactic

/-- Certificate form of `rr_product_lift_X_add_C_row_pow_sequence`: with
`certificate := rowXAddCPow` it runs `rr_product_lift_X_add_C_row_pow_sequence` with the same
arguments, including the `base` and `cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_row_x_add_c_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "rowXAddCPow" :
  tactic

/-- Certificate form of `rr_product_lift_C_add_X_pow_sequence`: with `certificate := cAddXPow` it
runs `rr_product_lift_C_add_X_pow_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_c_add_x_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "cAddXPow" :
  tactic

/-- Certificate form of `rr_product_lift_C_add_X_pow_sequence`: with `certificate := cAddXPow` it
runs `rr_product_lift_C_add_X_pow_sequence` with the same arguments, including the `base` and
`cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_c_add_x_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "cAddXPow" :
  tactic

/-- Certificate form of `rr_product_lift_C_sequence`: with `certificate := scalar` it runs
`rr_product_lift_C_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_scalar)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalar" :
  tactic

/-- Certificate form of `rr_product_lift_C_sequence`: with `certificate := scalar` it runs
`rr_product_lift_C_sequence` with the same arguments, including the `base` and `cutoff` of the
cutoff form. -/
syntax (name := rr_product_lift_sequence_scalar_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalar" :
  tactic

/-- Certificate form of `rr_product_lift_C_sequence_auto`: with `certificate := scalarAuto` it runs
`rr_product_lift_C_sequence_auto` with the same arguments. -/
syntax (name := rr_product_lift_sequence_scalar_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarAuto" :
  tactic

/-- Certificate form of `rr_product_lift_C_sequence_auto`: with `certificate := scalarAuto` it runs
`rr_product_lift_C_sequence_auto` with the same arguments, including the `base` and `cutoff` of the
cutoff form. -/
syntax (name := rr_product_lift_sequence_scalar_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarAuto" :
  tactic

/-- Certificate form of `rr_product_lift_C_pow_sequence`: with `certificate := scalarPow` it runs
`rr_product_lift_C_pow_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_scalar_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarPow" :
  tactic

/-- Certificate form of `rr_product_lift_C_pow_sequence`: with `certificate := scalarPow` it runs
`rr_product_lift_C_pow_sequence` with the same arguments, including the `base` and `cutoff` of the
cutoff form. -/
syntax (name := rr_product_lift_sequence_scalar_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarPow" :
  tactic

/-- Certificate form of `rr_product_lift_C_pow_sequence_auto`: with `certificate := scalarPowAuto`
it runs `rr_product_lift_C_pow_sequence_auto` with the same arguments. -/
syntax (name := rr_product_lift_sequence_scalar_pow_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarPowAuto" :
  tactic

/-- Certificate form of `rr_product_lift_C_pow_sequence_auto`: with `certificate := scalarPowAuto`
it runs `rr_product_lift_C_pow_sequence_auto` with the same arguments, including the `base` and
`cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_scalar_pow_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "scalarPowAuto" :
  tactic

/-- Certificate form of `rr_product_lift_affine_sequence`: with `certificate := affine` it runs
`rr_product_lift_affine_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_affine)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affine" :
  tactic

/-- Certificate form of `rr_product_lift_affine_sequence`: with `certificate := affine` it runs
`rr_product_lift_affine_sequence` with the same arguments, including the `base` and `cutoff` of the
cutoff form. -/
syntax (name := rr_product_lift_sequence_affine_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affine" :
  tactic

/-- Certificate form of `rr_product_lift_affine_sequence_auto`: with `certificate := affineAuto` it
runs `rr_product_lift_affine_sequence_auto` with the same arguments. -/
syntax (name := rr_product_lift_sequence_affine_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affineAuto" :
  tactic

/-- Certificate form of `rr_product_lift_affine_sequence_auto`: with `certificate := affineAuto` it
runs `rr_product_lift_affine_sequence_auto` with the same arguments, including the `base` and
`cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_affine_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affineAuto" :
  tactic

/-- Certificate form of `rr_product_lift_const_first_sequence`: with
`certificate := constFirstAffine` it runs `rr_product_lift_const_first_sequence` with the same
arguments. -/
syntax (name := rr_product_lift_sequence_const_first_affine)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffine" :
  tactic

/-- Certificate form of `rr_product_lift_const_first_sequence`: with
`certificate := constFirstAffine` it runs `rr_product_lift_const_first_sequence` with the same
arguments, including the `base` and `cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_const_first_affine_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffine" :
  tactic

/-- Certificate form of `rr_product_lift_const_first_sequence_auto`: with
`certificate := constFirstAffineAuto` it runs `rr_product_lift_const_first_sequence_auto` with the
same arguments. -/
syntax (name := rr_product_lift_sequence_const_first_affine_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffineAuto" :
  tactic

/-- Certificate form of `rr_product_lift_const_first_sequence_auto`: with
`certificate := constFirstAffineAuto` it runs `rr_product_lift_const_first_sequence_auto` with the
same arguments, including the `base` and `cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_const_first_affine_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffineAuto" :
  tactic

/-- Certificate form of `rr_product_lift_affine_pow_sequence`: with `certificate := affinePow` it
runs `rr_product_lift_affine_pow_sequence` with the same arguments. -/
syntax (name := rr_product_lift_sequence_affine_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affinePow" :
  tactic

/-- Certificate form of `rr_product_lift_affine_pow_sequence`: with `certificate := affinePow` it
runs `rr_product_lift_affine_pow_sequence` with the same arguments, including the `base` and
`cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_affine_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affinePow" :
  tactic

/-- Certificate form of `rr_product_lift_affine_pow_sequence_auto`: with
`certificate := affinePowAuto` it runs `rr_product_lift_affine_pow_sequence_auto` with the same
arguments. -/
syntax (name := rr_product_lift_sequence_affine_pow_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affinePowAuto" :
  tactic

/-- Certificate form of `rr_product_lift_affine_pow_sequence_auto`: with
`certificate := affinePowAuto` it runs `rr_product_lift_affine_pow_sequence_auto` with the same
arguments, including the `base` and `cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_affine_pow_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "affinePowAuto" :
  tactic

/-- Certificate form of `rr_product_lift_const_first_affine_pow_sequence`: with
`certificate := constFirstAffinePow` it runs `rr_product_lift_const_first_affine_pow_sequence` with
the same arguments. -/
syntax (name := rr_product_lift_sequence_const_first_affine_pow)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffinePow" :
  tactic

/-- Certificate form of `rr_product_lift_const_first_affine_pow_sequence`: with
`certificate := constFirstAffinePow` it runs `rr_product_lift_const_first_affine_pow_sequence` with
the same arguments, including the `base` and `cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_const_first_affine_pow_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "slope_ne" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffinePow" :
  tactic

/-- Certificate form of `rr_product_lift_const_first_affine_pow_sequence_auto`: with
`certificate := constFirstAffinePowAuto` it runs
`rr_product_lift_const_first_affine_pow_sequence_auto` with the same arguments. -/
syntax (name := rr_product_lift_sequence_const_first_affine_pow_auto)
  "rr_product_lift_sequence" " using "
    "quotient_realrooted" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffinePowAuto" :
  tactic

/-- Certificate form of `rr_product_lift_const_first_affine_pow_sequence_auto`: with
`certificate := constFirstAffinePowAuto` it runs
`rr_product_lift_const_first_affine_pow_sequence_auto` with the same arguments, including the `base`
and `cutoff` of the cutoff form. -/
syntax (name := rr_product_lift_sequence_const_first_affine_pow_auto_cutoff)
  "rr_product_lift_sequence" " using "
    "base" ":=" term ","
    "quotient_realrooted" ":=" term ","
    "cutoff" ":=" term ","
    "factorization" ":=" term ","
    "certificate" ":=" "constFirstAffinePowAuto" :
  tactic


macro_rules
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factor_realrooted := $hfactor:term,
        factorization := $hrow:term,
        certificate := suppliedFactor) =>
      `(tactic|
        rr_product_lift_sequence using
          quotient_realrooted := $hquot,
          factor_realrooted := $hfactor,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := suppliedFactor) =>
      `(tactic|
        rr_product_lift_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          factor_realrooted := $hfactor,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := auto) =>
      `(tactic|
        rr_product_lift_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := auto) =>
      `(tactic|
        rr_product_lift_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := rootZero) =>
      `(tactic|
        rr_product_lift_X_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := rootZero) =>
      `(tactic|
        rr_product_lift_X_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := rootZeroPow) =>
      `(tactic|
        rr_product_lift_X_pow_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := rootZeroPow) =>
      `(tactic|
        rr_product_lift_X_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := xAddC) =>
      `(tactic|
        rr_product_lift_X_add_C_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := xAddC) =>
      `(tactic|
        rr_product_lift_X_add_C_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := cAddX) =>
      `(tactic|
        rr_product_lift_C_add_X_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := cAddX) =>
      `(tactic|
        rr_product_lift_C_add_X_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := fixedXAddCPow) =>
      `(tactic|
        rr_product_lift_X_add_C_pow_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := fixedXAddCPow) =>
      `(tactic|
        rr_product_lift_X_add_C_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := rowXAddCPow) =>
      `(tactic|
        rr_product_lift_X_add_C_row_pow_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := rowXAddCPow) =>
      `(tactic|
        rr_product_lift_X_add_C_row_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := cAddXPow) =>
      `(tactic|
        rr_product_lift_C_add_X_pow_sequence using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := cAddXPow) =>
      `(tactic|
        rr_product_lift_C_add_X_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hscalar:term,
        factorization := $hrow:term,
        certificate := scalar) =>
      `(tactic|
        rr_product_lift_C_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := $hscalar,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hscalar:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := scalar) =>
      `(tactic|
        rr_product_lift_C_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := $hscalar,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := scalarAuto) =>
      `(tactic|
        rr_product_lift_C_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := scalarAuto) =>
      `(tactic|
        rr_product_lift_C_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        scalar_ne := $hscalar:term,
        factorization := $hrow:term,
        certificate := scalarPow) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          quotient_realrooted := $hquot,
          scalar_ne := $hscalar,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        scalar_ne := $hscalar:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := scalarPow) =>
      `(tactic|
        rr_product_lift_C_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          scalar_ne := $hscalar,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := scalarPowAuto) =>
      `(tactic|
        rr_product_lift_C_pow_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := scalarPowAuto) =>
      `(tactic|
        rr_product_lift_C_pow_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        factorization := $hrow:term,
        certificate := affine) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := affine) =>
      `(tactic|
        rr_product_lift_affine_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := affineAuto) =>
      `(tactic|
        rr_product_lift_affine_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := affineAuto) =>
      `(tactic|
        rr_product_lift_affine_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        factorization := $hrow:term,
        certificate := constFirstAffine) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := constFirstAffine) =>
      `(tactic|
        rr_product_lift_const_first_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := constFirstAffineAuto) =>
      `(tactic|
        rr_product_lift_const_first_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := constFirstAffineAuto) =>
      `(tactic|
        rr_product_lift_const_first_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        factorization := $hrow:term,
        certificate := affinePow) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := affinePow) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := affinePowAuto) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := affinePowAuto) =>
      `(tactic|
        rr_product_lift_affine_pow_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        factorization := $hrow:term,
        certificate := constFirstAffinePow) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        slope_ne := $hslope:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := constFirstAffinePow) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence using
          base := $hbase,
          quotient_realrooted := $hquot,
          slope_ne := $hslope,
          cutoff := $N,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        quotient_realrooted := $hquot:term,
        factorization := $hrow:term,
        certificate := constFirstAffinePowAuto) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence_auto using
          quotient_realrooted := $hquot,
          factorization := $hrow)
  | `(tactic|
      rr_product_lift_sequence using
        base := $hbase:term,
        quotient_realrooted := $hquot:term,
        cutoff := $N:term,
        factorization := $hrow:term,
        certificate := constFirstAffinePowAuto) =>
      `(tactic|
        rr_product_lift_const_first_affine_pow_sequence_auto using
          base := $hbase,
          quotient_realrooted := $hquot,
          cutoff := $N,
          factorization := $hrow)
end Tactic
end RealRooted
