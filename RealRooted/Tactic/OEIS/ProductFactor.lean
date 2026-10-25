module

public import RealRooted.Tactic.J1Chebyshev
public import RealRooted.Tactic.J1Gap3Reciprocal
public import RealRooted.Tactic.Product

/-!
# OEIS product-factor certificate frontend

Parser declarations and dispatch rules for finite-product factor certificates,
including formula and J1 model endpoints.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

/-- Certificate `suppliedFactor` of `rr_product_factor_sequence`. Closes
`∀ n, P n ≠ 0 ∧ (P n).Splits` for a recurrence `P (n + 1) = F n * P n` from `base`, the
real-rootedness of `P 0`, `factor_realrooted`, the real-rootedness of every factor `F n`, an
optional `cutoff` and `recurrence`. -/
syntax (name := rr_product_factor_sequence_supplied_factor)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "suppliedFactor" :
  tactic

/-- Certificate `auto` of `rr_product_factor_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for a
one-step product recurrence from `base`, an optional `cutoff` and `recurrence`, by trying in order
the checked dispatchers for root-zero powers, scalars, affine factors and affine powers, and then
the families `X + C t`, `C t + X`, `X ^ m` and `(C t + X) ^ m`. -/
syntax (name := rr_product_factor_sequence_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "auto" :
  tactic

/-- Certificate `affine` of `rr_product_factor_sequence`, dispatching to
`rr_product_affine_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = (C (s n) * X + C (t n)) * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`
and `slope_ne : ∀ n, s n ≠ 0`; the optional `cutoff : N` makes `base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_affine)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affine" :
  tactic

/-- Certificate `affineAuto` of `rr_product_factor_sequence`, dispatching to
`rr_product_affine_sequence_auto`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = (C (s n) * X + C (t n)) * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`;
the optional `cutoff : N` makes `base` cover all `n ≤ N`. The nonvanishing `slope_ne` is proved
automatically. -/
syntax (name := rr_product_factor_sequence_affine_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affineAuto" :
  tactic

/-- Certificate `constFirstAffine` of `rr_product_factor_sequence`, dispatching to
`rr_product_const_first_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = (C (t n) + C (s n) * X) * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`
and `slope_ne : ∀ n, s n ≠ 0`; the optional `cutoff : N` makes `base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_const_first_affine)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffine" :
  tactic

/-- Certificate `constFirstAffineAuto` of `rr_product_factor_sequence`, dispatching to
`rr_product_const_first_sequence_auto`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step
recurrence `recurrence : ∀ n, P (n + 1) = (C (t n) + C (s n) * X) * P n` from
`base : P 0 ≠ 0 ∧ (P 0).Splits`; the optional `cutoff : N` makes `base` cover all `n ≤ N`. The
nonvanishing `slope_ne` is proved automatically. -/
syntax (name := rr_product_factor_sequence_const_first_affine_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffineAuto" :
  tactic

/-- Certificate `xAddC` of `rr_product_factor_sequence`, dispatching to `rr_product_X_sequence`.
Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = (X + C (t n)) * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`; the
optional `cutoff : N` makes `base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_x_add_c)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "xAddC" :
  tactic

/-- Certificate `cAddX` of `rr_product_factor_sequence`, dispatching to
`rr_product_C_add_X_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = (C (t n) + X) * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`; the
optional `cutoff : N` makes `base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_c_add_x)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "cAddX" :
  tactic

/-- Certificate `rootZeroPow` of `rr_product_factor_sequence`, dispatching to
`rr_product_X_pow_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = X ^ m n * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`; the optional
`cutoff : N` makes `base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_root_zero_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "rootZeroPow" :
  tactic

/-- Certificate `xAddCPow` of `rr_product_factor_sequence`, dispatching to
`rr_product_X_add_C_pow_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = (X + C (t n)) ^ m n * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`; the
optional `cutoff : N` makes `base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_x_add_c_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "xAddCPow" :
  tactic

/-- Certificate `cAddXPow` of `rr_product_factor_sequence`, dispatching to
`rr_product_C_add_X_pow_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = (C (t n) + X) ^ m n * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`; the
optional `cutoff : N` makes `base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_c_add_x_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "cAddXPow" :
  tactic

/-- Certificate `scalar` of `rr_product_factor_sequence`, dispatching to
`rr_product_scalar_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = C (a n) * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits` and
`scalar_ne : ∀ n, a n ≠ 0`; the optional `cutoff : N` makes `base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_scalar)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalar" :
  tactic

/-- Certificate `scalarAuto` of `rr_product_factor_sequence`, dispatching to
`rr_product_scalar_sequence_auto`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = C (a n) * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`; the optional
`cutoff : N` makes `base` cover all `n ≤ N`. The nonvanishing `scalar_ne` is proved
automatically. -/
syntax (name := rr_product_factor_sequence_scalar_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarAuto" :
  tactic

/-- Certificate `scalarPow` of `rr_product_factor_sequence`, dispatching to
`rr_product_C_pow_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = C (c n) ^ m n * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits` and
`scalar_ne : ∀ n, c n ≠ 0`; the optional `cutoff : N` makes `base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_scalar_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarPow" :
  tactic

/-- Certificate `scalarPowAuto` of `rr_product_factor_sequence`, dispatching to
`rr_product_C_pow_sequence_auto`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = C (c n) ^ m n * P n` from `base : P 0 ≠ 0 ∧ (P 0).Splits`; the
optional `cutoff : N` makes `base` cover all `n ≤ N`. The nonvanishing `scalar_ne` is proved
automatically. -/
syntax (name := rr_product_factor_sequence_scalar_pow_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarPowAuto" :
  tactic

/-- Certificate `affinePow` of `rr_product_factor_sequence`, dispatching to
`rr_product_affine_pow_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step recurrence
`recurrence : ∀ n, P (n + 1) = (C (s n) * X + C (t n)) ^ m n * P n` from
`base : P 0 ≠ 0 ∧ (P 0).Splits` and `slope_ne : ∀ n, s n ≠ 0`; the optional `cutoff : N` makes
`base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_affine_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affinePow" :
  tactic

/-- Certificate `affinePowAuto` of `rr_product_factor_sequence`, dispatching to
`rr_product_affine_pow_sequence_auto`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step
recurrence `recurrence : ∀ n, P (n + 1) = (C (s n) * X + C (t n)) ^ m n * P n` from
`base : P 0 ≠ 0 ∧ (P 0).Splits`; the optional `cutoff : N` makes `base` cover all `n ≤ N`. The
nonvanishing `slope_ne` is proved automatically. -/
syntax (name := rr_product_factor_sequence_affine_pow_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affinePowAuto" :
  tactic

/-- Certificate `constFirstAffinePow` of `rr_product_factor_sequence`, dispatching to
`rr_product_const_first_affine_pow_sequence`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the one-step
recurrence `recurrence : ∀ n, P (n + 1) = (C (t n) + C (s n) * X) ^ m n * P n` from
`base : P 0 ≠ 0 ∧ (P 0).Splits` and `slope_ne : ∀ n, s n ≠ 0`; the optional `cutoff : N` makes
`base` cover all `n ≤ N`. -/
syntax (name := rr_product_factor_sequence_const_first_affine_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffinePow" :
  tactic

/-- Certificate `constFirstAffinePowAuto` of `rr_product_factor_sequence`, dispatching to
`rr_product_const_first_affine_pow_sequence_auto`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for the
one-step recurrence `recurrence : ∀ n, P (n + 1) = (C (t n) + C (s n) * X) ^ m n * P n` from
`base : P 0 ≠ 0 ∧ (P 0).Splits`; the optional `cutoff : N` makes `base` cover all `n ≤ N`. The
nonvanishing `slope_ne` is proved automatically. -/
syntax (name := rr_product_factor_sequence_const_first_affine_pow_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffinePowAuto" :
  tactic

/-- Certificate `finiteLinearProduct` of `rr_product_formula_sequence`. Closes
`∀ n, P n ≠ 0 ∧ (P n).Splits` for rows given as finite products of real linear factors,
`formula : ∀ n, P n = ∏ j ∈ Finset.range n, (X - C (root n j))`. -/
syntax (name := rr_product_formula_sequence_finite_linear_product)
  "rr_product_formula_sequence" " using "
    "formula" ":=" term ","
    "certificate" ":=" "finiteLinearProduct" :
  tactic

/-- Certificate `scalarFiniteLinearProduct` of `rr_product_formula_sequence`. Closes
`∀ n, P n ≠ 0 ∧ (P n).Splits` for rows given as nonzero scalar multiples of finite products of real
linear factors: `scalar_ne_zero : ∀ n, c n ≠ 0` and
`root_grid : ∀ n, P n = C (c n) * ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))`. -/
syntax (name := rr_product_formula_sequence_scalar_finite_linear_product)
  "rr_product_formula_sequence" " using "
    "scalar_ne_zero" ":=" term ","
    "root_grid" ":=" term ","
    "certificate" ":=" "scalarFiniteLinearProduct" :
  tactic

/-- J1 form of the `scalarFiniteLinearProduct` certificate of `rr_product_formula_sequence`. Closes
`∀ n, P n ≠ 0 ∧ (P n).Splits` for rows
`P n = C (c n) * ∏ j ∈ Finset.range (rootCount n), (X - C (roots n j))` (`root_grid`) with
`scalar_ne_zero : ∀ n, c n ≠ 0`. -/
syntax (name := rr_j1_factorable_sequence_realrooted_finite_linear_product)
  "rr_j1_factorable_sequence_realrooted" " using "
    "scalar_ne_zero" ":=" term ","
    "root_grid" ":=" term ","
    "certificate" ":=" "finiteLinearProduct" :
  tactic

/-- Certificate `modelRealRooted`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for rows that are
degree-padded reciprocal reflections of a real-rooted model:
`model_realrooted : ∀ n, R n ≠ 0 ∧ (R n).Splits`, `degree : ∀ n, (R n).natDegree ≤ D n` and
`reciprocal : ∀ n, P n = reciprocalShift (D n) (R n)`. -/
syntax (name := rr_j1_gap3_reciprocal_sequence_realrooted_model_realrooted)
  "rr_j1_gap3_reciprocal_sequence_realrooted" " using "
    "model_realrooted" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term ","
    "certificate" ":=" "modelRealRooted" :
  tactic

/-- Certificate `modelPF`. Closes `∀ n, P n ≠ 0 ∧ (P n).Splits` for rows that are degree-padded
reciprocal reflections of a PF model: `model_pf : ∀ n, IsPFPolynomial (R n)`,
`model_ne : ∀ n, R n ≠ 0`, `degree : ∀ n, (R n).natDegree ≤ D n` and
`reciprocal : ∀ n, P n = reciprocalShift (D n) (R n)`. -/
syntax (name := rr_j1_gap3_reciprocal_sequence_realrooted_model_pf)
  "rr_j1_gap3_reciprocal_sequence_realrooted" " using "
    "model_pf" ":=" term ","
    "model_ne" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term ","
    "certificate" ":=" "modelPF" :
  tactic

macro_rules
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        recurrence := $hrec:term,
        certificate := suppliedFactor) =>
      `(tactic|
        rr_product_factor_sequence using
          base := $hbase,
          factor_realrooted := $hfactor,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        factor_realrooted := $hfactor:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := suppliedFactor) =>
      `(tactic|
        rr_product_factor_sequence using
          base := $hbase,
          factor_realrooted := $hfactor,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := auto) =>
      `(tactic|
        first
          | rr_product_checked_root_zero_pow_sequence_auto using
              base := $hbase,
              recurrence := $hrec
          | rr_product_checked_scalar_sequence_auto using
              base := $hbase,
              recurrence := $hrec
          | rr_product_checked_affine_sequence_auto using
              base := $hbase,
              recurrence := $hrec
          | rr_product_checked_affine_pow_sequence_auto using
              base := $hbase,
              recurrence := $hrec
          | rr_product_X_sequence using
              base := $hbase,
              recurrence := $hrec
          | rr_product_C_add_X_sequence using
              base := $hbase,
              recurrence := $hrec
          | rr_product_X_pow_sequence using
              base := $hbase,
              recurrence := $hrec
          | rr_product_C_add_X_pow_sequence using
              base := $hbase,
              recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := auto) =>
      `(tactic|
        first
          | rr_product_checked_root_zero_pow_sequence_auto using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_checked_scalar_sequence_auto using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_checked_affine_sequence_auto using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_checked_affine_pow_sequence_auto using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_X_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_C_add_X_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_X_pow_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_C_add_X_pow_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := affine) =>
      `(tactic|
        rr_product_affine_sequence using
          base := $hbase,
          slope_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := affine) =>
      `(tactic|
        rr_product_affine_sequence using
          base := $hbase,
          slope_ne := $hs,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := affineAuto) =>
      `(tactic|
        rr_product_affine_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := affineAuto) =>
      `(tactic|
        rr_product_affine_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := constFirstAffine) =>
      `(tactic|
        rr_product_const_first_sequence using
          base := $hbase,
          slope_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := constFirstAffine) =>
      `(tactic|
        rr_product_const_first_sequence using
          base := $hbase,
          slope_ne := $hs,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := constFirstAffineAuto) =>
      `(tactic|
        rr_product_const_first_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := constFirstAffineAuto) =>
      `(tactic|
        rr_product_const_first_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := xAddC) =>
      `(tactic|
        rr_product_X_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := xAddC) =>
      `(tactic|
        rr_product_X_sequence using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := cAddX) =>
      `(tactic|
        rr_product_C_add_X_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := cAddX) =>
      `(tactic|
        rr_product_C_add_X_sequence using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := rootZeroPow) =>
      `(tactic|
        rr_product_X_pow_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := rootZeroPow) =>
      `(tactic|
        rr_product_X_pow_sequence using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := xAddCPow) =>
      `(tactic|
        rr_product_X_add_C_pow_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := xAddCPow) =>
      `(tactic|
        rr_product_X_add_C_pow_sequence using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := cAddXPow) =>
      `(tactic|
        rr_product_C_add_X_pow_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := cAddXPow) =>
      `(tactic|
        rr_product_C_add_X_pow_sequence using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        scalar_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := scalar) =>
      `(tactic|
        rr_product_scalar_sequence using
          base := $hbase,
          scalar_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        scalar_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := scalar) =>
      `(tactic|
        rr_product_scalar_sequence using
          base := $hbase,
          scalar_ne := $hs,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := scalarAuto) =>
      `(tactic|
        rr_product_scalar_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := scalarAuto) =>
      `(tactic|
        rr_product_scalar_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        scalar_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := scalarPow) =>
      `(tactic|
        rr_product_C_pow_sequence using
          base := $hbase,
          scalar_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        scalar_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := scalarPow) =>
      `(tactic|
        rr_product_C_pow_sequence using
          base := $hbase,
          scalar_ne := $hs,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := scalarPowAuto) =>
      `(tactic|
        rr_product_C_pow_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := scalarPowAuto) =>
      `(tactic|
        rr_product_C_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := affinePow) =>
      `(tactic|
        rr_product_affine_pow_sequence using
          base := $hbase,
          slope_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := affinePow) =>
      `(tactic|
        rr_product_affine_pow_sequence using
          base := $hbase,
          slope_ne := $hs,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := affinePowAuto) =>
      `(tactic|
        rr_product_affine_pow_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := affinePowAuto) =>
      `(tactic|
        rr_product_affine_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        recurrence := $hrec:term,
        certificate := constFirstAffinePow) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence using
          base := $hbase,
          slope_ne := $hs,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        slope_ne := $hs:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := constFirstAffinePow) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence using
          base := $hbase,
          slope_ne := $hs,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := constFirstAffinePowAuto) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence_auto using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_factor_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := constFirstAffinePowAuto) =>
      `(tactic|
        rr_product_const_first_affine_pow_sequence_auto using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_formula_sequence using
        formula := $hroot:term,
        certificate := finiteLinearProduct) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.finiteLinearProductSequence_realRooted $hroot))
  | `(tactic|
      rr_product_formula_sequence using
        scalar_ne_zero := $hc:term,
        root_grid := $hroot:term,
        certificate := scalarFiniteLinearProduct) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.finiteLinearProductScalarSequence_realRooted $hc $hroot))
  | `(tactic|
      rr_j1_factorable_sequence_realrooted using
        scalar_ne_zero := $hc:term,
        root_grid := $hroot:term,
        certificate := finiteLinearProduct) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.finiteLinearProductScalarSequence_realRooted $hc $hroot))
  | `(tactic|
      rr_j1_gap3_reciprocal_sequence_realrooted using
        model_realrooted := $hmodel:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term,
        certificate := modelRealRooted) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_reciprocalShift_sequence
            $hmodel $hdegree $hreciprocal))
  | `(tactic|
      rr_j1_gap3_reciprocal_sequence_realrooted using
        model_pf := $hmodel:term,
        model_ne := $hmodel_ne:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term,
        certificate := modelPF) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_reciprocalShift_pf_sequence
            $hmodel $hmodel_ne $hdegree $hreciprocal))
end Tactic
end RealRooted
