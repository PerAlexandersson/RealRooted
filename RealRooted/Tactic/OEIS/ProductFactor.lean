import RealRooted.Tactic.J1Chebyshev
import RealRooted.Tactic.J1Gap3Reciprocal
import RealRooted.Tactic.Product

/-!
# OEIS product-factor certificate frontend

Parser declarations and dispatch rules for finite-product factor certificates,
including formula and J1 model endpoints.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_product_factor_sequence_supplied_factor)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "suppliedFactor" :
  tactic

syntax (name := rr_product_factor_sequence_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "auto" :
  tactic

syntax (name := rr_product_factor_sequence_affine)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affine" :
  tactic

syntax (name := rr_product_factor_sequence_affine_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affineAuto" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffine" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffineAuto" :
  tactic

syntax (name := rr_product_factor_sequence_x_add_c)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "xAddC" :
  tactic

syntax (name := rr_product_factor_sequence_c_add_x)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "cAddX" :
  tactic

syntax (name := rr_product_factor_sequence_root_zero_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "rootZeroPow" :
  tactic

syntax (name := rr_product_factor_sequence_x_add_c_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "xAddCPow" :
  tactic

syntax (name := rr_product_factor_sequence_c_add_x_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "cAddXPow" :
  tactic

syntax (name := rr_product_factor_sequence_scalar)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalar" :
  tactic

syntax (name := rr_product_factor_sequence_scalar_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarAuto" :
  tactic

syntax (name := rr_product_factor_sequence_scalar_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarPow" :
  tactic

syntax (name := rr_product_factor_sequence_scalar_pow_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "scalarPowAuto" :
  tactic

syntax (name := rr_product_factor_sequence_affine_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affinePow" :
  tactic

syntax (name := rr_product_factor_sequence_affine_pow_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "affinePowAuto" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine_pow)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    "slope_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffinePow" :
  tactic

syntax (name := rr_product_factor_sequence_const_first_affine_pow_auto)
  "rr_product_factor_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "constFirstAffinePowAuto" :
  tactic

syntax (name := rr_product_formula_sequence_finite_linear_product)
  "rr_product_formula_sequence" " using "
    "formula" ":=" term ","
    "certificate" ":=" "finiteLinearProduct" :
  tactic

syntax (name := rr_product_formula_sequence_scalar_finite_linear_product)
  "rr_product_formula_sequence" " using "
    "scalar_ne_zero" ":=" term ","
    "root_grid" ":=" term ","
    "certificate" ":=" "scalarFiniteLinearProduct" :
  tactic

syntax (name := rr_j1_factorable_sequence_realrooted_finite_linear_product)
  "rr_j1_factorable_sequence_realrooted" " using "
    "scalar_ne_zero" ":=" term ","
    "root_grid" ":=" term ","
    "certificate" ":=" "finiteLinearProduct" :
  tactic

syntax (name := rr_j1_gap3_reciprocal_sequence_realrooted_model_realrooted)
  "rr_j1_gap3_reciprocal_sequence_realrooted" " using "
    "model_realrooted" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term ","
    "certificate" ":=" "modelRealRooted" :
  tactic

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
          | rr_product_X_add_C_pow_sequence using
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
          | rr_product_X_add_C_pow_sequence using
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
          (RealRooted.j1FactorableLag3Sequence_realRooted $hc $hroot))
  | `(tactic|
      rr_j1_gap3_reciprocal_sequence_realrooted using
        model_realrooted := $hmodel:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term,
        certificate := modelRealRooted) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_j1_gap3_reciprocal_sequence
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
          (RealRooted.isRealRooted_of_j1_gap3_reciprocal_pf_sequence
            $hmodel $hmodel_ne $hdegree $hreciprocal))
end Tactic
end RealRooted
