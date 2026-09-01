import RealRooted.Tactic.Product

/-!
# OEIS product-parity certificate frontend

Parser declarations and dispatch rules for alternating scalar/product steps and
endpoint-pair certificates.
-/

namespace RealRooted
namespace Tactic

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

syntax (name := rr_product_parity_sequence_scalar_then_factor_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "factor_realrooted" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenFactorAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_x_add_c)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddC" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_x_add_c_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddCAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_c_add_x)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddX" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_c_add_x_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "linear_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddXAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_root_zero_pow)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenRootZeroPow" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_root_zero_pow_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenRootZeroPowAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_x_add_c_pow)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddCPow" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_x_add_c_pow_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenXAddCPowAuto" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_c_add_x_pow)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    "scalar_ne" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddXPow" :
  tactic

syntax (name := rr_product_parity_sequence_scalar_then_c_add_x_pow_auto)
  "rr_product_parity_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "scalar_step" ":=" term ","
    "factor_step" ":=" term ","
    "certificate" ":=" "scalarThenCAddXPowAuto" :
  tactic

syntax (name := rr_product_parity_lift_sequence_scalar_x_odd)
  "rr_product_parity_lift_sequence" " using "
    "even_realrooted" ":=" term ","
    "scalar_ne" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "scalarXOdd" :
  tactic

syntax (name := rr_endpoint_pair_sequence_sum_then_x)
  "rr_endpoint_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term ","
    "certificate" ":=" "sumThenX" :
  tactic

syntax (name := rr_endpoint_pair_sequence_realrooted_sum_then_x)
  "rr_endpoint_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term ","
    "certificate" ":=" "sumThenX" :
  tactic

syntax (name := rr_endpoint_pair_sequence_x_then_sum)
  "rr_endpoint_pair_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "certificate" ":=" "xThenSum" :
  tactic

syntax (name := rr_endpoint_pair_sequence_realrooted_x_then_sum)
  "rr_endpoint_pair_sequence_realrooted" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "certificate" ":=" "xThenSum" :
  tactic

syntax (name := rr_endpoint_pair_lift_sequence_sum_then_x)
  "rr_endpoint_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "sum_step" ":=" term ","
    "x_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "sumThenX" :
  tactic

syntax (name := rr_endpoint_pair_lift_sequence_x_then_sum)
  "rr_endpoint_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
    "even_factorization" ":=" term ","
    "odd_factorization" ":=" term ","
    "certificate" ":=" "xThenSum" :
  tactic

syntax (name := rr_endpoint_pair_lift_sequence_x_then_sum_swapped)
  "rr_endpoint_pair_lift_sequence" " using "
    "base" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "x_step" ":=" term ","
    "sum_step" ":=" term ","
    "coprime" ":=" term ","
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
        coprime := $hcop:term,
        certificate := sumThenX) =>
      `(tactic|
        rr_endpoint_sum_then_X_pair_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          sum_step := $hsum_step,
          x_step := $hx_step,
          coprime := $hcop)
  | `(tactic|
      rr_endpoint_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term,
        certificate := sumThenX) =>
      `(tactic|
        rr_endpoint_sum_then_X_pair_sequence_realrooted using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          sum_step := $hsum_step,
          x_step := $hx_step,
          coprime := $hcop)
  | `(tactic|
      rr_endpoint_pair_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        certificate := xThenSum) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_sequence using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step,
          coprime := $hcop)
  | `(tactic|
      rr_endpoint_pair_sequence_realrooted using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
        certificate := xThenSum) =>
      `(tactic|
        rr_endpoint_X_then_sum_pair_sequence_realrooted using
          base := $hbase,
          left_nonneg := $hleft_nonneg,
          right_nonneg := $hright_nonneg,
          x_step := $hx_step,
          sum_step := $hsum_step,
          coprime := $hcop)
  | `(tactic|
      rr_endpoint_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        sum_step := $hsum_step:term,
        x_step := $hx_step:term,
        coprime := $hcop:term,
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
          coprime := $hcop,
          even_factorization := $heven,
          odd_factorization := $hodd)
  | `(tactic|
      rr_endpoint_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
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
          coprime := $hcop,
          even_factorization := $heven,
          odd_factorization := $hodd)
  | `(tactic|
      rr_endpoint_pair_lift_sequence using
        base := $hbase:term,
        left_nonneg := $hleft_nonneg:term,
        right_nonneg := $hright_nonneg:term,
        x_step := $hx_step:term,
        sum_step := $hsum_step:term,
        coprime := $hcop:term,
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
          coprime := $hcop,
          even_factorization := $heven,
          odd_factorization := $hodd)
end Tactic
end RealRooted
