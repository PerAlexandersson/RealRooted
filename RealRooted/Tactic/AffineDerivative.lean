import RealRooted.AffineDerivative

/-!
# Affine-derivative tactic frontends

Thin wrappers for the affine-derivative interlacing theorem
`C c * f + (1 - X) * f.derivative`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_affine_deriv_eval_at_root_named)
  "rr_affine_deriv_eval_at_root" " using " "root" ":=" term :
  tactic

syntax (name := rr_affine_deriv_eval_zero_iff_named)
  "rr_affine_deriv_eval_zero_iff" " using "
    "root" ":=" term ","
    "root_nonpos" ":=" term :
  tactic

syntax (name := rr_affine_deriv_coeff_named)
  "rr_affine_deriv_coeff" " using " "degree_ge_one" ":=" term :
  tactic

syntax (name := rr_affine_deriv_natDegree_named)
  "rr_affine_deriv_natDegree" " using "
    "nonzero" ":=" term ","
    "degree_ge_one" ":=" term ","
    "scalar_ne_degree" ":=" term :
  tactic

syntax (name := rr_affine_deriv_leadingCoeff_named)
  "rr_affine_deriv_leadingCoeff" " using "
    "nonzero" ":=" term ","
    "degree_ge_one" ":=" term ","
    "scalar_ne_degree" ":=" term :
  tactic

syntax (name := rr_affine_deriv_ne_zero_named)
  "rr_affine_deriv_ne_zero" " using "
    "nonzero" ":=" term ","
    "degree_ge_one" ":=" term ","
    "scalar_ne_degree" ":=" term :
  tactic

syntax (name := rr_prec_affine_derivative_strong_named)
  "rr_prec_affine_derivative_strong" " using "
    "splits" ":=" term ","
    "degree_ge_two" ":=" term ","
    "pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "scalar_gt_degree" ":=" term :
  tactic

syntax (name := rr_prec_affine_derivative_degree_one_named)
  "rr_prec_affine_derivative_degree_one" " using "
    "splits" ":=" term ","
    "degree_eq_one" ":=" term ","
    "pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "scalar_gt_degree" ":=" term :
  tactic

syntax (name := rr_prec_affine_derivative_named)
  "rr_prec_affine_derivative" " using "
    "splits" ":=" term ","
    "degree_ge_one" ":=" term ","
    "pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "scalar_gt_degree" ":=" term :
  tactic

syntax (name := rr_prec_affine_derivative_nonneg_named)
  "rr_prec_affine_derivative_nonneg" " using "
    "splits" ":=" term ","
    "degree_ge_one" ":=" term ","
    "nonneg" ":=" term ","
    "scalar_gt_degree" ":=" term :
  tactic

syntax (name := rr_affine_deriv_eval_pos_iff_named)
  "rr_affine_deriv_eval_pos_iff" " using "
    "root" ":=" term ","
    "root_nonpos" ":=" term :
  tactic

syntax (name := rr_affine_deriv_eval_neg_iff_named)
  "rr_affine_deriv_eval_neg_iff" " using "
    "root" ":=" term ","
    "root_nonpos" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_affine_deriv_eval_at_root using root := $hr:term) =>
      `(tactic| exact RealRooted.eval_affineDeriv_at_root $hr _)
  | `(tactic|
      rr_affine_deriv_eval_zero_iff using
        root := $hr:term,
        root_nonpos := $hrnp:term) =>
      `(tactic| exact RealRooted.eval_affineDeriv_eq_zero_iff $hr _ $hrnp)
  | `(tactic| rr_affine_deriv_coeff using degree_ge_one := $hdeg:term) =>
      `(tactic| exact RealRooted.coeff_affineDeriv $hdeg _)
  | `(tactic|
      rr_affine_deriv_natDegree using
        nonzero := $hf:term,
        degree_ge_one := $hdeg:term,
        scalar_ne_degree := $hc:term) =>
      `(tactic| exact RealRooted.natDegree_affineDeriv $hf $hdeg $hc)
  | `(tactic|
      rr_affine_deriv_leadingCoeff using
        nonzero := $hf:term,
        degree_ge_one := $hdeg:term,
        scalar_ne_degree := $hc:term) =>
      `(tactic| exact RealRooted.leadingCoeff_affineDeriv $hf $hdeg $hc)
  | `(tactic|
      rr_affine_deriv_ne_zero using
        nonzero := $hf:term,
        degree_ge_one := $hdeg:term,
        scalar_ne_degree := $hc:term) =>
      `(tactic| exact RealRooted.affineDeriv_ne_zero $hf $hdeg $hc)
  | `(tactic|
      rr_prec_affine_derivative_strong using
        splits := $hsplits:term,
        degree_ge_two := $hdeg:term,
        pos_lc := $hpos:term,
        roots_nonpos := $hroots:term,
        scalar_gt_degree := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_affine_derivative $hsplits $hdeg $hpos $hroots $hc)
  | `(tactic|
      rr_prec_affine_derivative_degree_one using
        splits := $hsplits:term,
        degree_eq_one := $hdeg:term,
        pos_lc := $hpos:term,
        roots_nonpos := $hroots:term,
        scalar_gt_degree := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_affine_derivative_deg_one
          $hsplits $hdeg $hpos $hroots $hc)
  | `(tactic|
      rr_prec_affine_derivative using
        splits := $hsplits:term,
        degree_ge_one := $hdeg:term,
        pos_lc := $hpos:term,
        roots_nonpos := $hroots:term,
        scalar_gt_degree := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_affine_derivative' $hsplits $hdeg $hpos $hroots $hc)
  | `(tactic|
      rr_prec_affine_derivative_nonneg using
        splits := $hsplits:term,
        degree_ge_one := $hdeg:term,
        nonneg := $hnn:term,
        scalar_gt_degree := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_affine_derivative_of_nonnegCoeffs
          $hsplits $hdeg $hnn $hc)
  | `(tactic|
      rr_affine_deriv_eval_pos_iff using
        root := $hr:term,
        root_nonpos := $hrnp:term) =>
      `(tactic| exact RealRooted.eval_affineDeriv_pos_iff $hr _ $hrnp)
  | `(tactic|
      rr_affine_deriv_eval_neg_iff using
        root := $hr:term,
        root_nonpos := $hrnp:term) =>
      `(tactic| exact RealRooted.eval_affineDeriv_neg_iff $hr _ $hrnp)

end Tactic
end RealRooted
