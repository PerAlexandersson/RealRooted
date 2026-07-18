import RealRooted.GammaRealRoots

/-!
# Gamma-real-rootedness tactic frontends

Thin wrappers for gamma transforms and the gamma-polynomial
real-rootedness/nonpositive-root bridge.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_gamma_transform_add_named)
  "rr_gamma_transform_add" :
  tactic

syntax (name := rr_gamma_transform_C_mul_named)
  "rr_gamma_transform_C_mul" :
  tactic

syntax (name := rr_gamma_transform_monomial_named)
  "rr_gamma_transform_monomial" :
  tactic

syntax (name := rr_gamma_transform_fixed_named)
  "rr_gamma_transform_fixed" :
  tactic

syntax (name := rr_gamma_basis_nonneg_named)
  "rr_gamma_basis_nonneg" :
  tactic

syntax (name := rr_gamma_transform_nonneg_named)
  "rr_gamma_transform_nonneg" " using " "nonneg" ":=" term :
  tactic

syntax (name := rr_gamma_transform_natDegree_le_named)
  "rr_gamma_transform_natDegree_le" :
  tactic

syntax (name := rr_gamma_transform_injective_named)
  "rr_gamma_transform_injective" " using "
    "left_degree" ":=" term ","
    "right_degree" ":=" term ","
    "transform_eq" ":=" term :
  tactic

syntax (name := rr_gamma_transform_zero_iff_named)
  "rr_gamma_transform_zero_iff" " using " "gamma_degree" ":=" term :
  tactic

syntax (name := rr_gamma_transform_X_mul_two_named)
  "rr_gamma_transform_X_mul_two" :
  tactic

syntax (name := rr_gamma_transform_pad_two_named)
  "rr_gamma_transform_pad_two" " using " "gamma_degree" ":=" term :
  tactic

syntax (name := rr_gamma_transform_odd_named)
  "rr_gamma_transform_odd" :
  tactic

syntax (name := rr_gamma_transform_realrooted_nonneg_named)
  "rr_gamma_transform_realrooted_nonneg" " using "
    "gamma_degree" ":=" term ","
    "gamma_nonzero" ":=" term ","
    "gamma_splits" ":=" term ","
    "gamma_nonneg" ":=" term :
  tactic

syntax (name := rr_gamma_transform_roots_nonpos_nonneg_named)
  "rr_gamma_transform_roots_nonpos_nonneg" " using "
    "gamma_degree" ":=" term ","
    "gamma_nonzero" ":=" term ","
    "gamma_splits" ":=" term ","
    "gamma_nonneg" ":=" term :
  tactic

syntax (name := rr_gamma_transform_realrooted_nonpos_named)
  "rr_gamma_transform_realrooted_nonpos" " using "
    "gamma_degree" ":=" term ","
    "gamma_nonzero" ":=" term ","
    "gamma_splits" ":=" term ","
    "gamma_roots_nonpos" ":=" term :
  tactic

syntax (name := rr_gamma_transform_backward_minimal_named)
  "rr_gamma_transform_backward_minimal" " using "
    "transform_nonzero" ":=" term ","
    "transform_splits" ":=" term ","
    "transform_roots_nonpos" ":=" term :
  tactic

syntax (name := rr_gamma_transform_backward_named)
  "rr_gamma_transform_backward" " using "
    "gamma_degree" ":=" term ","
    "transform_nonzero" ":=" term ","
    "transform_splits" ":=" term ","
    "transform_roots_nonpos" ":=" term :
  tactic

syntax (name := rr_gamma_realrooted_iff_named)
  "rr_gamma_realrooted_iff" " using "
    "gamma_degree" ":=" term ","
    "polynomial_degree" ":=" term ","
    "symmetric" ":=" term ","
    "expansion" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_gamma_transform_add) =>
      `(tactic| exact RealRooted.gammaTransform_add _ _ _)
  | `(tactic| rr_gamma_transform_C_mul) =>
      `(tactic| exact RealRooted.gammaTransform_C_mul _ _ _)
  | `(tactic| rr_gamma_transform_monomial) =>
      `(tactic| exact RealRooted.gammaTransform_monomial _ _ _)
  | `(tactic| rr_gamma_transform_fixed) =>
      `(tactic| exact RealRooted.gammaTransform_fixed _ _)
  | `(tactic| rr_gamma_basis_nonneg) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_gammaBasisTerm _ _)
  | `(tactic| rr_gamma_transform_nonneg using nonneg := $hγ:term) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_gammaTransform $hγ)
  | `(tactic| rr_gamma_transform_natDegree_le) =>
      `(tactic| exact RealRooted.natDegree_gammaTransform_le _ _)
  | `(tactic|
      rr_gamma_transform_injective using
        left_degree := $hγ:term,
        right_degree := $hδ:term,
        transform_eq := $hEq:term) =>
      `(tactic| exact RealRooted.gammaTransform_injective_of_natDegree_le $hγ $hδ $hEq)
  | `(tactic| rr_gamma_transform_zero_iff using gamma_degree := $hγ:term) =>
      `(tactic| exact RealRooted.gammaTransform_eq_zero_iff_of_natDegree_le $hγ)
  | `(tactic| rr_gamma_transform_X_mul_two) =>
      `(tactic| exact RealRooted.gammaTransform_X_mul_two _ _)
  | `(tactic| rr_gamma_transform_pad_two using gamma_degree := $hγ:term) =>
      `(tactic| exact RealRooted.gammaTransform_pad_two $hγ)
  | `(tactic| rr_gamma_transform_odd) =>
      `(tactic| exact RealRooted.gammaTransform_odd _ _)
  | `(tactic|
      rr_gamma_transform_realrooted_nonneg using
        gamma_degree := $hdeg:term,
        gamma_nonzero := $hne:term,
        gamma_splits := $hsplits:term,
        gamma_nonneg := $hnn:term) =>
      `(tactic|
        exact
          RealRooted.isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
            $hdeg $hne $hsplits $hnn)
  | `(tactic|
      rr_gamma_transform_roots_nonpos_nonneg using
        gamma_degree := $hdeg:term,
        gamma_nonzero := $hne:term,
        gamma_splits := $hsplits:term,
        gamma_nonneg := $hnn:term) =>
      `(tactic|
        exact
          RealRooted.hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
            $hdeg $hne $hsplits $hnn)
  | `(tactic|
      rr_gamma_transform_realrooted_nonpos using
        gamma_degree := $hdeg:term,
        gamma_nonzero := $hne:term,
        gamma_splits := $hsplits:term,
        gamma_roots_nonpos := $hnp:term) =>
      `(tactic|
        exact
          isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
            $hdeg $hne $hsplits $hnp)
  | `(tactic|
      rr_gamma_transform_backward_minimal using
        transform_nonzero := $hne:term,
        transform_splits := $hsplits:term,
        transform_roots_nonpos := $hnp:term) =>
      `(tactic|
        exact
          RealRooted.isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
            $hne $hsplits $hnp)
  | `(tactic|
      rr_gamma_transform_backward using
        gamma_degree := $hdeg:term,
        transform_nonzero := $hne:term,
        transform_splits := $hsplits:term,
        transform_roots_nonpos := $hnp:term) =>
      `(tactic|
        exact
          RealRooted.isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
            $hdeg $hne $hsplits $hnp)
  | `(tactic|
      rr_gamma_realrooted_iff using
        gamma_degree := $hγdeg:term,
        polynomial_degree := $hpdeg:term,
        symmetric := $hsym:term,
        expansion := $hexp:term) =>
      `(tactic|
        exact RealRooted.gammaRealRootedIffPolynomialRealRootedNonpos
          $hγdeg $hpdeg $hsym $hexp)

end Tactic
end RealRooted
