import RealRooted.AissenSchoenbergWhitney
import RealRooted.PFPolynomial

/-!
# Aissen--Schoenberg--Whitney tactic frontends

Thin certificate-driven wrappers around the proved forward ASW theorem and
its standard projections.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_asw_forward_named)
  "rr_asw_forward" " using "
    "pf_coeff" ":=" term :
  tactic

syntax (name := rr_asw_splits_named)
  "rr_asw_splits" " using "
    "pf_coeff" ":=" term :
  tactic

syntax (name := rr_asw_forward_or_zero_named)
  "rr_asw_forward_or_zero" " using "
    "pf_coeff" ":=" term :
  tactic

syntax (name := rr_asw_forward_nonzero_named)
  "rr_asw_forward_nonzero" " using "
    "nonzero" ":=" term ","
    "pf_coeff" ":=" term :
  tactic

syntax (name := rr_asw_pf_polynomial_named)
  "rr_asw_pf_polynomial" " using "
    "pf_coeff" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_asw_forward using
        pf_coeff := $hpf:term) =>
      `(tactic|
        exact RealRooted.aissenSchoenbergWhitneyForward $hpf)
  | `(tactic|
      rr_asw_splits using
        pf_coeff := $hpf:term) =>
      `(tactic|
        exact RealRooted.aissenSchoenbergWhitneyForwardSplits $hpf)
  | `(tactic|
      rr_asw_forward_or_zero using
        pf_coeff := $hpf:term) =>
      `(tactic|
        exact RealRooted.aissenSchoenbergWhitneyForwardOrZero
          (RealRooted.hasNonnegCoeffs_of_IsPolyaFreqSeq_coeff $hpf) $hpf)
  | `(tactic|
      rr_asw_forward_nonzero using
        nonzero := $hp0:term,
        pf_coeff := $hpf:term) =>
      `(tactic|
        exact RealRooted.aissenSchoenbergWhitneyForwardNoNonneg $hp0 $hpf)
  | `(tactic|
      rr_asw_pf_polynomial using
        pf_coeff := $hpf:term) =>
      `(tactic|
        exact RealRooted.IsPFPolynomial.of_sequence
          RealRooted.aissenSchoenbergWhitneyForwardOrZero $hpf)

end Tactic
end RealRooted
