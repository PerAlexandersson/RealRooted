module

public import RealRooted.AissenSchoenbergWhitney
public import RealRooted.PFPolynomial

/-!
# Aissen--Schoenberg--Whitney tactic frontends

Thin certificate-driven wrappers around the proved forward ASW theorem and
its standard projections.
-/

@[expose] public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Closes `p.Splits ∧ ∀ r ∈ p.roots, r ≤ 0` from `pf_coeff : IsPolyaFreqSeq p.coeff`, by the
forward Aissen--Schoenberg--Whitney theorem. -/
syntax (name := rr_asw_forward_named)
  "rr_asw_forward" " using "
    "pf_coeff" ":=" term :
  tactic

/-- Closes `p.Splits` from `pf_coeff : IsPolyaFreqSeq p.coeff`, by the forward
Aissen--Schoenberg--Whitney theorem. -/
syntax (name := rr_asw_splits_named)
  "rr_asw_splits" " using "
    "pf_coeff" ":=" term :
  tactic

/-- Closes `(p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0` from `pf_coeff : IsPolyaFreqSeq p.coeff`. -/
syntax (name := rr_asw_forward_or_zero_named)
  "rr_asw_forward_or_zero" " using "
    "pf_coeff" ":=" term :
  tactic

/-- Closes `(p ≠ 0 ∧ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0` from `nonzero : p ≠ 0` and
`pf_coeff : IsPolyaFreqSeq p.coeff`. -/
syntax (name := rr_asw_forward_nonzero_named)
  "rr_asw_forward_nonzero" " using "
    "nonzero" ":=" term ","
    "pf_coeff" ":=" term :
  tactic

/-- Closes `IsPFPolynomial p` from `pf_coeff : IsPolyaFreqSeq p.coeff`. -/
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
        exact RealRooted.aissenSchoenbergWhitneyForwardOrZero $hpf)
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
        exact RealRooted.IsPFPolynomial.of_polyaFreqSeq $hpf)

end Tactic
end RealRooted
