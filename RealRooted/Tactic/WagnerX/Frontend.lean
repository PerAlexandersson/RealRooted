module

public import RealRooted.Tactic.WagnerX.Syntax

/-!
# Wagner `X`-shift tactic frontend
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

macro_rules
  -- Each conclusion fixes its hidden polynomial and scalar parameters first.
  | `(tactic|
      rr_strict_interl_mul_X using
        proper := $hstrictInterl:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term) =>
      `(tactic|
        exact RealRooted.strictInterl_mul_X_of_strictInterl_of_nonneg $hstrictInterl $hfnn $hgnn)
  | `(tactic| rr_strict_interl_mul_X) =>
      `(tactic|
        exact (by
          apply RealRooted.strictInterl_mul_X_of_strictInterl_of_nonneg
          case h => rr_lookup [rr_base_strict_interl]
          case hfnn => rr_lookup [rr_nonneg]
          case hgnn => rr_lookup [rr_nonneg]))
  | `(tactic|
      rr_strict_interl_mul_X_both using proper := $hstrictInterl:term) =>
      `(tactic|
        simpa using RealRooted.StrictInterl.mul_X_sub_C_both $hstrictInterl 0)
  | `(tactic|
      rr_strict_interl_mul_X_both using
        proper := $hstrictInterl:term,
        left_nonneg := $_hfnn:term,
        right_nonneg := $_hgnn:term) =>
      `(tactic|
        simpa using RealRooted.StrictInterl.mul_X_sub_C_both $hstrictInterl 0)
  | `(tactic| rr_strict_interl_mul_X_both) =>
      `(tactic|
        exact (by
          simpa using RealRooted.StrictInterl.mul_X_sub_C_both
            (by rr_lookup [rr_base_strict_interl]) 0))
  | `(tactic|
      rr_strict_interl_C_mul_X using
        proper := $hstrictInterl:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        coeff_ne := $hc:term) =>
      `(tactic|
        exact strictInterl_C_mul_X_of_strictInterl_of_nonneg
          $hstrictInterl $hfnn $hgnn $hc)
  | `(tactic|
      rr_strict_interl_C_mul_X using
        proper := $hstrictInterl:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        coeff_pos := $hc:term) =>
      `(tactic|
        exact RealRooted.strictInterl_C_mul_X_of_strictInterl_of_nonneg
          $hstrictInterl $hfnn $hgnn ($hc).ne')
  | `(tactic|
      rr_strict_interl_C_mul_X using
        coeff_ne := $hc:term) =>
      `(tactic|
        exact (by
          apply RealRooted.strictInterl_C_mul_X_of_strictInterl_of_nonneg
          case h => rr_lookup [rr_base_strict_interl]
          case hfnn => rr_lookup [rr_nonneg]
          case hgnn => rr_lookup [rr_nonneg]
          case hc => exact $hc))
  | `(tactic|
      rr_strict_interl_C_mul_X using
        coeff_pos := $hc:term) =>
      `(tactic|
        exact (by
          apply RealRooted.strictInterl_C_mul_X_of_strictInterl_of_nonneg
          case h => rr_lookup [rr_base_strict_interl]
          case hfnn => rr_lookup [rr_nonneg]
          case hgnn => rr_lookup [rr_nonneg]
          case hc => exact ($hc).ne'))
  | `(tactic|
      rr_strict_interl_X_derivative_X_self using
        splits := $hf:term,
        degree_two := $hdeg:term) =>
      `(tactic|
        exact RealRooted.strictInterl_X_derivative_X_self_of_splits $hf $hdeg)
  | `(tactic|
      rr_strict_interl_X_derivative_X_self using
        splits := $hf:term,
        degree_two := $hdeg:term,
        nonneg_coeffs := $_hfnn:term) =>
      `(tactic|
        exact RealRooted.strictInterl_X_derivative_X_self_of_splits $hf $hdeg)
  | `(tactic| rr_strict_interl_X_derivative_X_self) =>
      `(tactic|
        exact (by
          apply RealRooted.strictInterl_X_derivative_X_self_of_splits
          case hf => rr_lookup
          case hdeg => rr_lookup [rr_degree]))
  | `(tactic|
      rr_strict_interl_wagner_derivative_gap_lag using
        proper := $hstrictInterl:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term) =>
      `(tactic|
        exact RealRooted.strictInterl_wagner_derivative_gap_lag_step
          $hstrictInterl $hfnn $hgnn $hdeg $ha $hc)
  | `(tactic| rr_strict_interl_wagner_derivative_gap_lag) =>
      `(tactic|
        exact (by
          apply RealRooted.strictInterl_wagner_derivative_gap_lag_step
          case h => rr_lookup [rr_base_strict_interl]
          case hfnn => rr_lookup [rr_nonneg]
          case hgnn => rr_lookup [rr_nonneg]
          case hdeg => rr_lookup [rr_degree]
          case ha => first | rr_lookup | rr_wagner_pos
          case hc => first | rr_lookup | rr_wagner_pos))
end Tactic
end RealRooted
