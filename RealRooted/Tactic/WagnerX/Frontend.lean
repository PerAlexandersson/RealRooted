module

public import RealRooted.Tactic.WagnerX.Syntax
public import RealRooted.Tactic.Lookup
public import RealRooted.WagnerX.NonnegativeRoots

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
end Tactic
end RealRooted

