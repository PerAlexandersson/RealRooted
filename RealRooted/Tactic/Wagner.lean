module

public import RealRooted.Tactic.Lookup
public import RealRooted.Wagner.NonpositiveRoots

/-!
# Wagner tactic frontends

Thin wrappers around the reusable nonpositive-root Wagner lemma forms.

Production-facing adapters also expose hypothesis-light common-right addition,
common-factor transport, and linear-factor cancellation without
sequence-specific names.
-/

@[expose] public section

open Polynomial

namespace RealRooted
namespace Tactic

theorem wagner_commonRight_add_sequence {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hFH : ∀ n : Nat, StrictInterl (F n) (H n))
    (hGH : ∀ n : Nat, StrictInterl (G n) (H n)) :
    ∀ n : Nat, StrictInterl (F n + G n) (H n) := fun n =>
  Wagner.commonRight_add (hF n) (hG n) (hFH n) (hGH n)

theorem wagner_commonLeft_add_sequence {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hHF : ∀ n : Nat, StrictInterl (H n) (F n))
    (hHG : ∀ n : Nat, StrictInterl (H n) (G n)) :
    ∀ n : Nat, StrictInterl (H n) (F n + G n) := fun n =>
  Wagner.commonLeft_add (hF n) (hG n) (hHF n) (hHG n)

theorem wagner_mulX_iff_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n)) :
    ∀ n : Nat, StrictInterl (F n) (G n) ↔ StrictInterl (G n) (X * F n) := fun n =>
  Wagner.mulX_iff (hF n) (hG n)

/-- Closes `StrictInterl (f + g) h` from `left : Wagner.HasNonposRootsPosLeading f`,
`right` for `g`, `left_interlaces_common : StrictInterl f h` and
`right_interlaces_common : StrictInterl g h`. -/
syntax (name := rr_wagner_common_right_add_named)
  "rr_wagner_common_right_add" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "left_interlaces_common" ":=" term ","
    "right_interlaces_common" ":=" term :
  tactic

/-- Closes `StrictInterl h (f + g)` from `left : Wagner.HasNonposRootsPosLeading f`,
`right` for `g`, `common_interlaces_left : StrictInterl h f` and
`common_interlaces_right : StrictInterl h g`. -/
syntax (name := rr_wagner_common_left_add_named)
  "rr_wagner_common_left_add" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "common_interlaces_left" ":=" term ","
    "common_interlaces_right" ":=" term :
  tactic

/-- Closes `StrictInterl f g ↔ StrictInterl g (X * f)` from
`shorter : Wagner.HasNonposRootsPosLeading f` and `longer` for `g`. -/
syntax (name := rr_wagner_mulX_iff_named)
  "rr_wagner_mulX_iff" " using "
    "shorter" ":=" term ","
    "longer" ":=" term :
  tactic

/-- Sequence form of `rr_wagner_common_right_add`: the same certificate for every index `n`. -/
syntax (name := rr_wagner_common_right_add_sequence_named)
  "rr_wagner_common_right_add_sequence" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "left_interlaces_common" ":=" term ","
    "right_interlaces_common" ":=" term :
  tactic

/-- Sequence form of `rr_wagner_common_left_add`: the same certificate for every index `n`. -/
syntax (name := rr_wagner_common_left_add_sequence_named)
  "rr_wagner_common_left_add_sequence" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "common_interlaces_left" ":=" term ","
    "common_interlaces_right" ":=" term :
  tactic

/-- Sequence form of `rr_wagner_mulX_iff`: the same certificate for every index `n`. -/
syntax (name := rr_wagner_mulX_iff_sequence_named)
  "rr_wagner_mulX_iff_sequence" " using "
    "shorter" ":=" term ","
    "longer" ":=" term :
  tactic

/-- Closes `StrictInterl (f + g) h` from `left_interlaces_common : StrictInterl f h`,
`right_interlaces_common : StrictInterl g h` and the positive leading coefficients
`left_pos_lc` and `right_pos_lc` of `f` and `g`. -/
syntax (name := rr_wagner_common_right_add_pos_lc_named)
  "rr_wagner_common_right_add_pos_lc" " using "
    "left_interlaces_common" ":=" term ","
    "right_interlaces_common" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

/-- Hypothesis-free form of
`rr_wagner_common_right_add_pos_lc`: the interlacings are found by `rr_lookup
[rr_base_strict_interl]` and the leading coefficients by `rr_lookup [rr_pos_lc]`. -/
syntax (name := rr_wagner_common_right_add_pos_lc_inferred)
  "rr_wagner_common_right_add_pos_lc" : tactic

/-- Closes `StrictInterl f g` from `root : r` and
`multiplied_interlacing : StrictInterl ((X - C r) * f) ((X - C r) * g)`. -/
syntax (name := rr_strict_interl_cancel_common_linear_factor_named)
  "rr_strict_interl_cancel_common_linear_factor" " using "
    "root" ":=" term ","
    "multiplied_interlacing" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_cancel_common_linear_factor` that finds
`multiplied_interlacing` by `rr_lookup [rr_base_strict_interl]`. -/
syntax (name := rr_strict_interl_cancel_common_linear_factor_inferred)
  "rr_strict_interl_cancel_common_linear_factor" " using "
    "root" ":=" term :
  tactic

/-- Closes `StrictInterl (d * f) (d * g)` from `factor_nonzero : d ≠ 0`,
`factor_splits : d.Splits` and `base_interlacing : StrictInterl f g`. -/
syntax (name := rr_strict_interl_mul_common_factor_named)
  "rr_strict_interl_mul_common_factor" " using "
    "factor_nonzero" ":=" term ","
    "factor_splits" ":=" term ","
    "base_interlacing" ":=" term :
  tactic

/-- Hypothesis-free form of `rr_strict_interl_mul_common_factor`: `factor_nonzero` is found by
`rr_lookup [rr_nonzero]`, `factor_splits` by `assumption`, and `base_interlacing` by `rr_lookup
[rr_base_strict_interl]`. -/
syntax (name := rr_strict_interl_mul_common_factor_inferred)
  "rr_strict_interl_mul_common_factor" : tactic

macro_rules
  | `(tactic|
      rr_wagner_common_right_add using
        left := $hf:term,
        right := $hg:term,
        left_interlaces_common := $hfh:term,
        right_interlaces_common := $hgh:term) =>
      `(tactic|
        exact RealRooted.Wagner.commonRight_add
          $hf $hg $hfh $hgh)
  | `(tactic|
      rr_wagner_common_left_add using
        left := $hf:term,
        right := $hg:term,
        common_interlaces_left := $hhf:term,
        common_interlaces_right := $hhg:term) =>
      `(tactic|
        exact RealRooted.Wagner.commonLeft_add
          $hf $hg $hhf $hhg)
  | `(tactic|
      rr_wagner_mulX_iff using
        shorter := $hf:term,
        longer := $hg:term) =>
      `(tactic|
        exact RealRooted.Wagner.mulX_iff $hf $hg)
  | `(tactic|
      rr_wagner_common_right_add_sequence using
        left := $hf:term,
        right := $hg:term,
        left_interlaces_common := $hfh:term,
        right_interlaces_common := $hgh:term) =>
      `(tactic|
        exact RealRooted.Tactic.wagner_commonRight_add_sequence
          $hf $hg $hfh $hgh)
  | `(tactic|
      rr_wagner_common_left_add_sequence using
        left := $hf:term,
        right := $hg:term,
        common_interlaces_left := $hhf:term,
        common_interlaces_right := $hhg:term) =>
      `(tactic|
        exact RealRooted.Tactic.wagner_commonLeft_add_sequence
          $hf $hg $hhf $hhg)
  | `(tactic|
      rr_wagner_mulX_iff_sequence using
        shorter := $hf:term,
        longer := $hg:term) =>
      `(tactic|
        exact RealRooted.Tactic.wagner_mulX_iff_sequence $hf $hg)
  | `(tactic|
      rr_wagner_common_right_add_pos_lc using
        left_interlaces_common := $hfh:term,
        right_interlaces_common := $hgh:term,
        left_pos_lc := $hf_pos:term,
        right_pos_lc := $hg_pos:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.add_of_right_of_posLeadingCoeff
          $hfh $hgh $hf_pos $hg_pos)
  | `(tactic| rr_wagner_common_right_add_pos_lc) =>
      `(tactic|
        exact (by
          apply RealRooted.StrictInterl.add_of_right_of_posLeadingCoeff
          case hfh => rr_lookup [rr_base_strict_interl]
          case hgh => rr_lookup [rr_base_strict_interl]
          case hf_pos => rr_lookup [rr_pos_lc]
          case hg_pos => rr_lookup [rr_pos_lc]))
  | `(tactic|
      rr_strict_interl_cancel_common_linear_factor using
        root := $r:term,
        multiplied_interlacing := $h:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.of_mul_X_sub_C_both (r := $r) $h)
  | `(tactic|
      rr_strict_interl_cancel_common_linear_factor using
        root := $r:term) =>
      `(tactic|
        exact (by
          apply RealRooted.StrictInterl.of_mul_X_sub_C_both (r := $r)
          rr_lookup [rr_base_strict_interl]))
  | `(tactic|
      rr_strict_interl_mul_common_factor using
        factor_nonzero := $hd_ne:term,
        factor_splits := $hd_splits:term,
        base_interlacing := $h:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.mul_common_factor $h $hd_ne $hd_splits)
  | `(tactic| rr_strict_interl_mul_common_factor) =>
      `(tactic|
        exact (by
          apply RealRooted.StrictInterl.mul_common_factor
          case hd_ne => rr_lookup [rr_nonzero]
          case hd_splits => assumption
          case h => rr_lookup [rr_base_strict_interl]))

end Tactic
end RealRooted
