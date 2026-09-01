import RealRooted.Tactic.Lookup
import RealRooted.Wagner.NonpositiveRoots

/-!
# Wagner tactic frontends

Thin wrappers around the reusable nonpositive-root Wagner lemma forms.

Production-facing adapters also expose hypothesis-light common-right addition,
common-factor transport, and linear-factor cancellation without
sequence-specific names.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem wagner_commonRight_add_sequence {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (H n))
    (hFH : ∀ n : Nat, Prec (F n) (H n))
    (hGH : ∀ n : Nat, Prec (G n) (H n)) :
    ∀ n : Nat, Prec (F n + G n) (H n) := fun n => by
  have _ := hH n
  exact Wagner.commonRight_add (hF n) (hG n) (hFH n) (hGH n)

theorem wagner_commonLeft_add_sequence {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (H n))
    (hHF : ∀ n : Nat, Prec (H n) (F n))
    (hHG : ∀ n : Nat, Prec (H n) (G n)) :
    ∀ n : Nat, Prec (H n) (F n + G n) := fun n => by
  have _ := hH n
  exact Wagner.commonLeft_add (hF n) (hG n) (hHF n) (hHG n)

theorem wagner_mulX_iff_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Wagner.HasNonposRootsPosLeading (G n))
    (hdeg : ∀ n : Nat, (F n).natDegree + 1 = (G n).natDegree) :
    ∀ n : Nat, Prec (F n) (G n) ↔ Prec (G n) (X * F n) := fun n =>
  Wagner.mulX_iff (hF n) (hG n) (hdeg n)

syntax (name := rr_wagner_common_right_add_named)
  "rr_wagner_common_right_add" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "common" ":=" term ","
    "left_interlaces_common" ":=" term ","
    "right_interlaces_common" ":=" term :
  tactic

syntax (name := rr_wagner_common_left_add_named)
  "rr_wagner_common_left_add" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "common" ":=" term ","
    "common_interlaces_left" ":=" term ","
    "common_interlaces_right" ":=" term :
  tactic

syntax (name := rr_wagner_mulX_iff_named)
  "rr_wagner_mulX_iff" " using "
    "shorter" ":=" term ","
    "longer" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_wagner_common_right_add_sequence_named)
  "rr_wagner_common_right_add_sequence" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "common" ":=" term ","
    "left_interlaces_common" ":=" term ","
    "right_interlaces_common" ":=" term :
  tactic

syntax (name := rr_wagner_common_left_add_sequence_named)
  "rr_wagner_common_left_add_sequence" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "common" ":=" term ","
    "common_interlaces_left" ":=" term ","
    "common_interlaces_right" ":=" term :
  tactic

syntax (name := rr_wagner_mulX_iff_sequence_named)
  "rr_wagner_mulX_iff_sequence" " using "
    "shorter" ":=" term ","
    "longer" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_wagner_common_right_add_pos_lc_named)
  "rr_wagner_common_right_add_pos_lc" " using "
    "left_interlaces_common" ":=" term ","
    "right_interlaces_common" ":=" term ","
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term :
  tactic

syntax (name := rr_wagner_common_right_add_pos_lc_inferred)
  "rr_wagner_common_right_add_pos_lc" : tactic

syntax (name := rr_prec_cancel_common_linear_factor_named)
  "rr_prec_cancel_common_linear_factor" " using "
    "root" ":=" term ","
    "multiplied_interlacing" ":=" term :
  tactic

syntax (name := rr_prec_cancel_common_linear_factor_inferred)
  "rr_prec_cancel_common_linear_factor" " using "
    "root" ":=" term :
  tactic

syntax (name := rr_prec_mul_common_factor_named)
  "rr_prec_mul_common_factor" " using "
    "factor_nonzero" ":=" term ","
    "factor_splits" ":=" term ","
    "base_interlacing" ":=" term :
  tactic

syntax (name := rr_prec_mul_common_factor_inferred)
  "rr_prec_mul_common_factor" : tactic

macro_rules
  | `(tactic|
      rr_wagner_common_right_add using
        left := $hf:term,
        right := $hg:term,
        common := $_hh:term,
        left_interlaces_common := $hfh:term,
        right_interlaces_common := $hgh:term) =>
      `(tactic|
        exact RealRooted.Wagner.commonRight_add
          $hf $hg $hfh $hgh)
  | `(tactic|
      rr_wagner_common_left_add using
        left := $hf:term,
        right := $hg:term,
        common := $_hh:term,
        common_interlaces_left := $hhf:term,
        common_interlaces_right := $hhg:term) =>
      `(tactic|
        exact RealRooted.Wagner.commonLeft_add
          $hf $hg $hhf $hhg)
  | `(tactic|
      rr_wagner_mulX_iff using
        shorter := $hf:term,
        longer := $hg:term,
        degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Wagner.mulX_iff $hf $hg $hdeg)
  | `(tactic|
      rr_wagner_common_right_add_sequence using
        left := $hf:term,
        right := $hg:term,
        common := $hh:term,
        left_interlaces_common := $hfh:term,
        right_interlaces_common := $hgh:term) =>
      `(tactic|
        exact RealRooted.Tactic.wagner_commonRight_add_sequence
          $hf $hg $hh $hfh $hgh)
  | `(tactic|
      rr_wagner_common_left_add_sequence using
        left := $hf:term,
        right := $hg:term,
        common := $hh:term,
        common_interlaces_left := $hhf:term,
        common_interlaces_right := $hhg:term) =>
      `(tactic|
        exact RealRooted.Tactic.wagner_commonLeft_add_sequence
          $hf $hg $hh $hhf $hhg)
  | `(tactic|
      rr_wagner_mulX_iff_sequence using
        shorter := $hf:term,
        longer := $hg:term,
        degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Tactic.wagner_mulX_iff_sequence $hf $hg $hdeg)
  | `(tactic|
      rr_wagner_common_right_add_pos_lc using
        left_interlaces_common := $hfh:term,
        right_interlaces_common := $hgh:term,
        left_pos_lc := $hf_pos:term,
        right_pos_lc := $hg_pos:term) =>
      `(tactic|
        exact RealRooted.prec_add_of_prec_right_of_posLeadingCoeff
          $hfh $hgh $hf_pos $hg_pos)
  | `(tactic| rr_wagner_common_right_add_pos_lc) =>
      `(tactic|
        exact (by
          apply RealRooted.prec_add_of_prec_right_of_posLeadingCoeff
          case hfh => rr_lookup [rr_base_prec]
          case hgh => rr_lookup [rr_base_prec]
          case hf_pos => rr_lookup [rr_pos_lc]
          case hg_pos => rr_lookup [rr_pos_lc]))
  | `(tactic|
      rr_prec_cancel_common_linear_factor using
        root := $r:term,
        multiplied_interlacing := $h:term) =>
      `(tactic| exact RealRooted.prec_of_prec_mul_X_sub_C_both $r $h)
  | `(tactic|
      rr_prec_cancel_common_linear_factor using
        root := $r:term) =>
      `(tactic|
        exact (by
          apply RealRooted.prec_of_prec_mul_X_sub_C_both $r
          rr_lookup [rr_base_prec]))
  | `(tactic|
      rr_prec_mul_common_factor using
        factor_nonzero := $hd_ne:term,
        factor_splits := $hd_splits:term,
        base_interlacing := $h:term) =>
      `(tactic|
        exact RealRooted.prec_mul_common_factor $hd_ne $hd_splits $h)
  | `(tactic| rr_prec_mul_common_factor) =>
      `(tactic|
        exact (by
          apply RealRooted.prec_mul_common_factor
          case hd_ne => rr_lookup [rr_nonzero]
          case hd_splits => assumption
          case h => rr_lookup [rr_base_prec]))

end Tactic
end RealRooted
