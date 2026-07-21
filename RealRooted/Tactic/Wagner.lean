import RealRooted.Challenges.Wagner

/-!
# Wagner challenge tactic frontends

Thin wrappers around the challenge-facing Wagner lemma forms.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem wagner_commonRight_add_sequence {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (H n))
    (hFH : ∀ n : Nat, Prec (F n) (H n))
    (hGH : ∀ n : Nat, Prec (G n) (H n)) :
    ∀ n : Nat, Prec (F n + G n) (H n) := fun n => by
  have _ := hH n
  exact Challenges.Wagner.commonRight_add (hF n) (hG n) (hFH n) (hGH n)

theorem wagner_commonLeft_add_sequence {F G H : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (G n))
    (hH : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (H n))
    (hHF : ∀ n : Nat, Prec (H n) (F n))
    (hHG : ∀ n : Nat, Prec (H n) (G n)) :
    ∀ n : Nat, Prec (H n) (F n + G n) := fun n => by
  have _ := hH n
  exact Challenges.Wagner.commonLeft_add (hF n) (hG n) (hHF n) (hHG n)

theorem wagner_mulX_iff_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (F n))
    (hG : ∀ n : Nat, Challenges.Wagner.HasNonposRootsPosLeading (G n))
    (hdeg : ∀ n : Nat, (F n).natDegree + 1 = (G n).natDegree) :
    ∀ n : Nat, Prec (F n) (G n) ↔ Prec (G n) (X * F n) := fun n =>
  Challenges.Wagner.mulX_iff (hF n) (hG n) (hdeg n)

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

macro_rules
  | `(tactic|
      rr_wagner_common_right_add using
        left := $hf:term,
        right := $hg:term,
        common := $_hh:term,
        left_interlaces_common := $hfh:term,
        right_interlaces_common := $hgh:term) =>
      `(tactic|
        exact RealRooted.Challenges.Wagner.commonRight_add
          $hf $hg $hfh $hgh)
  | `(tactic|
      rr_wagner_common_left_add using
        left := $hf:term,
        right := $hg:term,
        common := $_hh:term,
        common_interlaces_left := $hhf:term,
        common_interlaces_right := $hhg:term) =>
      `(tactic|
        exact RealRooted.Challenges.Wagner.commonLeft_add
          $hf $hg $hhf $hhg)
  | `(tactic|
      rr_wagner_mulX_iff using
        shorter := $hf:term,
        longer := $hg:term,
        degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Challenges.Wagner.mulX_iff $hf $hg $hdeg)
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

end Tactic
end RealRooted
