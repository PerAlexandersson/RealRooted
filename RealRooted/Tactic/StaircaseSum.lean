import RealRooted.StaircaseSum

/-!
# Staircase-sum tactic frontends

Thin wrappers for staircase-weighted sums of interlacing nonnegative
sequences.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem staircaseSum_sequence_zero {FS : Nat → List ℝ[X]} :
    ∀ i : Nat, staircaseSum (FS i) 0 = (FS i).sum := fun i =>
  RealRooted.staircaseSum_zero (FS i)

theorem staircaseSum_sequence_length {FS : Nat → List ℝ[X]} :
    ∀ i : Nat, staircaseSum (FS i) (FS i).length = X * (FS i).sum := fun i =>
  RealRooted.staircaseSum_length (FS i)

theorem staircaseSum_sequence_strictInterl
    {FS : Nat → List ℝ[X]} {M : Nat → Nat}
    (hFS : ∀ i : Nat, IsInterlacingSeqNonneg (FS i))
    (hM : ∀ i : Nat, M i < (FS i).length) :
    ∀ i : Nat, StrictInterl ((FS i).get ⟨M i, hM i⟩) (staircaseSum (FS i) (M i)) :=
  fun i =>
    RealRooted.strictInterl_get_staircaseSum_of_isInterlacingSeqNonneg
      (hFS i) (hM i)

theorem staircaseSum_sequence_realrooted
    {FS : Nat → List ℝ[X]} {M : Nat → Nat}
    (hFS : ∀ i : Nat, IsInterlacingSeqNonneg (FS i))
    (hM : ∀ i : Nat, M i < (FS i).length) :
    ∀ i : Nat, staircaseSum (FS i) (M i) ≠ 0 ∧
      (staircaseSum (FS i) (M i)).Splits := fun i =>
  RealRooted.isRealRooted_staircaseSum_of_isInterlacingSeqNonneg
    (hFS i) (hM i)

syntax (name := rr_staircaseSum_zero_named)
  "rr_staircaseSum_zero" :
  tactic

syntax (name := rr_staircaseSum_sequence_zero_named)
  "rr_staircaseSum_sequence_zero" :
  tactic

syntax (name := rr_staircaseSum_length_named)
  "rr_staircaseSum_length" :
  tactic

syntax (name := rr_staircaseSum_sequence_length_named)
  "rr_staircaseSum_sequence_length" :
  tactic

syntax (name := rr_staircaseSum_strict_interl_named)
  "rr_staircaseSum_strict_interl" " using "
    "interlacing_nonneg" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_staircaseSum_sequence_strict_interl_named)
  "rr_staircaseSum_sequence_strict_interl" " using "
    "interlacing_nonneg" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_staircaseSum_realrooted_named)
  "rr_staircaseSum_realrooted" " using "
    "interlacing_nonneg" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_staircaseSum_sequence_realrooted_named)
  "rr_staircaseSum_sequence_realrooted" " using "
    "interlacing_nonneg" ":=" term ","
    "index_lt" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_staircaseSum_zero) =>
      `(tactic| exact RealRooted.staircaseSum_zero _)
  | `(tactic| rr_staircaseSum_sequence_zero) =>
      `(tactic| exact RealRooted.Tactic.staircaseSum_sequence_zero)
  | `(tactic| rr_staircaseSum_length) =>
      `(tactic| exact RealRooted.staircaseSum_length _)
  | `(tactic| rr_staircaseSum_sequence_length) =>
      `(tactic| exact RealRooted.Tactic.staircaseSum_sequence_length)
  | `(tactic|
      rr_staircaseSum_strict_interl using
        interlacing_nonneg := $hfs:term,
        index_lt := $hm:term) =>
      `(tactic|
        exact RealRooted.strictInterl_get_staircaseSum_of_isInterlacingSeqNonneg
          $hfs $hm)
  | `(tactic|
      rr_staircaseSum_sequence_strict_interl using
        interlacing_nonneg := $hfs:term,
        index_lt := $hm:term) =>
      `(tactic|
        exact RealRooted.Tactic.staircaseSum_sequence_strictInterl $hfs $hm)
  | `(tactic|
      rr_staircaseSum_realrooted using
        interlacing_nonneg := $hfs:term,
        index_lt := $hm:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_staircaseSum_of_isInterlacingSeqNonneg
          $hfs $hm)
  | `(tactic|
      rr_staircaseSum_sequence_realrooted using
        interlacing_nonneg := $hfs:term,
        index_lt := $hm:term) =>
      `(tactic|
        exact RealRooted.Tactic.staircaseSum_sequence_realrooted $hfs $hm)

end Tactic
end RealRooted
namespace RealRooted
namespace Tactic
@[deprecated staircaseSum_sequence_strictInterl (since := "2026-09-26")]
alias staircaseSum_sequence_prec := staircaseSum_sequence_strictInterl

end Tactic
end RealRooted

/- Parser compatibility for the pre-#984 Prec/Prec0 tactic surface.
    Canonical syntax is preferred; these declarations retain old scripts
    and dispatch through the deprecated theorem aliases above. -/
namespace RealRooted
namespace Tactic
syntax (name := rr_staircaseSum_prec_named_legacy)
  "rr_staircaseSum_prec" " using "
    "interlacing_nonneg" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_staircaseSum_sequence_prec_named_legacy)
  "rr_staircaseSum_sequence_prec" " using "
    "interlacing_nonneg" ":=" term ","
    "index_lt" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_staircaseSum_prec using
        interlacing_nonneg := $hfs:term,
        index_lt := $hm:term) =>
      `(tactic|
        exact RealRooted.prec_get_staircaseSum_of_isInterlacingSeqNonneg
          $hfs $hm)
  | `(tactic|
      rr_staircaseSum_sequence_prec using
        interlacing_nonneg := $hfs:term,
        index_lt := $hm:term) =>
      `(tactic|
        exact RealRooted.Tactic.staircaseSum_sequence_prec $hfs $hm)
end Tactic
end RealRooted
