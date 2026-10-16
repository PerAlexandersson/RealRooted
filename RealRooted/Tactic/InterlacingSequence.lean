module

public import RealRooted.InterlacingSequenceBasic

/-!
# Interlacing-sequence tactic frontends

Thin wrappers for list-level interlacing sequence plumbing.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Closes `IsInterlacingSeq fs ↔ fs.Pairwise StrictInterl`. -/
syntax (name := rr_interlacingSeq_iff_pairwise_named)
  "rr_interlacingSeq_iff_pairwise" :
  tactic

/-- Closes `IsInterlacingSeq0 fs ↔ fs.Pairwise Interl`. -/
syntax (name := rr_interlacingSeq0_iff_pairwise_named)
  "rr_interlacingSeq0_iff_pairwise" :
  tactic

/-- Closes `IsInterlacingSeq0 fs` from `interlacing : IsInterlacingSeq fs`. -/
syntax (name := rr_interlacingSeq_to_interlacingSeq0_named)
  "rr_interlacingSeq_to_interlacingSeq0" " using "
    "interlacing" ":=" term :
  tactic

/-- Closes `StrictInterl (fs.get i) (fs.get j)` from `interlacing : IsInterlacingSeq fs` and
`index_lt : i < j`. -/
syntax (name := rr_interlacingSeq_strict_interl_named)
  "rr_interlacingSeq_strict_interl" " using "
    "interlacing" ":=" term ","
    "index_lt" ":=" term :
  tactic

/-- Closes `Interl (fs.get i) (fs.get j)` from `interlacing0 : IsInterlacingSeq0 fs` and
`index_lt : i < j`. -/
syntax (name := rr_interlacingSeq0_interl_named)
  "rr_interlacingSeq0_interl" " using "
    "interlacing0" ":=" term ","
    "index_lt" ":=" term :
  tactic

/-- Closes `IsInterlacingSeq gs` from `interlacing : IsInterlacingSeq fs` and
`sublist : gs.Sublist fs`. -/
syntax (name := rr_interlacingSeq_sublist_named)
  "rr_interlacingSeq_sublist" " using "
    "interlacing" ":=" term ","
    "sublist" ":=" term :
  tactic

/-- Closes `IsInterlacingSeqNonneg gs` from `interlacing_nonneg : IsInterlacingSeqNonneg fs` and
`sublist : gs.Sublist fs`. -/
syntax (name := rr_interlacingSeqNonneg_sublist_named)
  "rr_interlacingSeqNonneg_sublist" " using "
    "interlacing_nonneg" ":=" term ","
    "sublist" ":=" term :
  tactic

/-- Closes `IsInterlacingSeq0 gs` from `interlacing0 : IsInterlacingSeq0 fs` and
`sublist : gs.Sublist fs`. -/
syntax (name := rr_interlacingSeq0_sublist_named)
  "rr_interlacingSeq0_sublist" " using "
    "interlacing0" ":=" term ","
    "sublist" ":=" term :
  tactic

/-- Closes `IsInterlacingSeqNonneg gs` from `interlacing0_nonneg : IsInterlacingSeq0Nonneg fs`,
`sublist : gs.Sublist fs`, `realrooted` (the nonzero members of `fs` are real-rooted) and
`nonzero` (the members of `gs` are nonzero). -/
syntax (name := rr_interlacingSeq0Nonneg_sublist_realrooted_named)
  "rr_interlacingSeq0Nonneg_sublist_realrooted" " using "
    "interlacing0_nonneg" ":=" term ","
    "sublist" ":=" term ","
    "realrooted" ":=" term ","
    "nonzero" ":=" term :
  tactic

/-- Closes `IsInterlacingSeq (fs ++ gs)` from `left_interlacing : IsInterlacingSeq fs`,
`right_interlacing : IsInterlacingSeq gs` and `cross_strictInterl` (every member of `fs`
strictly interlaces every member of `gs`). -/
syntax (name := rr_interlacingSeq_append_named)
  "rr_interlacingSeq_append" " using "
    "left_interlacing" ":=" term ","
    "right_interlacing" ":=" term ","
    "cross_strictInterl" ":=" term :
  tactic

/-- Closes `fs.reverse.Pairwise (fun f g => StrictInterl g f)` from
`interlacing : IsInterlacingSeq fs`. -/
syntax (name := rr_interlacingSeq_reverse_pairwise_named)
  "rr_interlacingSeq_reverse_pairwise" " using "
    "interlacing" ":=" term :
  tactic

/-- Closes `fs.reverse.Pairwise (fun f g => Interl g f)` from
`interlacing0 : IsInterlacingSeq0 fs`. -/
syntax (name := rr_interlacingSeq0_reverse_pairwise_named)
  "rr_interlacingSeq0_reverse_pairwise" " using "
    "interlacing0" ":=" term :
  tactic

/-- Closes the nonnegativity, real-rootedness and reversed pairwise interlacing of
`fs.reverse` from `interlacing_nonneg : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_interlacingSeqNonneg_reverse_pairwise_named)
  "rr_interlacingSeqNonneg_reverse_pairwise" " using "
    "interlacing_nonneg" ":=" term :
  tactic

/-- Closes `∀ f ∈ fs, f ≠ 0 ∧ f.Splits` from `interlacing_nonneg : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_interlacingSeqNonneg_realrooted_named)
  "rr_interlacingSeqNonneg_realrooted" " using "
    "interlacing_nonneg" ":=" term :
  tactic

/-- Closes `f.Splits` from `interlacing_nonneg : IsInterlacingSeqNonneg fs` and `member : f ∈
fs`. -/
syntax (name := rr_interlacingSeqNonneg_splits_named)
  "rr_interlacingSeqNonneg_splits" " using "
    "interlacing_nonneg" ":=" term ","
    "member" ":=" term :
  tactic

/-- Closes `∀ f ∈ fs, HasPosLeadingCoeff f` from
`interlacing_nonneg : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_interlacingSeqNonneg_pos_lc_named)
  "rr_interlacingSeqNonneg_pos_lc" " using "
    "interlacing_nonneg" ":=" term :
  tactic

/-- Closes `∀ f ∈ fs, HasNonnegCoeffs f` from `interlacing_nonneg : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_interlacingSeqNonneg_nonneg_coeffs_named)
  "rr_interlacingSeqNonneg_nonneg_coeffs" " using "
    "interlacing_nonneg" ":=" term :
  tactic

/-- Closes `IsInterlacingSeqNonneg (fs.filter (· ≠ 0))` from
`interlacing0_nonneg : IsInterlacingSeq0Nonneg fs` and `realrooted` (the nonzero members of `fs`
are real-rooted). -/
syntax (name := rr_interlacingSeq0Nonneg_filter_ne_zero_named)
  "rr_interlacingSeq0Nonneg_filter_ne_zero" " using "
    "interlacing0_nonneg" ":=" term ","
    "realrooted" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_interlacingSeq_iff_pairwise) =>
      `(tactic| exact RealRooted.isInterlacingSeq_iff_pairwise)
  | `(tactic| rr_interlacingSeq0_iff_pairwise) =>
      `(tactic| exact RealRooted.isInterlacingSeq0_iff_pairwise)
  | `(tactic|
      rr_interlacingSeq_to_interlacingSeq0 using
        interlacing := $hfs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq.toIsInterlacingSeq0 $hfs)
  | `(tactic|
      rr_interlacingSeq_strict_interl using
        interlacing := $hfs:term,
        index_lt := $hij:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq.strictInterl $hfs $hij)
  | `(tactic|
      rr_interlacingSeq0_interl using
        interlacing0 := $hfs:term,
        index_lt := $hij:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq0.interl $hfs $hij)
  | `(tactic|
      rr_interlacingSeq_sublist using
        interlacing := $hfs:term,
        sublist := $hgs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq.sublist $hfs $hgs)
  | `(tactic|
      rr_interlacingSeqNonneg_sublist using
        interlacing_nonneg := $hfs:term,
        sublist := $hgs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeqNonneg.sublist $hfs $hgs)
  | `(tactic|
      rr_interlacingSeq0_sublist using
        interlacing0 := $hfs:term,
        sublist := $hgs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq0.sublist $hfs $hgs)
  | `(tactic|
      rr_interlacingSeq0Nonneg_sublist_realrooted using
        interlacing0_nonneg := $hfs:term,
        sublist := $hgs:term,
        realrooted := $hreal:term,
        nonzero := $hne:term) =>
      `(tactic|
        exact RealRooted.IsInterlacingSeq0Nonneg.sublist_of_realRooted_of_ne
          $hfs $hgs $hreal $hne)
  | `(tactic|
      rr_interlacingSeq_append using
        left_interlacing := $hfs:term,
        right_interlacing := $hgs:term,
        cross_strictInterl := $hfg:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq.append $hfs $hgs $hfg)
  | `(tactic|
      rr_interlacingSeq_reverse_pairwise using
        interlacing := $hfs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq.reverse $hfs)
  | `(tactic|
      rr_interlacingSeq0_reverse_pairwise using
        interlacing0 := $hfs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq0.reverse $hfs)
  | `(tactic|
      rr_interlacingSeqNonneg_reverse_pairwise using
        interlacing_nonneg := $hfs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeqNonneg.reverse $hfs)
  | `(tactic|
      rr_interlacingSeqNonneg_realrooted using
        interlacing_nonneg := $hfs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeqNonneg.realRooted $hfs)
  | `(tactic|
      rr_interlacingSeqNonneg_splits using
        interlacing_nonneg := $hfs:term,
        member := $hf:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeqNonneg.splits $hfs $hf)
  | `(tactic|
      rr_interlacingSeqNonneg_pos_lc using
        interlacing_nonneg := $hfs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeqNonneg.posLeadingCoeff $hfs)
  | `(tactic|
      rr_interlacingSeqNonneg_nonneg_coeffs using
        interlacing_nonneg := $hfs:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeqNonneg.nonnegCoeffs $hfs)
  | `(tactic|
      rr_interlacingSeq0Nonneg_filter_ne_zero using
        interlacing0_nonneg := $hfs:term,
        realrooted := $hreal:term) =>
      `(tactic|
        exact RealRooted.IsInterlacingSeq0Nonneg.filter_ne_zero_of_realRooted
          $hfs $hreal)

end Tactic
end RealRooted
