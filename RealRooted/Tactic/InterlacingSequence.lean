import RealRooted.InterlacingSequenceBasic

/-!
# Interlacing-sequence tactic frontends

Thin wrappers for list-level interlacing sequence plumbing.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_interlacingSeq_iff_pairwise_named)
  "rr_interlacingSeq_iff_pairwise" :
  tactic

syntax (name := rr_interlacingSeq0_iff_pairwise_named)
  "rr_interlacingSeq0_iff_pairwise" :
  tactic

syntax (name := rr_interlacingSeq_to_interlacingSeq0_named)
  "rr_interlacingSeq_to_interlacingSeq0" " using "
    "interlacing" ":=" term :
  tactic

syntax (name := rr_interlacingSeq_prec_named)
  "rr_interlacingSeq_prec" " using "
    "interlacing" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_interlacingSeq0_prec0_named)
  "rr_interlacingSeq0_prec0" " using "
    "interlacing0" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_interlacingSeq_sublist_named)
  "rr_interlacingSeq_sublist" " using "
    "interlacing" ":=" term ","
    "sublist" ":=" term :
  tactic

syntax (name := rr_interlacingSeqNonneg_sublist_named)
  "rr_interlacingSeqNonneg_sublist" " using "
    "interlacing_nonneg" ":=" term ","
    "sublist" ":=" term :
  tactic

syntax (name := rr_interlacingSeq0_sublist_named)
  "rr_interlacingSeq0_sublist" " using "
    "interlacing0" ":=" term ","
    "sublist" ":=" term :
  tactic

syntax (name := rr_interlacingSeq0Nonneg_sublist_realrooted_named)
  "rr_interlacingSeq0Nonneg_sublist_realrooted" " using "
    "interlacing0_nonneg" ":=" term ","
    "sublist" ":=" term ","
    "realrooted" ":=" term ","
    "nonzero" ":=" term :
  tactic

syntax (name := rr_interlacingSeq_append_named)
  "rr_interlacingSeq_append" " using "
    "left_interlacing" ":=" term ","
    "right_interlacing" ":=" term ","
    "cross_prec" ":=" term :
  tactic

syntax (name := rr_interlacingSeq_reverse_pairwise_named)
  "rr_interlacingSeq_reverse_pairwise" " using "
    "interlacing" ":=" term :
  tactic

syntax (name := rr_interlacingSeq0_reverse_pairwise_named)
  "rr_interlacingSeq0_reverse_pairwise" " using "
    "interlacing0" ":=" term :
  tactic

syntax (name := rr_interlacingSeqNonneg_reverse_pairwise_named)
  "rr_interlacingSeqNonneg_reverse_pairwise" " using "
    "interlacing_nonneg" ":=" term :
  tactic

syntax (name := rr_interlacingSeqNonneg_realrooted_named)
  "rr_interlacingSeqNonneg_realrooted" " using "
    "interlacing_nonneg" ":=" term :
  tactic

syntax (name := rr_interlacingSeqNonneg_splits_named)
  "rr_interlacingSeqNonneg_splits" " using "
    "interlacing_nonneg" ":=" term ","
    "member" ":=" term :
  tactic

syntax (name := rr_interlacingSeqNonneg_pos_lc_named)
  "rr_interlacingSeqNonneg_pos_lc" " using "
    "interlacing_nonneg" ":=" term :
  tactic

syntax (name := rr_interlacingSeqNonneg_nonneg_coeffs_named)
  "rr_interlacingSeqNonneg_nonneg_coeffs" " using "
    "interlacing_nonneg" ":=" term :
  tactic

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
      rr_interlacingSeq_prec using
        interlacing := $hfs:term,
        index_lt := $hij:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq.prec $hfs $hij)
  | `(tactic|
      rr_interlacingSeq0_prec0 using
        interlacing0 := $hfs:term,
        index_lt := $hij:term) =>
      `(tactic| exact RealRooted.IsInterlacingSeq0.prec0 $hfs $hij)
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
        cross_prec := $hfg:term) =>
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
