import RealRooted.MatrixInterlacing
import RealRooted.RowThreshold
import RealRooted.StaircaseSum
import RealRooted.Tactic.SideGoals

/-!
# Matrix-transfer tactic

Dispatcher tactics:

```lean
rr_matrix
rr_matrix0
rr_matrix0_weak
rr_matrix0_realrooted
rr_matrix0_filter_ne_zero
```

Primary target:
refined vector recurrences already written as

```text
F_next = matPolyAction G F.
```

The tactics apply `matrix_preserves_interlacing_seq`,
`matrix_preserves_interlacing_seq0_of_2x2`, or row-threshold wrappers after
the user supplies the matrix action, rectangularity, entry nonnegativity, and
`2 x 2` Branden conditions.

Family J warning:
do not attack raw scalar long-lag recurrences.  First derive a refined vector
or production-matrix recurrence.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_matrix)
  "rr_matrix" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_matrix_named)
  "rr_matrix" " using "
    "n_pos" ":=" term ","
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

syntax (name := rr_matrix0)
  "rr_matrix0" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_matrix0_named)
  "rr_matrix0" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

syntax (name := rr_matrix0_weak)
  "rr_matrix0_weak" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_matrix0_weak_named)
  "rr_matrix0_weak" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term ","
    "input_real_rooted" ":=" term :
  tactic

syntax (name := rr_matrix0_realrooted)
  "rr_matrix0_realrooted" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_matrix0_realrooted_named)
  "rr_matrix0_realrooted" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

syntax (name := rr_matrix0_filter_ne_zero)
  "rr_matrix0_filter_ne_zero" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_matrix0_filter_ne_zero_named)
  "rr_matrix0_filter_ne_zero" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

syntax (name := rr_row_threshold_matrix_named)
  "rr_row_threshold_matrix" " using "
    "n_pos" ":=" term ","
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "row_threshold" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

syntax (name := rr_row_threshold_matrix0_named)
  "rr_row_threshold_matrix0" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "row_threshold" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

syntax (name := rr_row_threshold_entry_nonneg_named)
  "rr_row_threshold_entry_nonneg" " using "
    "row_threshold" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_matrix using
        $hn:term, $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term,
        $fs:term, $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq
          $hn $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix using
        n_pos := $hn:term,
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_matrix using $hn, $G, $hG_rect, $hG_nonneg, $hG_affine, $fs,
          $hfs_len, $hfs)
  | `(tactic|
      rr_matrix0 using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_of_2x2
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix0 using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_matrix0 using $G, $hG_rect, $hG_nonneg, $hG_affine, $fs, $hfs_len,
          $hfs)
  | `(tactic|
      rr_matrix0_weak using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term, $hfs_real:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_of_2x2_weak
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs $hfs_real)
  | `(tactic|
      rr_matrix0_weak using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term,
        input_real_rooted := $hfs_real:term) =>
      `(tactic|
        rr_matrix0_weak using $G, $hG_rect, $hG_nonneg, $hG_affine, $fs,
          $hfs_len, $hfs, $hfs_real)
  | `(tactic|
      rr_matrix0_realrooted using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_of_2x2_realRooted
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix0_realrooted using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_matrix0_realrooted using $G, $hG_rect, $hG_nonneg, $hG_affine, $fs,
          $hfs_len, $hfs)
  | `(tactic|
      rr_matrix0_filter_ne_zero using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix0_filter_ne_zero using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_matrix0_filter_ne_zero using $G, $hG_rect, $hG_nonneg, $hG_affine,
          $fs, $hfs_len, $hfs)
  | `(tactic|
      rr_row_threshold_matrix using
        n_pos := $hn:term,
        matrix := $G:term,
        rectangular := $hG_rect:term,
        row_threshold := $hG_threshold:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        exact RealRooted.rowThreshold_matrix_preserves_interlacing_seq_of_2x2
          $hn $G $hG_rect $hG_threshold $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_row_threshold_matrix0 using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        row_threshold := $hG_threshold:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        exact RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_of_2x2
          $G $hG_rect $hG_threshold $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_row_threshold_entry_nonneg using
        row_threshold := $hG_threshold:term) =>
      `(tactic|
        exact RealRooted.hasRowThresholdLinearStructure_nonneg $hG_threshold)

end Tactic
end RealRooted
