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

syntax (name := rr_matrix0)
  "rr_matrix0" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
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

macro_rules
  | `(tactic|
      rr_matrix using
        $hn:term, $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term,
        $fs:term, $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq
          $hn $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix0 using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_of_2x2
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix0_weak using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term, $hfs_real:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_of_2x2_weak
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs $hfs_real)

end Tactic
end RealRooted
