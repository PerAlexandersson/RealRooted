import RealRooted.MaWang
import RealRooted.Tactic.SideGoals

/-!
# Ma-Wang tactic

Dispatcher tactics:

```lean
rr_ma_wang
rr_finish_sequence
```

Primary target:
one-step derivative recurrences of the form

```text
P (n + 1) = u n * P n + v n * (P n).derivative.
```

The tactic should apply existing theorems such as `prec_ma_wang` and
`prec_of_interlaces_evalCoeff_nonpos`, then discharge certificate side goals.

First intended regression examples:

- `touchard`;
- `coloredSetPartitions`;
- `stirlingPermutations`;
- `typeBEulerian`;
- `simsun`.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_ma_wang)
  "rr_ma_wang" " using " term ", " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_named)
  "rr_ma_wang" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_ma_wang_same)
  "rr_ma_wang_same" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_same_named)
  "rr_ma_wang_same" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

syntax (name := rr_ma_wang_succ)
  "rr_ma_wang_succ" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_ma_wang_succ_named)
  "rr_ma_wang_succ" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "degree" ":=" term ","
    "target_pos_lc" ":=" term ","
    "source_pos_lc" ":=" term ","
    "root_sign" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_ma_wang using
        $hf:term, $hdegf:term, $hdeg_lo:term, $hdeg_hi:term, $hF_pos:term,
        $hf_pos:term, $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang using
          $hf, $hdegf, $hdeg_lo, $hdeg_hi, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        $hf:term, $hdegf:term, $hdeg:term, $hF_pos:term, $hf_pos:term,
        $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang_same
          $hf $hdegf $hdeg $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_same using $hf, $hdegf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        $hf:term, $hdegf:term, $hdeg:term, $hF_pos:term, $hf_pos:term,
        $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang_succ
          $hf $hdegf $hdeg $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_succ using $hf, $hdegf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)

end Tactic
end RealRooted
