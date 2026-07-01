import RealRooted.GeneralizedLiuWang
import RealRooted.Tactic.SideGoals

/-!
# Generalized Liu-Wang tactic

Dispatcher tactics:

```lean
rr_liu_wang
rr_liu_wang_strict
```

Primary target:
finite weighted sums where one or more previous polynomials interlace a common
base polynomial, and the coefficient polynomials have the required sign at
the roots of the base.

The tactics apply `prec_generalizedLiuWang_of_no_common` or the strict
finite-family variants after the user supplies the distinguished interlacer
and remaining summands.

First intended regression examples:

- clean Family E three-term recurrences;
- selected Family G/Jacobi-like recurrences;
- `LiuWangBenchmark` after the basic shape is stable.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_liu_wang)
  "rr_liu_wang" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_liu_wang_strict)
  "rr_liu_wang_strict" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_liu_wang_strict_same)
  "rr_liu_wang_strict_same" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

syntax (name := rr_liu_wang_strict_succ)
  "rr_liu_wang_strict_succ" " using " term ", "
    term ", "
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
      rr_liu_wang using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg_lo:term, $hdeg_hi:term, $hno:term, $hb_nonpos:term) =>
      `(tactic|
        exact RealRooted.prec_generalizedLiuWang_of_no_common
          $hgf $hg_pos $hl_inter $hl_pos $hl_nonpos
          $hF_pos $hdeg_lo $hdeg_hi $hno $hb_nonpos)
  | `(tactic|
      rr_liu_wang_strict using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg_lo:term, $hdeg_hi:term, $hno:term, $hb_neg:term) =>
      `(tactic|
        exact RealRooted.prec_generalizedLiuWang_strict
          $hgf $hg_pos $hl_inter $hl_pos $hl_nonpos
          $hF_pos $hdeg_lo $hdeg_hi $hno $hb_neg)
  | `(tactic|
      rr_liu_wang_strict_same using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg:term, $hno:term, $hb_neg:term) =>
      `(tactic|
        exact RealRooted.prec_generalizedLiuWang_strict_same
          $hgf $hg_pos $hl_inter $hl_pos $hl_nonpos
          $hF_pos $hdeg $hno $hb_neg)
  | `(tactic|
      rr_liu_wang_strict_succ using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg:term, $hno:term, $hb_neg:term) =>
      `(tactic|
        exact RealRooted.prec_generalizedLiuWang_strict_succ
          $hgf $hg_pos $hl_inter $hl_pos $hl_nonpos
          $hF_pos $hdeg $hno $hb_neg)

end Tactic
end RealRooted
