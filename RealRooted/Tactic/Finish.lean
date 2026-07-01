import RealRooted.Basic
import RealRooted.Tactic.SideGoals

/-!
# Finish tactics

Small dispatchers for the proof tails that follow once an engine has produced a
`Prec` certificate.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_nonzero) "rr_nonzero" " using " term : tactic
syntax (name := rr_splits) "rr_splits" " using " term : tactic
syntax (name := rr_realrooted) "rr_realrooted" " using " term : tactic

syntax (name := rr_interlaces_with_degree)
  "rr_interlaces" " using " term ", " term : tactic

syntax (name := rr_interlaces_auto_degree)
  "rr_interlaces" " using " term : tactic

syntax (name := rr_prec0) "rr_prec0" " using " term : tactic

syntax (name := rr_prec_of_prec0)
  "rr_prec" " using " term ", " term ", " term : tactic

syntax (name := rr_gsturm_cons)
  "rr_gsturm_cons" " using " term ", " term : tactic

syntax (name := rr_sturm_cons)
  "rr_sturm_cons" " using " term ", " term : tactic

syntax (name := rr_sturm_base) "rr_sturm_base" : tactic

macro_rules
  | `(tactic| rr_nonzero using $h:term) =>
      `(tactic|
        first
          | exact ($h).1
          | exact ($h).1.1
          | exact ($h).2.1.1)
  | `(tactic| rr_splits using $h:term) =>
      `(tactic|
        first
          | exact ($h).2
          | exact ($h).1.2
          | exact ($h).2.1.2)
  | `(tactic| rr_realrooted using $h:term) =>
      `(tactic|
        first
          | exact $h
          | exact ($h).1
          | exact ($h).2.1)
  | `(tactic| rr_interlaces using $hprec:term, $hdeg:term) =>
      `(tactic|
        first
          | exact RealRooted.Prec.toInterlaces $hprec $hdeg
          | exact RealRooted.Prec.toInterlaces $hprec ($hdeg).symm)
  | `(tactic| rr_interlaces using $hprec:term) =>
      `(tactic|
        exact RealRooted.Prec.toInterlaces $hprec (by rr_side))
  | `(tactic| rr_prec0 using $hprec:term) =>
      `(tactic|
        exact RealRooted.Prec.toPrec0 $hprec)
  | `(tactic| rr_prec using $hprec0:term, $hf:term, $hg:term) =>
      `(tactic|
        exact RealRooted.Prec0.toPrec_of_ne $hprec0 $hf $hg)
  | `(tactic| rr_gsturm_cons using $hprec:term, $htail:term) =>
      `(tactic|
        simpa [RealRooted.IsGeneralizedSturmSeq] using And.intro $hprec $htail)
  | `(tactic| rr_sturm_cons using $hinter:term, $htail:term) =>
      `(tactic|
        simpa [RealRooted.IsSturmSeq] using And.intro $hinter $htail)
  | `(tactic| rr_sturm_base) =>
      `(tactic|
        simp [RealRooted.IsSturmSeq, RealRooted.IsGeneralizedSturmSeq])

end Tactic
end RealRooted
