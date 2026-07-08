import RealRooted.Basic
import RealRooted.Tactic.Lookup
import RealRooted.Tactic.Sign
import RealRooted.Tactic.SideGoals

/-!
# Finish tactics

Small dispatchers for the proof tails that follow once an engine has produced a
`Prec` certificate.
-/

open Polynomial

namespace RealRooted

/-- Generic `Prec`-chain induction from one base case and a successor step.

This is the plateau-safe sequence shell: the step only needs the previous
`Prec` certificate, not a degree-increasing `Interlaces` certificate. -/
theorem prec_sequence_of_base_and_step {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hstep : ∀ n : Nat, Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact hbase
  | succ n ih =>
      exact hstep n ih

/-- Real-rootedness corollary of a generic `Prec`-chain induction. -/
theorem isRealRooted_of_prec_sequence {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hstep : ∀ n : Nat, Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) :=
    prec_sequence_of_base_and_step hbase hstep
  intro n
  cases n with
  | zero =>
      exact hbase.1
  | succ n =>
      exact (hprec n).2.1

/-- Generic `Prec`-chain induction with a same-degree/successor-degree branch.

This wraps plateau recurrences such as degree patterns `1,1,2,2,3,3,...`.
The theorem does not prove either branch; it carries the induction hypothesis
and dispatches to the sequence-specific same-degree or successor-degree step. -/
theorem prec_sequence_of_base_and_degree_branches {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hbranch : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  refine prec_sequence_of_base_and_step hbase ?_
  intro n hprev
  rcases hbranch n with hsame_degree | hsucc_degree
  · exact hsame n hsame_degree hprev
  · exact hsucc n hsucc_degree hprev

/-- Real-rootedness corollary of a branched generic `Prec`-chain induction. -/
theorem isRealRooted_of_prec_sequence_degree_branches {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hbranch : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  apply isRealRooted_of_prec_sequence hbase
  intro n hprev
  rcases hbranch n with hsame_degree | hsucc_degree
  · exact hsame n hsame_degree hprev
  · exact hsucc n hsucc_degree hprev

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

syntax (name := rr_prec_sequence)
  "rr_prec_sequence" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_prec_sequence_realrooted)
  "rr_prec_sequence_realrooted" " using "
    "base" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches)
  "rr_prec_sequence_branches" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "succ" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_degree_branch)
  "rr_prec_sequence_branches" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "succ" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_realrooted)
  "rr_prec_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "succ" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_realrooted_degree_branch)
  "rr_prec_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "succ" ":=" term :
  tactic

syntax (name := rr_finish) "rr_finish" : tactic

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
  | `(tactic|
      rr_prec_sequence using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_step $hbase $hstep)
  | `(tactic|
      rr_prec_sequence_realrooted using
        base := $hbase:term,
        step := $hstep:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_prec_sequence $hbase $hstep)
  | `(tactic|
      rr_prec_sequence_branches using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        succ := $hsucc:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_prec_sequence_branches using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        succ := $hsucc:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_prec_sequence_branches_realrooted using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        succ := $hsucc:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_prec_sequence_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_prec_sequence_branches_realrooted using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        succ := $hsucc:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_prec_sequence_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic| rr_finish) =>
      `(tactic|
        first
          | rr_lookup
          | assumption
          | rr_sign
          | simp_all [
              RealRooted.Prec,
              RealRooted.Prec0,
              RealRooted.Interlaces,
              RealRooted.IsSturmSeq,
              RealRooted.IsGeneralizedSturmSeq]
          | rr_side)

end Tactic
end RealRooted
