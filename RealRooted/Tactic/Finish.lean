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

/-- Project the nonvanishing half of a real-rootedness certificate. -/
theorem ne_zero_of_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    p ≠ 0 :=
  hp.1

/-- Project the splitting half of a real-rootedness certificate. -/
theorem splits_of_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    p.Splits :=
  hp.2

/-- Project real-rootedness of the left argument from a `Prec` certificate. -/
theorem left_isRealRooted_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    f ≠ 0 ∧ f.Splits :=
  hfg.1

/-- Project real-rootedness of the right argument from a `Prec` certificate. -/
theorem right_isRealRooted_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    g ≠ 0 ∧ g.Splits :=
  hfg.2.1

/-- Project left-argument nonvanishing from a `Prec` certificate. -/
theorem left_ne_zero_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    f ≠ 0 :=
  (left_isRealRooted_of_prec hfg).1

/-- Project left-argument splitting from a `Prec` certificate. -/
theorem left_splits_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    f.Splits :=
  (left_isRealRooted_of_prec hfg).2

/-- Project right-argument nonvanishing from a `Prec` certificate. -/
theorem right_ne_zero_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    g ≠ 0 :=
  (right_isRealRooted_of_prec hfg).1

/-- Project right-argument splitting from a `Prec` certificate. -/
theorem right_splits_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    g.Splits :=
  (right_isRealRooted_of_prec hfg).2

/-- Project real-rootedness of the right argument from an `Interlaces` certificate. -/
theorem right_isRealRooted_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    f ≠ 0 ∧ f.Splits :=
  hgf.1

/-- Project real-rootedness of the left argument from an `Interlaces` certificate. -/
theorem left_isRealRooted_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    g ≠ 0 ∧ g.Splits :=
  hgf.2.1

/-- Project right-argument nonvanishing from an `Interlaces` certificate. -/
theorem right_ne_zero_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    f ≠ 0 :=
  (right_isRealRooted_of_interlaces hgf).1

/-- Project right-argument splitting from an `Interlaces` certificate. -/
theorem right_splits_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    f.Splits :=
  (right_isRealRooted_of_interlaces hgf).2

/-- Project left-argument nonvanishing from an `Interlaces` certificate. -/
theorem left_ne_zero_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    g ≠ 0 :=
  (left_isRealRooted_of_interlaces hgf).1

/-- Project left-argument splitting from an `Interlaces` certificate. -/
theorem left_splits_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    g.Splits :=
  (left_isRealRooted_of_interlaces hgf).2

/-- Project the successor-degree equality from an `Interlaces` certificate. -/
theorem natDegree_succ_of_interlaces {g f : ℝ[X]} (hgf : Interlaces g f) :
    g.natDegree + 1 = f.natDegree :=
  hgf.2.2.1

/-- Project row-wise nonvanishing from a sequence real-rootedness certificate. -/
theorem ne_zero_of_isRealRooted_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (hP n).1

/-- Project row-wise splitting from a sequence real-rootedness certificate. -/
theorem splits_of_isRealRooted_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, (P n).Splits :=
  fun n => (hP n).2

/-- Project left row-wise nonvanishing from a pair-sequence certificate. -/
theorem left_ne_zero_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n ≠ 0 :=
  fun n => (hP n).1.1

/-- Project left row-wise splitting from a pair-sequence certificate. -/
theorem left_splits_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, (A n).Splits :=
  fun n => (hP n).1.2

/-- Project right row-wise nonvanishing from a pair-sequence certificate. -/
theorem right_ne_zero_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n ≠ 0 :=
  fun n => (hP n).2.1

/-- Project right row-wise splitting from a pair-sequence certificate. -/
theorem right_splits_of_isRealRooted_pair_sequence {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, (B n).Splits :=
  fun n => (hP n).2.2

namespace Tactic

syntax (name := rr_exact_realrooted_or_projection)
  "rr_exact_realrooted_or_projection" term :
  tactic

syntax (name := rr_exact_realrooted_sequence_or_projection)
  "rr_exact_realrooted_sequence_or_projection" term :
  tactic

syntax (name := rr_exact_realrooted_pair_sequence_or_projection)
  "rr_exact_realrooted_pair_sequence_or_projection" term :
  tactic

syntax (name := rr_nonzero) "rr_nonzero" " using " term : tactic
syntax (name := rr_splits) "rr_splits" " using " term : tactic
syntax (name := rr_realrooted) "rr_realrooted" " using " term : tactic
syntax (name := rr_nonzero_auto) "rr_nonzero" : tactic
syntax (name := rr_splits_auto) "rr_splits" : tactic
syntax (name := rr_realrooted_auto) "rr_realrooted" : tactic

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
    "successor" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_degree_branch)
  "rr_prec_sequence_branches" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_realrooted)
  "rr_prec_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_prec_sequence_branches_realrooted_degree_branch)
  "rr_prec_sequence_branches_realrooted" " using "
    "base" ":=" term ","
    "degree_branch" ":=" term ","
    "same" ":=" term ","
    "successor" ":=" term :
  tactic

syntax (name := rr_finish) "rr_finish" : tactic

macro_rules
  | `(tactic| rr_exact_realrooted_or_projection $h:term) =>
      `(tactic|
        first
          | exact $h
          | exact RealRooted.ne_zero_of_isRealRooted $h
          | exact RealRooted.splits_of_isRealRooted $h
          | exact RealRooted.left_isRealRooted_of_prec $h
          | exact RealRooted.right_isRealRooted_of_prec $h
          | exact RealRooted.left_ne_zero_of_prec $h
          | exact RealRooted.right_ne_zero_of_prec $h
          | exact RealRooted.left_splits_of_prec $h
          | exact RealRooted.right_splits_of_prec $h
          | exact RealRooted.right_isRealRooted_of_interlaces $h
          | exact RealRooted.left_isRealRooted_of_interlaces $h
          | exact RealRooted.right_ne_zero_of_interlaces $h
          | exact RealRooted.left_ne_zero_of_interlaces $h
          | exact RealRooted.right_splits_of_interlaces $h
          | exact RealRooted.left_splits_of_interlaces $h)
  | `(tactic| rr_exact_realrooted_sequence_or_projection $h:term) =>
      `(tactic|
        first
          | exact $h
          | exact RealRooted.ne_zero_of_isRealRooted_sequence $h
          | exact RealRooted.splits_of_isRealRooted_sequence $h)
  | `(tactic| rr_exact_realrooted_pair_sequence_or_projection $h:term) =>
      `(tactic|
        first
          | exact $h
          | exact RealRooted.left_ne_zero_of_isRealRooted_pair_sequence $h
          | exact RealRooted.left_splits_of_isRealRooted_pair_sequence $h
          | exact RealRooted.right_ne_zero_of_isRealRooted_pair_sequence $h
          | exact RealRooted.right_splits_of_isRealRooted_pair_sequence $h)
  | `(tactic| rr_nonzero using $h:term) =>
      `(tactic|
        first
          | exact RealRooted.left_ne_zero_of_prec $h
          | exact RealRooted.right_ne_zero_of_prec $h
          | exact RealRooted.right_ne_zero_of_interlaces $h
          | exact RealRooted.left_ne_zero_of_interlaces $h
          | exact ($h).1
          | exact ($h).1.1
          | exact ($h).2.1.1)
  | `(tactic| rr_nonzero) =>
      `(tactic|
        first
          | rr_lookup
          | exact RealRooted.left_ne_zero_of_prec (by rr_lookup)
          | exact RealRooted.right_ne_zero_of_prec (by rr_lookup)
          | exact RealRooted.right_ne_zero_of_interlaces (by rr_lookup)
          | exact RealRooted.left_ne_zero_of_interlaces (by rr_lookup)
          | assumption
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_splits using $h:term) =>
      `(tactic|
        first
          | exact RealRooted.left_splits_of_prec $h
          | exact RealRooted.right_splits_of_prec $h
          | exact RealRooted.right_splits_of_interlaces $h
          | exact RealRooted.left_splits_of_interlaces $h
          | exact ($h).2
          | exact ($h).1.2
          | exact ($h).2.1.2)
  | `(tactic| rr_splits) =>
      `(tactic|
        first
          | rr_lookup
          | exact RealRooted.left_splits_of_prec (by rr_lookup)
          | exact RealRooted.right_splits_of_prec (by rr_lookup)
          | exact RealRooted.right_splits_of_interlaces (by rr_lookup)
          | exact RealRooted.left_splits_of_interlaces (by rr_lookup)
          | assumption
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
  | `(tactic| rr_realrooted using $h:term) =>
      `(tactic|
        first
          | exact $h
          | exact RealRooted.left_isRealRooted_of_prec $h
          | exact RealRooted.right_isRealRooted_of_prec $h
          | exact RealRooted.right_isRealRooted_of_interlaces $h
          | exact RealRooted.left_isRealRooted_of_interlaces $h
          | exact ($h).1
          | exact ($h).2.1)
  | `(tactic| rr_realrooted) =>
      `(tactic|
        first
          | rr_lookup
          | exact RealRooted.left_isRealRooted_of_prec (by rr_lookup)
          | exact RealRooted.right_isRealRooted_of_prec (by rr_lookup)
          | exact RealRooted.right_isRealRooted_of_interlaces (by rr_lookup)
          | exact RealRooted.left_isRealRooted_of_interlaces (by rr_lookup)
          | assumption
          | simp_all [RealRooted.Prec, RealRooted.Interlaces])
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
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_sequence $hbase $hstep))
  | `(tactic|
      rr_prec_sequence_branches using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_prec_sequence_branches using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        exact RealRooted.prec_sequence_of_base_and_degree_branches
          $hbase $hbranch $hsame $hsucc)
  | `(tactic|
      rr_prec_sequence_branches_realrooted using
        base := $hbase:term,
        degree := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_sequence_degree_branches
            $hbase $hbranch $hsame $hsucc))
  | `(tactic|
      rr_prec_sequence_branches_realrooted using
        base := $hbase:term,
        degree_branch := $hbranch:term,
        same := $hsame:term,
        successor := $hsucc:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_sequence_degree_branches
            $hbase $hbranch $hsame $hsucc))
  | `(tactic| rr_finish) =>
      `(tactic|
        first
          | rr_lookup
          | assumption
          | exact RealRooted.left_isRealRooted_of_prec (by rr_lookup)
          | exact RealRooted.right_isRealRooted_of_prec (by rr_lookup)
          | exact RealRooted.left_ne_zero_of_prec (by rr_lookup)
          | exact RealRooted.right_ne_zero_of_prec (by rr_lookup)
          | exact RealRooted.left_splits_of_prec (by rr_lookup)
          | exact RealRooted.right_splits_of_prec (by rr_lookup)
          | exact RealRooted.right_isRealRooted_of_interlaces (by rr_lookup)
          | exact RealRooted.left_isRealRooted_of_interlaces (by rr_lookup)
          | exact RealRooted.right_ne_zero_of_interlaces (by rr_lookup)
          | exact RealRooted.left_ne_zero_of_interlaces (by rr_lookup)
          | exact RealRooted.right_splits_of_interlaces (by rr_lookup)
          | exact RealRooted.left_splits_of_interlaces (by rr_lookup)
          | exact RealRooted.natDegree_succ_of_interlaces (by rr_lookup)
          | exact (RealRooted.natDegree_succ_of_interlaces (by rr_lookup)).symm
          | exact RealRooted.Prec.toInterlaces (by rr_lookup) (by rr_lookup)
          | exact RealRooted.Prec.toInterlaces (by rr_lookup) (by
              symm
              rr_lookup)
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
