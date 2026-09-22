import RealRooted.InterlacingSequenceBasic
import RealRooted.Tactic.Finish

open Polynomial

namespace RealRooted
namespace Tactic

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hstep : ∀ n : Nat,
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_prec_sequence using
    base := hbase,
    step := hstep

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hstep : ∀ n : Nat,
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_finish using hbase, hstep

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hstep : ∀ n : Nat,
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_sequence_realrooted using
    base := hbase,
    step := hstep

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hstep : ∀ n : Nat,
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_finish using hbase, hstep

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hstep : ∀ n : Nat,
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, (P n).Splits := by
  rr_prec_sequence_realrooted using
    base := hbase,
    step := hstep

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hstep : ∀ n : Nat,
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, (P n).Splits := by
  rr_finish_sequence using
    base := hbase,
    step := hstep

example {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_finish_sequence using
    prec := hprec

example {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_finish using hprec

example {P : Nat → ℝ[X]} {n : Nat}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    P n ≠ 0 := by
  rr_finish_sequence using
    prec := hprec

example {P : Nat → ℝ[X]} {n : Nat}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    (P n).Splits := by
  rr_finish using hprec

example {P : Nat → ℝ[X]} {n : Nat}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    (P n).Splits := by
  rr_finish

example {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1)))
    (hdegree : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_finish_sequence using
    prec := hprec,
    degree := hdegree

example {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1)))
    (hdegree : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_finish using hprec, hdegree

example {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1)))
    (hdegree : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := by
  rr_finish

example {P : Nat → ℝ[X]} {n : Nat}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1)))
    (hdegree : ∀ n : Nat, (P (n + 1)).natDegree = (P n).natDegree + 1) :
    Interlaces (P n) (P (n + 1)) := by
  rr_finish_sequence using
    prec := hprec,
    degree := hdegree

example {P : Nat → ℝ[X]} {n : Nat}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1)))
    (hdegree : ∀ n : Nat, (P (n + 1)).natDegree = (P n).natDegree + 1) :
    Interlaces (P n) (P (n + 1)) := by
  rr_finish using hprec, hdegree

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_prec_sequence_branches using
    base := hbase,
    degree_branch := hdegree,
    same := hsame,
    successor := hsucc

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_finish using hbase, hdegree, hsame, hsucc

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_sequence_branches_realrooted using
    base := hbase,
    degree_branch := hdegree,
    same := hsame,
    successor := hsucc

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, (P n).Splits := by
  rr_finish using hbase, hdegree, hsame, hsucc

example {P : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      StrictInterl (P n) (P (n + 1)) → StrictInterl (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_finish_sequence_branches using
    base := hbase,
    degree_branch := hdegree,
    same := hsame,
    successor := hsucc

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : StrictInterl q p) (htail : IsGeneralizedSturmSeq (q :: rest)) :
    IsGeneralizedSturmSeq (p :: q :: rest) := by
  rr_gsturm_cons using hpq, htail

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : StrictInterl q p) (htail : IsGeneralizedSturmSeq (q :: rest)) :
    IsGeneralizedSturmSeq (p :: q :: rest) := by
  rr_finish using hpq, htail

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : StrictInterl q p) (htail : IsGeneralizedSturmSeq (q :: rest)) :
    IsGeneralizedSturmSeq (p :: q :: rest) := by
  rr_finish

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : Interlaces q p) (htail : IsSturmSeq (q :: rest)) :
    IsSturmSeq (p :: q :: rest) := by
  rr_sturm_cons using hpq, htail

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : Interlaces q p) (htail : IsSturmSeq (q :: rest)) :
    IsSturmSeq (p :: q :: rest) := by
  rr_finish using hpq, htail

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : Interlaces q p) (htail : IsSturmSeq (q :: rest)) :
    IsSturmSeq (p :: q :: rest) := by
  rr_finish

example : IsSturmSeq ([] : List ℝ[X]) := by rr_sturm_base

example (p : ℝ[X]) : IsGeneralizedSturmSeq [p] := by rr_sturm_base

@[rr_nonzero] theorem rr_finish_true_smoke : True := by trivial

example : True := by rr_finish


end Tactic
end RealRooted
