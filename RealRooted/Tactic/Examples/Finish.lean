import RealRooted.Tactic.Finish

/-!
# Finish tactic examples

Abstract smoke tests for tactics that consume `Prec` certificates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 := by
  rr_nonzero using hfg

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 := by
  rr_nonzero

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g) : g.Splits := by
  rr_splits using hfg

example {f g : ℝ[X]} (hfg : Prec f g) : g.Splits := by
  rr_splits

example {f g : ℝ[X]} (hfg : Prec f g) : g.Splits := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 ∧ f.Splits := by
  rr_realrooted using hfg

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 ∧ f.Splits := by
  rr_realrooted

example {f g : ℝ[X]} (hfg : Prec f g) : g ≠ 0 ∧ g.Splits := by
  rr_realrooted using hfg

example {f g : ℝ[X]} (hfg : Prec f g) : g ≠ 0 ∧ g.Splits := by
  rr_realrooted

example {f g : ℝ[X]} (hfg : Prec f g) : g ≠ 0 := by
  rr_nonzero using hfg

example {f g : ℝ[X]} (hfg : Prec f g) : f.Splits := by
  rr_splits using hfg

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 ∧ f.Splits := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g) : g ≠ 0 ∧ g.Splits := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g) : g = 0 ∨ g.Splits := by
  rr_finish

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    f ≠ 0 ∧ f.Splits := by
  rr_realrooted using hfg

example {f : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) : f = 0 ∨ f.Splits := by
  rr_exact_realrooted_or_projection hf

example {f : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) : f = 0 ∨ f.Splits := by
  rr_finish

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    g ≠ 0 ∧ g.Splits := by
  rr_realrooted using hfg

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    g ≠ 0 ∧ g.Splits := by
  rr_realrooted

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    f ≠ 0 := by
  rr_nonzero using hfg

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    g ≠ 0 := by
  rr_nonzero

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    f.Splits := by
  rr_splits using hfg

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    g.Splits := by
  rr_splits

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    g = 0 ∨ g.Splits := by
  rr_finish

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    g ≠ 0 ∧ g.Splits := by
  rr_finish

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 ∧ f.Splits := by
  rr_realrooted using hgf

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 ∧ f.Splits := by
  rr_realrooted

example {g f : ℝ[X]} (hgf : Interlaces g f) : g ≠ 0 ∧ g.Splits := by
  rr_realrooted using hgf

example {g f : ℝ[X]} (hgf : Interlaces g f) : g ≠ 0 ∧ g.Splits := by
  rr_realrooted

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 := by
  rr_nonzero using hgf

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 := by
  rr_nonzero

example {g f : ℝ[X]} (hgf : Interlaces g f) : g.Splits := by
  rr_splits using hgf

example {g f : ℝ[X]} (hgf : Interlaces g f) : g.Splits := by
  rr_splits

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 ∧ f.Splits := by
  rr_finish

example {g f : ℝ[X]} (hgf : Interlaces g f) : g ≠ 0 ∧ g.Splits := by
  rr_finish

example {g f : ℝ[X]} (hgf : Interlaces g f) : g = 0 ∨ g.Splits := by
  rr_finish

example {g f : ℝ[X]} (hgf : Interlaces g f) :
    g.natDegree + 1 = f.natDegree := by
  rr_finish

example {g f : ℝ[X]} (hgf : Interlaces g f) :
    f.natDegree = g.natDegree + 1 := by
  rr_finish

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_nonzero using hP

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_finish

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, (P n).Splits := by
  rr_splits

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, (P n).Splits := by
  rr_finish

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_exact_realrooted_sequence_or_projection hP

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_finish

example {P : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    P n ≠ 0 := by
  rr_nonzero using hP

example {P : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    P n ≠ 0 := by
  rr_finish

example {P : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    (P n).Splits := by
  rr_splits

example {P : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    (P n).Splits := by
  rr_finish

example {P : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    P n = 0 ∨ (P n).Splits := by
  rr_finish

example {P : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_realrooted

example {P : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_finish

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n ≠ 0 ∧ (A n).Splits := by
  rr_realrooted using hP

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n ≠ 0 ∧ (B n).Splits := by
  rr_realrooted

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n ≠ 0 ∧ (B n).Splits := by
  rr_finish

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n ≠ 0 := by
  rr_nonzero using hP

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, (B n).Splits := by
  rr_splits

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, (B n).Splits := by
  rr_finish

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n = 0 ∨ (B n).Splits := by
  rr_exact_realrooted_pair_sequence_or_projection hP

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, B n = 0 ∨ (B n).Splits := by
  rr_finish

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    A n ≠ 0 ∧ (A n).Splits := by
  rr_realrooted using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    B n ≠ 0 := by
  rr_nonzero

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    B n ≠ 0 := by
  rr_finish

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    (A n).Splits := by
  rr_splits using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    (A n).Splits := by
  rr_finish

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    A n = 0 ∨ (A n).Splits := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_interlaces using hfg, hdeg

example {f g : ℝ[X]} (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Interlaces f g := by
  rr_interlaces using hfg, hdeg

example {f g : ℝ[X]} (hfg : Prec f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Interlaces f g := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g) : Prec0 f g := by
  rr_prec0 using hfg

example {f g : ℝ[X]} (hfg : Prec f g) : Prec0 f g := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec0 f g) (hf : f ≠ 0) (hg : g ≠ 0) :
    Prec f g := by
  rr_prec using hfg, hf, hg

example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hstep : ∀ n : Nat,
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_prec_sequence using
    base := hbase,
    step := hstep

example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hstep : ∀ n : Nat,
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_sequence_realrooted using
    base := hbase,
    step := hstep

example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hstep : ∀ n : Nat,
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_prec_sequence_realrooted using
    base := hbase,
    step := hstep

example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hstep : ∀ n : Nat,
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, (P n).Splits := by
  rr_prec_sequence_realrooted using
    base := hbase,
    step := hstep

example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_prec_sequence_branches using
    base := hbase,
    degree_branch := hdegree,
    same := hsame,
    successor := hsucc

example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_prec_sequence_branches_realrooted using
    base := hbase,
    degree_branch := hdegree,
    same := hsame,
    successor := hsucc

example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hdegree : ∀ n : Nat,
      (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
        (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1)
    (hsame : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2)))
    (hsucc : ∀ n : Nat, (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1 →
      Prec (P n) (P (n + 1)) → Prec (P (n + 1)) (P (n + 2))) :
    ∀ n : Nat, (P n).Splits := by
  rr_prec_sequence_branches_realrooted using
    base := hbase,
    degree_branch := hdegree,
    same := hsame,
    successor := hsucc

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : Prec q p) (htail : IsGeneralizedSturmSeq (q :: rest)) :
    IsGeneralizedSturmSeq (p :: q :: rest) := by
  rr_gsturm_cons using hpq, htail

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : Prec q p) (htail : IsGeneralizedSturmSeq (q :: rest)) :
    IsGeneralizedSturmSeq (p :: q :: rest) := by
  rr_finish

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : Interlaces q p) (htail : IsSturmSeq (q :: rest)) :
    IsSturmSeq (p :: q :: rest) := by
  rr_sturm_cons using hpq, htail

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : Interlaces q p) (htail : IsSturmSeq (q :: rest)) :
    IsSturmSeq (p :: q :: rest) := by
  rr_finish

example : IsSturmSeq ([] : List ℝ[X]) := by
  rr_sturm_base

example (p : ℝ[X]) : IsGeneralizedSturmSeq [p] := by
  rr_sturm_base

@[rr_nonzero] theorem rr_finish_true_smoke : True := by
  trivial

example : True := by
  rr_finish

end Tactic
end RealRooted
