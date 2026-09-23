import RealRooted.InterlacingSequenceBasic
import RealRooted.Tactic.Finish

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} (hfg : StrictInterl f g) : f ≠ 0 := by rr_nonzero using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) : f ≠ 0 := by rr_nonzero

example {f g : ℝ[X]} (hfg : StrictInterl f g) : f ≠ 0 := by rr_finish

example {f g : ℝ[X]} (hfg : StrictInterl f g) : f ≠ 0 := by rr_finish using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) : g.Splits := by rr_splits using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) : g.Splits := by rr_splits

example {f g : ℝ[X]} (hfg : StrictInterl f g) : g.Splits := by rr_finish

example {f g : ℝ[X]} (hfg : StrictInterl f g) : f ≠ 0 ∧ f.Splits := by rr_realrooted using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) : f ≠ 0 ∧ f.Splits := by rr_realrooted

example {f g : ℝ[X]} (hfg : StrictInterl f g) : g ≠ 0 ∧ g.Splits := by rr_realrooted using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) : g ≠ 0 ∧ g.Splits := by rr_realrooted

example {f g : ℝ[X]} (hfg : StrictInterl f g) : g ≠ 0 := by rr_nonzero using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) : f.Splits := by rr_splits using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) : f ≠ 0 ∧ f.Splits := by rr_finish

example {f g : ℝ[X]} (hfg : StrictInterl f g) : g ≠ 0 ∧ g.Splits := by rr_finish

example {f g : ℝ[X]} (hfg : StrictInterl f g) : g ≠ 0 ∧ g.Splits := by rr_finish using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) : g = 0 ∨ g.Splits := by rr_finish

example {f g : ℝ[X]}
    (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    f ≠ 0 ∧ f.Splits := by
  rr_realrooted using hfg

example {f : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) : f = 0 ∨ f.Splits := by
  rr_exact_realrooted_or_projection hf

example {f : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) : f = 0 ∨ f.Splits := by rr_finish

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

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 ∧ f.Splits := by rr_realrooted using hgf

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 ∧ f.Splits := by rr_realrooted

example {g f : ℝ[X]} (hgf : Interlaces g f) : g ≠ 0 ∧ g.Splits := by rr_realrooted using hgf

example {g f : ℝ[X]} (hgf : Interlaces g f) : g ≠ 0 ∧ g.Splits := by rr_realrooted

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 := by rr_nonzero using hgf

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 := by rr_nonzero

example {g f : ℝ[X]} (hgf : Interlaces g f) : g.Splits := by rr_splits using hgf

example {g f : ℝ[X]} (hgf : Interlaces g f) : g.Splits := by rr_splits

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 ∧ f.Splits := by rr_finish

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 ∧ f.Splits := by rr_finish using hgf

example {g f : ℝ[X]} (hgf : Interlaces g f) : g ≠ 0 ∧ g.Splits := by rr_finish

example {g f : ℝ[X]} (hgf : Interlaces g f) : g = 0 ∨ g.Splits := by rr_finish

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
    (hP : ∀ n : Nat, P n ≠ 0) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_nonzero using hP

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_finish

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_finish using hP

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, (P n).Splits := by
  rr_splits

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat, (P n).Splits := by
  rr_splits using hP

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

example {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_nonzero using hprec

example {P : Nat → ℝ[X]} {n : Nat}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    P n ≠ 0 := by
  rr_nonzero using hprec

example {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    ∀ n : Nat, (P n).Splits := by
  rr_splits using hprec

example {P : Nat → ℝ[X]} {n : Nat}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    (P n).Splits := by
  rr_splits using hprec

example {P : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_zero_or_splits using hprec

example {P : Nat → ℝ[X]} {n : Nat}
    (hprec : ∀ n : Nat, StrictInterl (P n) (P (n + 1))) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_realrooted using hprec

example {A B : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (A n) (B n)) :
    ∀ n : Nat, A n ≠ 0 := by
  rr_nonzero using hprec

example {A B : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (A n) (B n)) :
    ∀ n : Nat, B n ≠ 0 := by
  rr_nonzero using hprec

example {A B : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (A n) (B n)) :
    ∀ n : Nat, (A n).Splits := by
  rr_splits using hprec

example {A B : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (A n) (B n)) :
    ∀ n : Nat, (B n).Splits := by
  rr_splits using hprec

example {A B : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (A n) (B n)) :
    ∀ n : Nat, A n ≠ 0 ∧ (A n).Splits := by
  rr_realrooted using hprec

example {A B : Nat → ℝ[X]}
    (hprec : ∀ n : Nat, StrictInterl (A n) (B n)) :
    ∀ n : Nat, B n ≠ 0 ∧ (B n).Splits := by
  rr_finish using hprec

example {P : Nat → ℝ[X]}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_nonzero using hinter

example {P : Nat → ℝ[X]} {n : Nat}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    P n ≠ 0 := by
  rr_nonzero using hinter

example {P : Nat → ℝ[X]}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    ∀ n : Nat, (P n).Splits := by
  rr_splits using hinter

example {P : Nat → ℝ[X]} {n : Nat}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    (P n).Splits := by
  rr_splits using hinter

example {P : Nat → ℝ[X]}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_zero_or_splits using hinter

example {P : Nat → ℝ[X]} {n : Nat}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_realrooted using hinter

example {P : Nat → ℝ[X]}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_finish using hinter

example {P : Nat → ℝ[X]} {n : Nat}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    P n ≠ 0 := by
  rr_finish using hinter

example {P : Nat → ℝ[X]}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    ∀ n : Nat, (P n).Splits := by
  rr_finish using hinter

example {P : Nat → ℝ[X]} {n : Nat}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    (P n).Splits := by
  rr_finish using hinter

example {P : Nat → ℝ[X]}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_finish using hinter

example {P : Nat → ℝ[X]} {n : Nat}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_finish using hinter

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
    ∀ n : Nat, B n ≠ 0 ∧ (B n).Splits := by
  rr_finish using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) := by
  rr_realrooted using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    (A n ≠ 0 ∧ (A n).Splits) ∧ (B n ≠ 0 ∧ (B n).Splits) := by
  rr_finish using hP

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

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n * B n ≠ 0 ∧ (A n * B n).Splits := by
  rr_realrooted using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    B n * A n ≠ 0 ∧ (B n * A n).Splits := by
  rr_finish using hP

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, (A n * B n).Splits := by
  rr_splits using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    (B n * A n).Splits := by
  rr_finish using hP

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    ∀ n : Nat, A n * B n = 0 ∨ (A n * B n).Splits := by
  rr_zero_or_splits using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n ≠ 0 ∧ (A n).Splits) ∧
      (B n ≠ 0 ∧ (B n).Splits)) :
    B n * A n = 0 ∨ (B n * A n).Splits := by
  rr_finish using hP

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    ∀ n : Nat, A n = 0 ∨ (A n).Splits := by
  rr_zero_or_splits using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    B n = 0 ∨ (B n).Splits := by
  rr_finish using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    (A n = 0 ∨ (A n).Splits) ∧ (B n = 0 ∨ (B n).Splits) := by
  rr_zero_or_splits using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    (A n = 0 ∨ (A n).Splits) ∧ (B n = 0 ∨ (B n).Splits) := by
  rr_finish using hP

example {A B : Nat → ℝ[X]}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    ∀ n : Nat, A n * B n = 0 ∨ (A n * B n).Splits := by
  rr_zero_or_splits using hP

example {A B : Nat → ℝ[X]} {n : Nat}
    (hP : ∀ n : Nat, (A n = 0 ∨ (A n).Splits) ∧
      (B n = 0 ∨ (B n).Splits)) :
    B n * A n = 0 ∨ (B n * A n).Splits := by
  rr_finish using hP

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

example {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_interlaces using hfg, hdeg

example {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_interlaces using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Interlaces f g := by
  rr_interlaces using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_finish using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_finish

example {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_finish using hfg, hdeg

example {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Interlaces f g := by
  rr_interlaces using hfg, hdeg

example {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Interlaces f g := by
  rr_finish

example {p : ℝ[X]} {d : Nat}
    (htop : p.coeff d ≠ 0)
    (habove : ∀ m, d < m → p.coeff m = 0) :
    p.natDegree = d := by
  rr_natDegree_from_top_above using
    top_ne := htop,
    above := habove

example {p : ℝ[X]} {d : Nat}
    (htop : 0 < p.coeff d)
    (habove : ∀ m, d < m → p.coeff m = 0) :
    p.natDegree = d := by
  rr_natDegree_from_top_above using
    top_pos := htop,
    above := habove

example {p : ℝ[X]} {d : Nat}
    (htop : p.coeff d = 1)
    (habove : ∀ m, d < m → p.coeff m = 0) :
    p.natDegree = d := by
  rr_natDegree_from_top_above using
    top_eq := htop,
    above := habove

example {f g : ℝ[X]} (hfg : StrictInterl f g) : Interl f g := by rr_prec0 using hfg

example {f g : ℝ[X]} (hfg : StrictInterl f g) : Interl f g := by rr_finish

example {f g : ℝ[X]} (hfg : StrictInterl f g) : Interl f g := by rr_finish using hfg

example {f g : ℝ[X]} (hfg : Interlaces f g) : StrictInterl f g := by rr_prec using hfg

example {P : Nat → ℝ[X]}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_prec using hinter

example {P : Nat → ℝ[X]} {n : Nat}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    StrictInterl (P n) (P (n + 1)) := by
  rr_prec using hinter

example {P : Nat → ℝ[X]}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_finish using hinter

example {P : Nat → ℝ[X]} {n : Nat}
    (hinter : ∀ n : Nat, Interlaces (P n) (P (n + 1))) :
    StrictInterl (P n) (P (n + 1)) := by
  rr_finish using hinter

example {f g : ℝ[X]} (hfg : Interlaces f g) : StrictInterl f g := by rr_finish using hfg

example {f g : ℝ[X]} (hfg : Interlaces f g) : StrictInterl f g := by rr_finish

example {f g : ℝ[X]} (hfg : Interlaces f g) : Interl f g := by rr_prec0 using hfg

example {f g : ℝ[X]} (hfg : Interlaces f g) : Interl f g := by rr_finish using hfg

example {f g : ℝ[X]} (hfg : Interl f g) (hf : f ≠ 0) (hg : g ≠ 0) :
    StrictInterl f g := by
  rr_prec using hfg, hf, hg

example {f g : ℝ[X]} (hfg : Interl f g) (hf : f ≠ 0) (hg : g ≠ 0) :
    StrictInterl f g := by
  rr_finish using hfg, hf, hg


end Tactic
end RealRooted
