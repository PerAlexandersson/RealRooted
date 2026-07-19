import RealRooted.Tactic.Finish

/-!
# Finish tactic examples

Abstract smoke tests for tactics that consume `Prec` certificates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {f : ℝ[X]} (hf : f ≠ 0) : f ≠ 0 := by
  rr_nonzero using hf

example : (X : ℝ[X]) ≠ 0 := by
  rr_nonzero

example {a : ℝ} (ha : a ≠ 0) : (C a : ℝ[X]) ≠ 0 := by
  rr_nonzero

example {m k : Nat} (hk : k ≤ m) :
    (C (((Nat.choose m k : Nat) : ℝ)) : ℝ[X]) ≠ 0 := by
  rr_nonzero

example {a : ℝ} : (X + C a : ℝ[X]) ≠ 0 := by
  rr_nonzero

example {a : ℝ} : (C a + X : ℝ[X]) ≠ 0 := by
  rr_nonzero

example {a : ℝ} : (X - C a : ℝ[X]) ≠ 0 := by
  rr_nonzero

example {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0) : p * q ≠ 0 := by
  rr_nonzero

example {p : ℝ[X]} {n : Nat} (hp : p ≠ 0) : p ^ n ≠ 0 := by
  rr_nonzero

example {p : ℝ[X]} (hp : p ≠ 0) : p.reverse ≠ 0 := by
  rr_nonzero

example {p : ℝ[X]} {n : Nat} (hp : p ≠ 0) : X ^ n * p.reverse ≠ 0 := by
  rr_nonzero

example {p q : ℝ[X]} (hpq : p * q ≠ 0) : p ≠ 0 := by
  rr_nonzero

example {p q : ℝ[X]} (hpq : p * q ≠ 0) : q ≠ 0 := by
  rr_nonzero

example {p : ℝ[X]} (hdeg : p.natDegree ≠ 0) : p.derivative ≠ 0 := by
  rr_nonzero

example {p : ℝ[X]} (hdeg : 2 ≤ p.natDegree) : p.derivative ≠ 0 := by
  rr_nonzero

example {p : ℝ[X]} (hp : X ^ 2 * p.derivative ≠ 0) : p.derivative ≠ 0 := by
  rr_nonzero

example {p : ℝ[X]} (hp : HasPosLeadingCoeff p) : p ≠ 0 := by
  rr_nonzero

example {p q : ℝ[X]} (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q) :
    p * q ≠ 0 := by
  rr_nonzero

example {f : ℝ[X]} (hdeg : f.natDegree = 1) : f ≠ 0 := by
  rr_nonzero

example {f : ℝ[X]} (hdeg : f.natDegree = 1) : f ≠ 0 := by
  rr_finish

example {f : ℝ[X]} (hf : f.Splits) : f.Splits := by
  rr_splits using hf

example {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    p.derivative.Splits := by
  rr_splits

example {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    Interlaces p.derivative p := by
  rr_finish using hp

example {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    Interlaces p.derivative p := by
  rr_finish

example {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    Prec p.derivative p := by
  rr_finish using hp

example {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    Prec p.derivative p := by
  rr_finish

example {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    p.derivative ≠ 0 ∧ p.derivative.Splits := by
  rr_realrooted

example {a : ℝ} : (C a : ℝ[X]).Splits := by
  rr_splits

example : (X : ℝ[X]).Splits := by
  rr_splits

example {a : ℝ} : (X + C a : ℝ[X]).Splits := by
  rr_splits

example {a : ℝ} : (C a + X : ℝ[X]).Splits := by
  rr_splits

example {a : ℝ} : (X - C a : ℝ[X]).Splits := by
  rr_splits

example {n : Nat} : ((X : ℝ[X]) ^ n).Splits := by
  rr_splits

example {a : ℝ} {n : Nat} : (C a * X ^ n : ℝ[X]).Splits := by
  rr_splits

example {f : ℝ[X]} {n : Nat} (hf : f.Splits) : (f ^ n).Splits := by
  rr_splits using hf

example {f : ℝ[X]} {n : Nat} (hf : f.Splits) : (f ^ n).Splits := by
  rr_splits_pow using
    splits := hf,
    exponent := n

example {f : ℝ[X]} (hf : f.Splits) : f.reverse.Splits := by
  rr_splits_reverse using
    splits := hf

example {f : ℝ[X]} (hf : f.Splits) : f.reverse.Splits := by
  rr_splits using hf

example {f : ℝ[X]} (hf : f.reverse.Splits) : f.Splits := by
  rr_splits_of_reverse using
    reverse_splits := hf

example {f : ℝ[X]} (hf : f.reverse.Splits) : f.Splits := by
  rr_splits using hf

example {f : ℝ[X]} {N : Nat} (hf : f.Splits) (hN : f.natDegree ≤ N) :
    (reflect N f).Splits := by
  rr_splits_reflect using
    splits := hf,
    degree_bound := hN

example {f : ℝ[X]} {N : Nat} (hf : f.Splits) :
    (X ^ (N - f.natDegree) * f.reverse).Splits := by
  rr_splits_X_pow_mul_reverse using
    splits := hf

example {f : ℝ[X]} {N : Nat} (hf : f.Splits) :
    (X ^ (N - f.natDegree) * f.reverse).Splits := by
  rr_splits using hf

example {f : ℝ[X]} {n : Nat} (hf : f.Splits) : (X ^ n * f).Splits := by
  rr_splits using hf

example {f : ℝ[X]} {n : Nat} (hf : (X ^ n * f).Splits) : f.Splits := by
  rr_splits using hf

example {f : ℝ[X]} (h0 : f.coeff 0 = 0) (hf : f.Splits) :
    f.divX.Splits := by
  rr_splits_divX using
    coeff_zero := h0,
    splits := hf

example {f : ℝ[X]} (h0 : f.coeff 0 = 0) (hf : f.divX.Splits) :
    f.Splits := by
  rr_splits_of_divX using
    coeff_zero := h0,
    divX_splits := hf

example {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits) :
    (f * g).Splits := by
  rr_splits_mul using
    left := hf,
    right := hg

example {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits) :
    (g * f).Splits := by
  rr_splits_mul using
    left := hf,
    right := hg

example {f : ℝ[X]} (hdeg : f.natDegree ≤ 1) : f.Splits := by
  rr_splits

example {f : ℝ[X]} (hdeg : f.natDegree ≤ 1) : f.Splits := by
  rr_finish

example {f : ℝ[X]} (hf : f ≠ 0) (hdeg : f.natDegree ≤ 1) :
    f ≠ 0 ∧ f.Splits := by
  rr_realrooted

example {f : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) :
    f.reverse ≠ 0 ∧ f.reverse.Splits := by
  rr_realrooted_reverse using
    realrooted := hf

example {f : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) :
    f.reverse ≠ 0 ∧ f.reverse.Splits := by
  rr_realrooted using hf

example {f : ℝ[X]} (hf : f.reverse ≠ 0 ∧ f.reverse.Splits) :
    f ≠ 0 ∧ f.Splits := by
  rr_realrooted_of_reverse using
    reverse_realrooted := hf

example {f : ℝ[X]} (hf : f.reverse ≠ 0 ∧ f.reverse.Splits) :
    f ≠ 0 ∧ f.Splits := by
  rr_realrooted using hf

example {f : ℝ[X]} {N : Nat} (hf : f ≠ 0 ∧ f.Splits) (hN : f.natDegree ≤ N) :
    (reflect N f) ≠ 0 ∧ (reflect N f).Splits := by
  rr_realrooted_reflect using
    realrooted := hf,
    degree_bound := hN

example {f : ℝ[X]} {N : Nat} (hf : f ≠ 0 ∧ f.Splits) :
    (X ^ (N - f.natDegree) * f.reverse) ≠ 0 ∧
      (X ^ (N - f.natDegree) * f.reverse).Splits := by
  rr_realrooted_X_pow_mul_reverse using
    realrooted := hf

example {f : ℝ[X]} {N : Nat} (hf : f ≠ 0 ∧ f.Splits) :
    (X ^ (N - f.natDegree) * f.reverse) ≠ 0 ∧
      (X ^ (N - f.natDegree) * f.reverse).Splits := by
  rr_realrooted using hf

example {f : ℝ[X]} (h0 : f.coeff 0 = 0) (hf : f ≠ 0 ∧ f.Splits) :
    f.divX ≠ 0 ∧ f.divX.Splits := by
  rr_realrooted_divX using
    coeff_zero := h0,
    realrooted := hf

example {f : ℝ[X]} (h0 : f.coeff 0 = 0) (hf : f.divX ≠ 0 ∧ f.divX.Splits) :
    f ≠ 0 ∧ f.Splits := by
  rr_realrooted_of_divX using
    coeff_zero := h0,
    divX_realrooted := hf

example {f : ℝ[X]} (hf : f ≠ 0) (hdeg : f.natDegree = 1) :
    f ≠ 0 ∧ f.Splits := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 := by
  rr_nonzero using hfg

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 := by
  rr_nonzero

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g) : f ≠ 0 := by
  rr_finish using hfg

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

example {f g : ℝ[X]} (hfg : Prec f g) : g ≠ 0 ∧ g.Splits := by
  rr_finish using hfg

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

example {g f : ℝ[X]} (hgf : Interlaces g f) : f ≠ 0 ∧ f.Splits := by
  rr_finish using hgf

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
  rr_interlaces using hfg

example {f g : ℝ[X]} (hfg : Prec f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Interlaces f g := by
  rr_interlaces using hfg

example {f g : ℝ[X]} (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_finish using hfg

example {f g : ℝ[X]} (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Interlaces f g := by
  rr_finish using hfg, hdeg

example {f g : ℝ[X]} (hfg : Prec f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Interlaces f g := by
  rr_interlaces using hfg, hdeg

example {f g : ℝ[X]} (hfg : Prec f g)
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

example {f g : ℝ[X]} (hfg : Prec f g) : Prec0 f g := by
  rr_prec0 using hfg

example {f g : ℝ[X]} (hfg : Prec f g) : Prec0 f g := by
  rr_finish

example {f g : ℝ[X]} (hfg : Prec f g) : Prec0 f g := by
  rr_finish using hfg

example {f g : ℝ[X]} (hfg : Interlaces f g) : Prec f g := by
  rr_prec using hfg

example {f g : ℝ[X]} (hfg : Interlaces f g) : Prec f g := by
  rr_finish using hfg

example {f g : ℝ[X]} (hfg : Interlaces f g) : Prec f g := by
  rr_finish

example {f g : ℝ[X]} (hfg : Interlaces f g) : Prec0 f g := by
  rr_prec0 using hfg

example {f g : ℝ[X]} (hfg : Interlaces f g) : Prec0 f g := by
  rr_finish using hfg

example {f g : ℝ[X]} (hfg : Prec0 f g) (hf : f ≠ 0) (hg : g ≠ 0) :
    Prec f g := by
  rr_prec using hfg, hf, hg

example {f g : ℝ[X]} (hfg : Prec0 f g) (hf : f ≠ 0) (hg : g ≠ 0) :
    Prec f g := by
  rr_finish using hfg, hf, hg

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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_finish using hbase, hstep

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
  rr_finish using hbase, hstep

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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_finish using hbase, hdegree, hsame, hsucc

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
  rr_finish using hbase, hdegree, hsame, hsucc

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : Prec q p) (htail : IsGeneralizedSturmSeq (q :: rest)) :
    IsGeneralizedSturmSeq (p :: q :: rest) := by
  rr_gsturm_cons using hpq, htail

example {p q : ℝ[X]} {rest : List ℝ[X]}
    (hpq : Prec q p) (htail : IsGeneralizedSturmSeq (q :: rest)) :
    IsGeneralizedSturmSeq (p :: q :: rest) := by
  rr_finish using hpq, htail

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
  rr_finish using hpq, htail

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
