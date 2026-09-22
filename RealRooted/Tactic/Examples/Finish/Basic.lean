import RealRooted.InterlacingSequenceBasic
import RealRooted.Tactic.Finish

/-!
# Finish tactic examples

Abstract smoke tests for tactics that consume `StrictInterl` certificates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Synthetic family used to test generated-style named-wrapper lookup. -/
noncomputable def namedFinishSmoke (_ : Nat) : ℝ[X] :=
  1

/-- Synthetic refinement used to test generated-style interlacing lookup. -/
noncomputable def namedFinishSmokeRefined (_ : Nat) : List ℝ[X] :=
  []

theorem namedFinishSmoke_generated_realRooted (n : Nat) :
    namedFinishSmoke n ≠ 0 ∧ (namedFinishSmoke n).Splits := by
  simp [namedFinishSmoke]

theorem namedFinishSmoke_generated_ne_zero (n : Nat) :
    namedFinishSmoke n ≠ 0 :=
  (namedFinishSmoke_generated_realRooted n).1

theorem namedFinishSmoke_generated_splits (n : Nat) :
    (namedFinishSmoke n).Splits :=
  (namedFinishSmoke_generated_realRooted n).2

theorem namedFinishSmoke_generated_interlaces (n : Nat) :
    IsInterlacingSeq0Nonneg (namedFinishSmokeRefined n) := by
  simp [namedFinishSmokeRefined, IsInterlacingSeq0Nonneg, IsInterlacingSeq0]

-- Generated-style final wrappers are found by generic named-wrapper lookup.
example (n : Nat) : namedFinishSmoke n ≠ 0 := by rr_nonzero

-- Generated-style final wrappers are found by generic named-wrapper lookup.
example (n : Nat) : (namedFinishSmoke n).Splits := by rr_splits

-- Generated-style final wrappers are found by generic named-wrapper lookup.
example (n : Nat) : namedFinishSmoke n ≠ 0 ∧ (namedFinishSmoke n).Splits := by rr_realrooted

-- Generated-style refinement wrappers are found by generic named-wrapper lookup.
example (n : Nat) : IsInterlacingSeq0Nonneg (namedFinishSmokeRefined n) := by rr_interlaces

-- Generated-style final wrappers are found by generic named-wrapper lookup.
example (n : Nat) : namedFinishSmoke n ≠ 0 ∧ (namedFinishSmoke n).Splits := by rr_finish

noncomputable def recurrenceEvalSmoke : Nat → ℝ[X]
  | 0 => 1
  | n + 1 => (1 + X) * recurrenceEvalSmoke n

example : recurrenceEvalSmoke 0 = 1 := by recurrence_eval

example : recurrenceEvalSmoke 1 = 1 + X := by recurrence_eval

example : recurrenceEvalSmoke 2 = 1 + 2 * X + X ^ 2 := by recurrence_eval

example : (recurrenceEvalSmoke 2).derivative = 2 + 2 * X := by recurrence_eval

example {f : ℝ[X]} (hf : f ≠ 0) : f ≠ 0 := by rr_nonzero using hf

example : (X : ℝ[X]) ≠ 0 := by rr_nonzero

example {a : ℝ} (ha : a ≠ 0) : (C a : ℝ[X]) ≠ 0 := by rr_nonzero

example {m k : Nat} (hk : k ≤ m) :
    (C (((Nat.choose m k : Nat) : ℝ)) : ℝ[X]) ≠ 0 := by
  rr_nonzero

example {a : ℝ} : (X + C a : ℝ[X]) ≠ 0 := by rr_nonzero

example {a : ℝ} : (C a + X : ℝ[X]) ≠ 0 := by rr_nonzero

example {a : ℝ} : (X - C a : ℝ[X]) ≠ 0 := by rr_nonzero

example {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0) : p * q ≠ 0 := by rr_nonzero

example {p : ℝ[X]} {n : Nat} (hp : p ≠ 0) : p ^ n ≠ 0 := by rr_nonzero

example {p : ℝ[X]} (hp : p ≠ 0) : p.reverse ≠ 0 := by rr_nonzero

example {p : ℝ[X]} {n : Nat} (hp : p ≠ 0) : X ^ n * p.reverse ≠ 0 := by rr_nonzero

example {p q : ℝ[X]} (hpq : p * q ≠ 0) : p ≠ 0 := by rr_nonzero

example {p q : ℝ[X]} (hpq : p * q ≠ 0) : q ≠ 0 := by rr_nonzero

example {p : ℝ[X]} (hdeg : p.natDegree ≠ 0) : p.derivative ≠ 0 := by rr_nonzero

example {p : ℝ[X]} (hdeg : 2 ≤ p.natDegree) : p.derivative ≠ 0 := by rr_nonzero

example {p : ℝ[X]} (hp : X ^ 2 * p.derivative ≠ 0) : p.derivative ≠ 0 := by rr_nonzero

example {p : ℝ[X]} (hp : HasPosLeadingCoeff p) : p ≠ 0 := by rr_nonzero

example {p q : ℝ[X]} (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q) :
    p * q ≠ 0 := by
  rr_nonzero

example {f : ℝ[X]} (hdeg : f.natDegree = 1) : f ≠ 0 := by rr_nonzero

example {f : ℝ[X]} (hdeg : f.natDegree = 1) : f ≠ 0 := by rr_finish

example {f : ℝ[X]} (hf : f.Splits) : f.Splits := by rr_splits using hf

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
    StrictInterl p.derivative p := by
  rr_finish using hp

example {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    StrictInterl p.derivative p := by
  rr_finish

example {p : ℝ[X]} (hp : p.Splits) (hdeg : 2 ≤ p.natDegree) :
    p.derivative ≠ 0 ∧ p.derivative.Splits := by
  rr_realrooted

example {a : ℝ} : (C a : ℝ[X]).Splits := by rr_splits

example : (X : ℝ[X]).Splits := by rr_splits

example {a : ℝ} : (X + C a : ℝ[X]).Splits := by rr_splits

example {a : ℝ} : (C a + X : ℝ[X]).Splits := by rr_splits

example {a : ℝ} : (X - C a : ℝ[X]).Splits := by rr_splits

example {n : Nat} : ((X : ℝ[X]) ^ n).Splits := by rr_splits

example {a : ℝ} {n : Nat} : (C a * X ^ n : ℝ[X]).Splits := by rr_splits

example {f : ℝ[X]} {n : Nat} (hf : f.Splits) : (f ^ n).Splits := by rr_splits using hf

example {f : ℝ[X]} {n : Nat} (hf : f.Splits) : (f ^ n).Splits := by rr_splits

example {f : ℝ[X]} {n : Nat} (hf : f.Splits) : (f ^ n).Splits := by
  rr_splits_pow using
    splits := hf,
    exponent := n

example {f : ℝ[X]} (hf : f.Splits) : f.reverse.Splits := by
  rr_splits_reverse using
    splits := hf

example {f : ℝ[X]} (hf : f.Splits) : f.reverse.Splits := by rr_splits using hf

example {f : ℝ[X]} (hf : f.reverse.Splits) : f.Splits := by
  rr_splits_of_reverse using
    reverse_splits := hf

example {f : ℝ[X]} (hf : f.reverse.Splits) : f.Splits := by rr_splits using hf

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

example {f : ℝ[X]} {n : Nat} (hf : f.Splits) : (X ^ n * f).Splits := by rr_splits using hf

example {f : ℝ[X]} {n : Nat} (hf : (X ^ n * f).Splits) : f.Splits := by rr_splits using hf

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

example {f : ℝ[X]} (hf : f.Splits) : f = 0 ∨ f.Splits := by rr_zero_or_splits using hf

example {f : ℝ[X]} (hf : f.Splits) : f = 0 ∨ f.Splits := by rr_zero_or_splits

example {f : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) : f = 0 ∨ f.Splits := by rr_zero_or_splits using hf

example {f : ℝ[X]} (hf : f = 0 ∨ f.Splits) :
    f.reverse = 0 ∨ f.reverse.Splits := by
  rr_zero_or_splits_reverse using
    zero_or_splits := hf

example {f : ℝ[X]} (hf : f = 0 ∨ f.Splits) :
    f.reverse = 0 ∨ f.reverse.Splits := by
  rr_zero_or_splits using hf

example {f : ℝ[X]} (hf : f.reverse = 0 ∨ f.reverse.Splits) :
    f = 0 ∨ f.Splits := by
  rr_zero_or_splits_of_reverse using
    reverse_zero_or_splits := hf

example {f : ℝ[X]} (hf : f.reverse = 0 ∨ f.reverse.Splits) :
    f = 0 ∨ f.Splits := by
  rr_zero_or_splits using hf

example {f : ℝ[X]} {N : Nat} (hf : f = 0 ∨ f.Splits) (hN : f.natDegree ≤ N) :
    reflect N f = 0 ∨ (reflect N f).Splits := by
  rr_zero_or_splits_reflect using
    zero_or_splits := hf,
    degree_bound := hN

example {f : ℝ[X]} {N : Nat} (hf : f = 0 ∨ f.Splits) :
    X ^ (N - f.natDegree) * f.reverse = 0 ∨
      (X ^ (N - f.natDegree) * f.reverse).Splits := by
  rr_zero_or_splits_X_pow_mul_reverse using
    zero_or_splits := hf

example {f : ℝ[X]} {N : Nat} (hf : f = 0 ∨ f.Splits) :
    X ^ (N - f.natDegree) * f.reverse = 0 ∨
      (X ^ (N - f.natDegree) * f.reverse).Splits := by
  rr_zero_or_splits using hf

example {f g : ℝ[X]} (hf : f = 0 ∨ f.Splits) (hg : g = 0 ∨ g.Splits) :
    f * g = 0 ∨ (f * g).Splits := by
  rr_zero_or_splits_mul using
    left := hf,
    right := hg

example {f g : ℝ[X]} (hf : f = 0 ∨ f.Splits) (hg : g = 0 ∨ g.Splits) :
    g * f = 0 ∨ (g * f).Splits := by
  rr_zero_or_splits_mul using
    left := hf,
    right := hg

example {f g : ℝ[X]} (hfg : (f = 0 ∨ f.Splits) ∧ (g = 0 ∨ g.Splits)) :
    f = 0 ∨ f.Splits := by
  rr_zero_or_splits using hfg

example {f g : ℝ[X]} (hfg : (f = 0 ∨ f.Splits) ∧ (g = 0 ∨ g.Splits)) :
    g = 0 ∨ g.Splits := by
  rr_zero_or_splits using hfg

example {f g : ℝ[X]} (hfg : (f = 0 ∨ f.Splits) ∧ (g = 0 ∨ g.Splits)) :
    f * g = 0 ∨ (f * g).Splits := by
  rr_zero_or_splits using hfg

example {f g : ℝ[X]} (hfg : (f = 0 ∨ f.Splits) ∧ (g = 0 ∨ g.Splits)) :
    g * f = 0 ∨ (g * f).Splits := by
  rr_finish using hfg

example {f : ℝ[X]} {n : Nat} (hf : f = 0 ∨ f.Splits) :
    f ^ n = 0 ∨ (f ^ n).Splits := by
  rr_zero_or_splits_pow using
    zero_or_splits := hf,
    exponent := n

example {f : ℝ[X]} {n : Nat} (hf : f = 0 ∨ f.Splits) :
    f ^ n = 0 ∨ (f ^ n).Splits := by
  rr_zero_or_splits using hf

example {f : ℝ[X]} {n : Nat} (hf : f = 0 ∨ f.Splits) :
    f ^ n = 0 ∨ (f ^ n).Splits := by
  rr_zero_or_splits

example {f : ℝ[X]} {n : Nat} (hf : f = 0 ∨ f.Splits) :
    f ^ n = 0 ∨ (f ^ n).Splits := by
  rr_finish using hf

example {f : ℝ[X]} {n : Nat} (hf : f.Splits) :
    X ^ n * f = 0 ∨ (X ^ n * f).Splits := by
  rr_zero_or_splits using hf

example {f : ℝ[X]} {n : Nat} (hf : (X ^ n * f).Splits) :
    f = 0 ∨ f.Splits := by
  rr_zero_or_splits using hf

example {f : ℝ[X]} (h0 : f.coeff 0 = 0) (hf : f = 0 ∨ f.Splits) :
    f.divX = 0 ∨ f.divX.Splits := by
  rr_zero_or_splits_divX using
    coeff_zero := h0,
    zero_or_splits := hf

example {f : ℝ[X]} (h0 : f.coeff 0 = 0) (hf : f.divX = 0 ∨ f.divX.Splits) :
    f = 0 ∨ f.Splits := by
  rr_zero_or_splits_of_divX using
    coeff_zero := h0,
    divX_zero_or_splits := hf

example {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits) :
    (f * g).Splits := by
  rr_splits_mul using
    left := hf,
    right := hg

example {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits) :
    (f * g).Splits := by
  rr_splits

example {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits) :
    (g * f).Splits := by
  rr_splits_mul using
    left := hf,
    right := hg

example {f g : ℝ[X]} (hf : f = 0 ∨ f.Splits) (hg : g = 0 ∨ g.Splits) :
    f * g = 0 ∨ (f * g).Splits := by
  rr_zero_or_splits

example {f g : ℝ[X]} (hf : f = 0 ∨ f.Splits) (hg : g = 0 ∨ g.Splits) :
    g * f = 0 ∨ (g * f).Splits := by
  rr_finish

example {f : ℝ[X]} (hdeg : f.natDegree ≤ 1) : f.Splits := by rr_splits

example {f : ℝ[X]} (hdeg : f.natDegree ≤ 1) : f.Splits := by rr_finish

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

example {f g : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) (hg : g ≠ 0 ∧ g.Splits) :
    f * g ≠ 0 ∧ (f * g).Splits := by
  rr_mul_realrooted using hf, hg

example {f g : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) (hg : g ≠ 0 ∧ g.Splits) :
    (g * f).Splits := by
  rr_mul_realrooted using
    left := hf,
    right := hg

example {f : ℝ[X]} {n : Nat} (hf : f ≠ 0 ∧ f.Splits) :
    f ^ n ≠ 0 ∧ (f ^ n).Splits := by
  rr_pow_realrooted using
    realrooted := hf,
    exponent := n

example {f : ℝ[X]} {n : Nat} (hf : f ≠ 0 ∧ f.Splits) :
    f ^ n ≠ 0 ∧ (f ^ n).Splits := by
  rr_realrooted using hf

example {f : ℝ[X]} {n : Nat} (hf : f ≠ 0 ∧ f.Splits) :
    (f ^ n).Splits := by
  rr_splits using hf

example {f : ℝ[X]} {n : Nat} (hf : f ≠ 0 ∧ f.Splits) :
    f ^ n = 0 ∨ (f ^ n).Splits := by
  rr_finish using hf

example {f : ℝ[X]} {n : Nat} (hf : f ≠ 0 ∧ f.Splits) :
    f ^ n ≠ 0 ∧ (f ^ n).Splits := by
  rr_realrooted

example {f g : ℝ[X]} (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    f * g ≠ 0 ∧ (f * g).Splits := by
  rr_realrooted using hfg

example {f g : ℝ[X]} (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    (f * g).Splits := by
  rr_splits using hfg

example {f g : ℝ[X]} (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    g * f = 0 ∨ (g * f).Splits := by
  rr_finish using hfg

example {f g : ℝ[X]} (hfg : (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits)) :
    g * f ≠ 0 ∧ (g * f).Splits := by
  rr_finish using hfg

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


end Tactic
end RealRooted
