import RealRooted.Tactic.Linear

/-!
# Linear-polynomial tactic examples

Small regression examples for degree-one real-rootedness and interlacing.
-/

open Polynomial

namespace RealRooted
namespace Tactic

@[rr_degree] theorem rr_linear_X_add_two_degree_smoke :
    (X + C (2 : ℝ) : ℝ[X]).natDegree = 1 := by
  compute_degree!

example (r : ℝ) :
    (X - C r : ℝ[X]) ≠ 0 ∧ (X - C r : ℝ[X]).Splits := by
  rr_X_sub_C_realrooted using
    root := r

example {p : ℝ[X]} (hdeg : p.natDegree = 1) :
    p ≠ 0 ∧ p.Splits := by
  rr_degree_one_realrooted using
    degree := hdeg

example :
    (X + C (2 : ℝ) : ℝ[X]) ≠ 0 ∧ (X + C (2 : ℝ) : ℝ[X]).Splits := by
  rr_degree_one_realrooted

example {p : ℝ[X]} (hne : p ≠ 0) (hdeg : p.natDegree ≤ 1) :
    p ≠ 0 ∧ p.Splits := by
  rr_natDegree_le_one_realrooted using
    nonzero := hne,
    degree := hdeg

example {p : ℝ[X]} (hdeg : p.natDegree = 1) :
    Interlaces (1 : ℝ[X]) p := by
  rr_interlaces_one_linear using
    degree := hdeg

example :
    Interlaces (1 : ℝ[X]) (X + C (2 : ℝ) : ℝ[X]) := by
  rr_interlaces_one_linear

example {p : ℝ[X]} {c : ℝ} (hc : c ≠ 0) (hdeg : p.natDegree = 1) :
    Interlaces (C c) p := by
  rr_interlaces_C_linear using
    scalar_ne := hc,
    degree := hdeg

example :
    Interlaces (C (3 : ℝ)) (X + C (2 : ℝ) : ℝ[X]) := by
  rr_interlaces_C_linear using
    scalar_ne := rr_side_ne_term

example {f g : ℝ[X]} {a : ℝ} (hfg : Prec f g) (ha : a ≠ 0) :
    Prec (C a * f) g := by
  rr_prec_C_mul_left using
    prec := hfg,
    scalar_ne := ha

example {f g : ℝ[X]} {a : ℝ} (hfg : Prec f g) (ha : a ≠ 0) :
    Prec f (C a * g) := by
  rr_prec_C_mul_right using
    prec := hfg,
    scalar_ne := ha

example {f g : ℝ[X]} {a b : ℝ} (hfg : Prec f g) (ha : a ≠ 0) (hb : b ≠ 0) :
    Prec (C a * f) (C b * g) := by
  rr_prec_C_mul_both using
    prec := hfg,
    left_ne := ha,
    right_ne := hb

example {f g : ℝ[X]} {n : Nat} (hfg : Prec f g) :
    Prec (C ((n : ℝ) + 1) * f) g := by
  rr_prec_C_mul_left using
    prec := hfg

example {f g : ℝ[X]} {n : Nat} (hfg : Prec f g) :
    Prec (C ((n : ℝ) + 1) * f) (C ((n : ℝ) + 2) * g) := by
  rr_prec_C_mul_both using
    prec := hfg

example {F G : Nat → ℝ[X]} {a : Nat → ℝ}
    (hFG : ∀ n : Nat, Prec (F n) (G n))
    (ha : ∀ n : Nat, a n ≠ 0) :
    ∀ n : Nat, Prec (C (a n) * F n) (G n) := by
  rr_prec_C_mul_left_sequence using
    prec := hFG,
    scalar_ne := ha

example {F G : Nat → ℝ[X]} :
    (∀ n : Nat, Prec (F n) (G n)) →
      ∀ n : Nat, Prec (C ((n : ℝ) + 1) * F n) (G n) := by
  intro hFG
  rr_prec_C_mul_left_sequence using
    prec := hFG

example {F G : Nat → ℝ[X]} {a : Nat → ℝ}
    (hFG : ∀ n : Nat, Prec (F n) (G n))
    (ha : ∀ n : Nat, a n ≠ 0) :
    ∀ n : Nat, Prec (F n) (C (a n) * G n) := by
  rr_prec_C_mul_right_sequence using
    prec := hFG,
    scalar_ne := ha

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hFG : ∀ n : Nat, Prec (F n) (G n))
    (ha : ∀ n : Nat, a n ≠ 0)
    (hb : ∀ n : Nat, b n ≠ 0) :
    ∀ n : Nat, Prec (C (a n) * F n) (C (b n) * G n) := by
  rr_prec_C_mul_both_sequence using
    prec := hFG,
    left_ne := ha,
    right_ne := hb

example {F G : Nat → ℝ[X]}
    (hFG : ∀ n : Nat, Prec (F n) (G n)) :
    ∀ n : Nat, Prec (C ((n : ℝ) + 1) * F n) (C ((n : ℝ) + 2) * G n) := by
  rr_prec_C_mul_both_sequence using
    prec := hFG

example {f g : ℝ[X]} {a b : ℝ} (hfg : Prec f g) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdeg : (C a * f).natDegree + 1 = (C b * g).natDegree) :
    Interlaces (C a * f) (C b * g) := by
  have hscaled : Prec (C a * f) (C b * g) := by
    rr_prec_C_mul_both using
      prec := hfg,
      left_ne := ha,
      right_ne := hb
  rr_interlaces using hscaled

example {p : ℝ[X]} {a : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) (ha : a ≠ 0) :
    C a * p ≠ 0 ∧ (C a * p).Splits := by
  rr_C_mul_realrooted using
    realrooted := hp,
    scalar_ne := ha

example {p : ℝ[X]} {a : ℝ}
    (hp : p ≠ 0 ∧ p.Splits) (ha : a ≠ 0) :
    (C a * p).Splits := by
  rr_C_mul_realrooted using
    realrooted := hp,
    scalar_ne := ha

example {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    X * p ≠ 0 ∧ (X * p).Splits := by
  rr_X_mul_realrooted using
    realrooted := hp

example {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    X * p ≠ 0 := by
  rr_X_mul_realrooted using
    realrooted := hp

example {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0) :
    ∀ n : Nat, C (a n) * P n ≠ 0 ∧ (C (a n) * P n).Splits := by
  rr_C_mul_realrooted_sequence using
    realrooted := hP,
    scalar_ne := ha

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, C ((n : ℝ) + 1) * P n ≠ 0 ∧
      (C ((n : ℝ) + 1) * P n).Splits := by
  rr_C_mul_realrooted_sequence using
    realrooted := hP

example {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (ha : ∀ n : Nat, a n ≠ 0) :
    ∀ n : Nat, (C (a n) * P n).Splits := by
  rr_C_mul_realrooted_sequence using
    realrooted := hP,
    scalar_ne := ha

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, X * P n ≠ 0 ∧ (X * P n).Splits := by
  rr_X_mul_realrooted_sequence using
    realrooted := hP

example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits) :
    ∀ n : Nat, X * P n ≠ 0 := by
  rr_X_mul_realrooted_sequence using
    realrooted := hP

end Tactic
end RealRooted
